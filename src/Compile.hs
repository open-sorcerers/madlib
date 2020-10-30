{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE NamedFieldPuns #-}
module Compile where

import qualified Data.Map                      as M
import           Data.Maybe                     ( fromMaybe )
import           Data.List                      ( intercalate )
import           Data.Char (toLower)

import           AST.Solved
import           Explain.Location


class Compilable a where
  -- If the Bool is True it indicates that the expression terminates.
  compile :: a -> String

instance Compilable SExp where
  compile (Solved _ (Located _ exp)) = case exp of
    LInt v  -> v
    LStr v  -> "\"" <> v <> "\""
    LBool v -> toLower <$> v

    App abs arg -> case abs of
      -- Solved _ (Located _ ((App (Solved _ (Located _ (App (Solved _ (Located _ (Var "ifElse"))) condArg))) ifArg)))
      --   -> "("
      --   <> compile condArg
      --   <> " ? "
      --   <> compile ifArg
      --   <> " : "
      --   <> compile arg
      --   <> ")"
      Solved _ (Located _ (Var "+"))   -> "(" <> compile arg <> ") + "
      Solved _ (Located _ (Var "-"))   -> "(" <> compile arg <> ") - "
      Solved _ (Located _ (Var "*"))   -> "(" <> compile arg <> ") * "
      Solved _ (Located _ (Var "/"))   -> "(" <> compile arg <> ") / "
      Solved _ (Located _ (Var "===")) -> "(" <> compile arg <> ") === "
      Solved _ (Located _ (App (Solved _ (Located _ (Var "|>"))) arg')) -> 
        compile arg <> "(" <> compile arg' <> ")"
      
      _ -> compile abs <> "(" <> compile arg <> ")"

    FieldAccess record field ->
      compile record <> compile field

    Abs param body -> "(" <> param <> " => " <> compile body <> ")"

    Var name -> name

    -- NB: Export will happen with Export Exp
    Assignment name exp -> "const " <> name <> " = " <> compile exp <> ""
    -- let export = if eexported then "export " else ""
    -- in  export <> "const " <> name <> " = " <> compile exp <> ""

    TypedExp exp _ -> case exp of
      Solved _ (Located _ (Var _)) -> ""
      _     -> compile exp

    Record fields ->
      -- Maybe just map and intercalate ?
      let fs = init $ M.foldrWithKey compileField "" fields
      in  "{" <> fs <> " }"
      where
        compileField name exp res =
          " " <> name <> ": " <> compile exp <> "," <> res

    JSExp content -> content

    ListConstructor elems -> "[" <> intercalate ", " (compile <$> elems) <> "]"

    Switch exp (first:cs) ->
      "((__x__) => {\n  "
        <> compileCase first
        <> concat (("  else " ++) . compileCase <$> cs)
        -- TODO: Add an else for undefined patterns error and make it throw.
        <> "})("
        <> compile exp
        <> ")"
      where
        compilePattern :: String -> Pattern -> String
        compilePattern _     (PVar _) = "true"
        compilePattern _     PAny     = "true"
        compilePattern scope (PNum n) = scope <> " === " <> n
        compilePattern scope (PStr n) = scope <> " === \"" <> n <> "\""
        compilePattern scope (PBool n) | n == "True" = scope <> " === true"
                                      | otherwise   = scope <> " === false"
        compilePattern scope (PCon n)
          | n == "String" = "typeof " <> scope <> " === \"string\""
          | n == "Bool"   = "typeof " <> scope <> " === \"boolean\""
          | n == "Num"    = "typeof " <> scope <> " === \"number\""
          | otherwise     = ""
        compilePattern scope (PCtor n []) =
          scope <> ".__constructor === " <> "\"" <> n <> "\""
        compilePattern scope (PCtor n ps) =
          scope
            <> ".__constructor === "
            <> "\""
            <> n
            <> "\""
            <> if not (null args) then " && " <> args else ""
          where
          args =
            intercalate " && "
              $   filter (not . null)
              $   compileCtorArg scope n
              <$> zip [0 ..] ps
        compilePattern scope (PRecord m) =
          intercalate " && " $ filter (not . null) $ M.elems $ M.mapWithKey
            (compileRecord scope)
            m
        compilePattern scope (PUserDef n) = scope <> " === \"" <> n <> "\""
        compilePattern _     _            = ""

        compileCase :: Case -> String
        compileCase Case { casepattern, caseexp } =
          "if ("
            <> compilePattern "__x__" casepattern
            <> ") {\n"
            <> buildVars "__x__" casepattern
            <> "    return "
            <> compile caseexp
            <> ";\n  }\n"

        buildVars :: String -> Pattern -> String
        buildVars v p = case p of
          PRecord fields ->
            concat $ M.mapWithKey (\k p' -> buildVars (v <> "." <> k) p') fields
          PCtor _ ps ->
            concat
              $ (\(i, p) -> buildVars (v <> ".__args[" <> show i <> "].value") p)
              <$> zip [0 ..] ps
          PVar n -> "    const " <> n <> " = " <> v <> ";\n"
          _      -> ""

        compileRecord :: String -> Name -> Pattern -> String
        compileRecord scope n p = compilePattern (scope <> "." <> n) p

        compileCtorArg :: String -> String -> (Int, Pattern) -> String
        compileCtorArg scope _ (x, p) =
          compilePattern (scope <> ".__args[" <> show x <> "].value") p

    _ -> "// Not implemented\n"


instance Compilable ADT where
  compile ADT { adtconstructors = [] }                = ""
  compile ADT { adtconstructors } = foldr1
    (<>)
    (compile <$> adtconstructors)


instance Compilable ADTConstructor where
  compile ADTConstructor { adtcname, adtcargs } = case adtcargs of
    Nothing ->
      "const " <> adtcname <> " = { __constructor: \"" <> adtcname <> "\" };\n"
    Just args ->
      "const "
        <> adtcname
        <> " = "
        <> compileArgs args
        <> compileBody adtcname args
        <> ";\n"
   where
    compileArgs n =
      let argNames = (: []) <$> take (length n) ['a' ..]
      in  foldr1 (<>) $ (<> " => ") <$> argNames

    compileBody n a =
      let argNames = (: []) <$> take (length a) ['a' ..]
          -- TODO: Hook a function to each arg in order to define the type of them:
          -- ex:
          --   const Success = a => b => ({ __constructor: "Success", __args: [ { type: inputToType(a), value: a, { type: inputToType(b), value: b } ] });
          args     = buildPCompArg <$> argNames
          argStr   = intercalate ", " args
      in  "({ __constructor: \"" <> n <> "\", __args: [ " <> argStr <> " ] })"

  compile _ = "// Not implemented\n"

buildPCompArg :: String -> String
buildPCompArg a = "__buildCtorParam(" <> a <> ")"

instance Compilable Import where
  compile (NamedImport names path) =
    "import { " <> compileNames names <> " } from \"./" <> path <> ".mjs\""
    where compileNames names = (init . init . concat) $ (++ ", ") <$> names
  compile (DefaultImport path alias) =
    "import " <> alias <> " from \"./" <> path <> ".mjs\""


-- TODO: Add default export with all exported names compilation
instance Compilable AST where
  compile AST { aexps, aadts, apath, aimports } =

    let path        = fromMaybe "Unknown" apath

        infoComment = "// file: " <> path <> "\n"
        helpers     = buildPCompArgFn

        adts        = case aadts of
          [] -> ""
          x  -> foldr1 (<>) (compile <$> x)
        exps = case aexps of
          [] -> ""
          x  -> foldr1 (<>) (terminate . compile <$> x)
        imports = case aimports of
          [] -> ""
          x  -> foldr1 (<>) (terminate . compile <$> x) <> "\n"
        defaultExport = buildDefaultExport aexps
    in  infoComment <> imports <> helpers <> adts <> exps <> defaultExport
   where
    terminate :: String -> String
    terminate a | null a    = ""
                | otherwise = a <> ";\n"


buildDefaultExport :: [SExp] -> String
buildDefaultExport es =
  let exports = filter isExport es
  in  case exports of
    []   -> ""
    exps -> ""--"export default { " <> intercalate ", " (ename <$> exps) <> " };\n"

  where
    isExport :: SExp -> Bool
    isExport _ = False
    -- isExport a = case a of
    --   Assignment { eexported } -> eexported
    --   _                        -> False


buildPCompArgFn :: String
buildPCompArgFn = unlines
  [ "const __buildCtorParam = n => {"
  , "  if (typeof n === \"string\") {"
  , "    return { type: \"String\", value: n };"
  , "  } else {"
  , "    return { type: \"\", value: n };"
  , "  }"
  , "};\n"
  ]
