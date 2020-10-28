module InferSpec where

import           Grammar
import           Infer
import           AST
import qualified Data.Map as M
import           Test.Hspec                     ( describe
                                                , it
                                                , shouldBe
                                                , Spec
                                                )
import           Test.Hspec.Golden              ( Golden(..) )
import qualified Data.Text.IO                  as T
import           Data.Text                      ( Text
                                                , pack
                                                , replace
                                                , unpack
                                                )
import           Text.Show.Pretty               ( ppShow )
import           Control.Monad.Except           ( runExcept )
import           Control.Monad.State            ( StateT(runStateT) )

snapshotTest :: Show a => String -> a -> Golden Text
snapshotTest name actualOutput = Golden
  { output        = pack $ ppShow actualOutput
  , encodePretty  = ppShow
  , writeToFile   = T.writeFile
  , readFromFile  = T.readFile
  , testName      = unpack $ replace (pack " ") (pack "_") (pack name)
  , directory     = ".snapshots"
  , failFirstTime = False
  }

-- TODO: Refactor in order to use the inferAST function instead that supports imports
tester :: String -> Either InferError AST
tester code = case buildAST "path" code of
  (Right ast) -> runEnv ast >>= (`runInfer` ast)
  _           -> Left $ UnboundVariable ""
 where
  runEnv x =
    fst <$> runExcept (runStateT (buildInitialEnv x) Unique { count = 0 })

tableTester :: ASTTable -> AST -> Either InferError ASTTable
tableTester table ast = fst <$> runExcept (runStateT (inferAST "./" table ast) Unique { count = 0 })

spec :: Spec
spec = do
  describe "infer" $ do
    it "should infer abstractions" $ do
      let code   = "(b, c) => b + c"
          actual = tester code
      snapshotTest "should infer abstractions" actual

    it "should infer assignments" $ do
      let code   = unlines ["fn = (b, c) => b + c", "fn(2, 3)"]
          actual = tester code
      snapshotTest "should infer assignments" actual

    it "should infer minus operator" $ do
      let code   = "(b, c) => b - c"
          actual = tester code
      snapshotTest "should infer minus operator" actual

    it "should infer multiplication operator" $ do
      let code   = "(b, c) => b * c"
          actual = tester code
      snapshotTest "should infer multiplication operator" actual

    it "should infer division operator" $ do
      let code   = "(b, c) => b / c"
          actual = tester code
      snapshotTest "should infer division operator" actual

    it "should infer tripleEq operator" $ do
      let code   = "1 === 3"
          actual = tester code
      snapshotTest "should infer tripleEq operator" actual

    it "should infer wrapped tripleEq operator" $ do
      let code   = "((a, b) => a === b)(1, 3)"
          actual = tester code
      snapshotTest "should infer wrapped tripleEq operator" actual

    it "should infer asList function" $ do
      let code   = "(a) => asList(a)"
          actual = tester code
      snapshotTest "should infer asList function" actual

    it "should infer an empty source" $ do
      let code   = ""
          actual = tester code
      snapshotTest "should infer an empty source" actual

    it "should fail for unbound variables" $ do
      let code   = "x"
          actual = tester code
      snapshotTest "should fail for unbound variables" actual

    ---------------------------------------------------------------------------


    -- ADTs:

    it "should infer adts" $ do
      let code = unlines
            [ "data Result = Success String | Error"
            , "result = Success(\"response\")"
            ]
          actual = tester code
      snapshotTest "should infer adts" actual

    it "should infer adts with type parameters" $ do
      let code = unlines
            [ "data Result a"
            , "  = Success a"
            , "  | Error"
            , "result = Success(True)"
            ]
          actual = tester code
      snapshotTest "should infer adts with type parameters" actual

    it "should infer application of adts" $ do
      let code = unlines
            [ "data Result = Success String | Error"
            , "result1 = Success(\"response\")"
            , "result2 = Error"
            , "((a, b) => a === b)(result1, result2)"
            ]
          actual = tester code
      snapshotTest "should infer application of adts" actual

    it "should infer adt return for abstractions" $ do
      let code = unlines
            [ "data Result a = Success a | Error"
            , "result1 = Success(\"response\")"
            , "result2 = Error"
            , "((a, b) => a === b)(result1, result2)"
            ]
          actual = tester code
      snapshotTest "should infer adt return for abstractions" actual

    it "should return an error when an ADT defines a type already existing" $ do
      let code = unlines
            [ "data Result a = Success a | Error"
            , "data Result a = Success a | Error"
            ]
          actual = tester code
      snapshotTest
        "should return an error when an ADT defines a type already existing"
        actual

    it
        "should return an error when an ADT defines a constructor with an unbound variable"
      $ do
          let code   = unlines ["data Result a = Success b", ""]
              actual = tester code
          snapshotTest
            "should return an error when an ADT defines a constructor with an unbound variable"
            actual

    it "should infer adts with record constructors" $ do
      let
        code = unlines
          [ "data Result = Success { value :: String } | Error { message :: String }"
          , "result1 = Success({ value: \"42\" })"
          , "result2 = Error({ message: \"Err\" })"
          , "((a, b) => a === b)(result1, result2)"
          ]
        actual = tester code
      snapshotTest "should infer adts with record constructors" actual

    it "should infer params for adts" $ do
      let code = unlines
            [ "data Result = Success { value :: String }"
            , "r = Success { value: \"42\" }"
            , "((a) => a)(r)"
            ]
          actual = tester code
      snapshotTest "should infer params for adts" actual

    ---------------------------------------------------------------------------


    -- Records:

    it "should infer a record field access" $ do
      let code   = unlines ["a = { x: 3, y: 5 }", "a.x"]
          actual = tester code
      snapshotTest "should infer a record field access" actual

    it "should infer an App with a record" $ do
      let
        code = unlines
          ["a = { x: 3, y: 5 }", "xPlusY = (r) => r.x + r.y", "xPlusY(a)"]
        actual = tester code
      snapshotTest "should infer an App with a record" actual

    it "should fail to infer record if their fields do not match" $ do
      let
        code = "{ x: 3, y: 5 } === { name: \"John\" }"
        actual = tester code
      snapshotTest "should fail to infer record if their fields do not match" actual

    ---------------------------------------------------------------------------


    -- Lists:

    it "should infer list constructors" $ do
      let
        code = unlines
          ["[]", "[1, 2, 3]", "[\"one\", \"two\", \"three\"]"]
        actual = tester code
      snapshotTest "should infer list constructors" actual

    ---------------------------------------------------------------------------


    -- Abstractions:

    -- TODO: Write and implement the same test with ADTs
    -- TODO: Write tests where implementation and definition don't match to force
    -- implementing it as it's currently not implemented.
    it "should resolve abstractions with a type definition" $ do
      let code = unlines
            ["fn :: Num -> Num -> Bool", "fn = (a, b) => a === b", "fn(3, 4)"]
          actual = tester code
      snapshotTest "should resolve abstractions with a type definition" actual

    it "should fail for abstractions with a wrong type definition" $ do
      let code =
            unlines
              [ "fn :: String -> Num -> Bool"
              , "fn = (a, b) => a === b"
              , "fn(3, 4)"
              ]
          actual = tester code
      snapshotTest "should fail for abstractions with a wrong type definition"
                   actual

    ---------------------------------------------------------------------------


    -- If/Else:

    it "should infer a simple if else expression" $ do
      let
        code =
          unlines ["if(True) {", "  \"OK\"", "}", "else {", "  \"NOT OK\"", "}"]
        actual = tester code
      snapshotTest "should infer a simple if else expression" actual

    ---------------------------------------------------------------------------


    -- Pattern matching:

    it "should resolve switch with a boolean literal" $ do
      let code = unlines
            [ "switch(True) {"
            , "  case True : \"OK\""
            , "  case False: \"NOT OK\""
            , "}"
            ]
          actual = tester code
      snapshotTest "should resolve switch with a boolean literal" actual

    it "should resolve switch with a number input" $ do
      let code = unlines
            [ "switch(42) {"
            , "  case 1 : \"NOPE\""
            , "  case 3 : \"NOPE\""
            , "  case 33: \"NOPE\""
            , "  case 42: \"YEAH\""
            , "}"
            ]
          actual = tester code
      snapshotTest "should resolve switch with a number input" actual

    it "should resolve switch with a string input" $ do
      let code = unlines
            [ "switch(\"42\") {"
            , "  case \"1\" : 1"
            , "  case \"3\" : 3"
            , "  case \"33\": 33"
            , "  case \"42\": 42"
            , "}"
            ]
          actual = tester code
      snapshotTest "should resolve switch with a string input" actual
    
    -- TODO: Currently fails but should be allowed
    -- We need to have a special case for unification of TCon in inferCase
    -- Most likely we need to bypass the line:
    --   * su <- unify tarr tarr'
    -- and replace it with a special unify for patterns, and/or replace all
    -- TCon with TAny before unification ( That potentially sounds easier )
    it "should resolve switch with constant type constructor cases" $ do
      let code = unlines
            [ "switch(\"42\") {"
            , "  case String : 1"
            , "  case Bool   : 3"
            , "  case Num    : 33"
            , "}"
            ]
          actual = tester code
      snapshotTest "should resolve switch with constant type constructor cases" actual

    it "should resolve switch with an ADT that has unary constructors" $ do
      let code = unlines
            [ "data Maybe a = Just a | Nothing"
            , "perhaps = Just(4)"
            , "switch(perhaps) {"
            , "  case Just a: a"
            , "  case Nothing: 0"
            , "}"
            ]
          actual = tester code
      snapshotTest
        "should resolve switch with an ADT that has unary constructors"
        actual

    it "should resolve switch with an ADT and PCon patterns" $ do
      let code = unlines
            [ "data Maybe a = Just a | Nothing"
            , "perhaps = Just(4)"
            , "switch(perhaps) {"
            , "  case Just String: 1"
            , "  case Just Num   : 2"
            , "  case Just Bool  : 3"
            , "  case Nothing    : 0"
            , "}"
            ]
          actual = tester code
      snapshotTest
        "should resolve switch with an ADT and PCon patterns"
        actual

    it "should fail to resolve a pattern when the pattern constructor does not match the ADT" $ do
      let code = unlines
            [ "data Maybe a = Just a | Nothing"
            , "data Failure = Nope"
            , "perhaps = Nope"
            , "switch(perhaps) {"
            , "  case Just a: a"
            , "  case Nothing: 0"
            , "}"
            ]
          actual = tester code
      snapshotTest
        "should fail to resolve a pattern when the pattern constructor does not match the ADT"
        actual

    it "should fail to resolve a pattern when the pattern constructor does not match the constructor arg types" $ do
      let code = unlines
            [ "data User = LoggedIn String Num"
            , "u = LoggedIn(\"John\", 33)"
            , "switch(u) {"
            , "  case LoggedIn Num x: x"
            , "}"
            ]
          actual = tester code
      snapshotTest
        "should fail to resolve a pattern when the pattern constructor does not match the constructor arg types"
        actual
    
    it "should resolve a constructor pattern with different constant types for variables" $ do
      let code = unlines
            [ "data User a = LoggedIn a Num"
            , "u = LoggedIn(\"John\", 33)"
            , "switch(u) {"
            , "  case LoggedIn Num x   : x"
            , "  case LoggedIn String x: x"
            , "}"
            ]
          actual = tester code
      snapshotTest
        "should resolve a constructor pattern with different constant types for variables"
        actual

    -- TODO: Add tests with bigger constructors ( 2, 3, 4, 5 -aries ) and update
    -- implementation to get out of the that weird handling in generateCaseEnv

    ---------------------------------------------------------------------------


    -- Imports:
    it "should resolve names from imported modules" $ do
      let codeA = "export inc = (a) => a + 1"
          astA  = buildAST "ModuleA.mad" codeA
          codeB = unlines
            [ "import { inc } from \"ModuleA\""
            , "inc(3)"
            ]
          astB = buildAST "ModubleB.mad" codeB
          actual = case (astA, astB) of
            (Right a, Right b) ->
              let astTable = M.fromList [("./ModuleA.mad", a), ("./ModuleB.mad", b)]
              in  tableTester astTable b
      snapshotTest "should resolve names from imported modules" actual

    ---------------------------------------------------------------------------


    -- Pipe operator:
    -- TODO: Write tests for it