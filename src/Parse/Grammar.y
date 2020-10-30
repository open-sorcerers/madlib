{
module Parse.Grammar where

import           Text.Printf
import           Control.Monad.Except
import qualified Data.Map             as M
import           Data.Char(isUpper)

import           Parse.Lexer
import           Infer.Type
import qualified AST.Source           as Src
import           Explain.Location
}

%name parseMadlib ast
%tokentype { Token }
%error { parseError }
%monad { Alex }
%lexer { lexerWrap } { Token _ TokenEOF }

%token
  int      { Token _ (TokenInt _) }
  str      { Token _ (TokenStr _) }
  name     { Token _ (TokenName _) }
  js       { Token _ (TokenJSBlock _) }
  'ret'    { Token _ TokenReturn }
  '='      { Token _ TokenEq }
  '+'      { Token _ TokenPlus }
  '-'      { Token _ TokenDash }
  '*'      { Token _ TokenStar }
  '/'      { Token _ TokenSlash }
  '::'     { Token _ TokenDoubleColon }
  ':'      { Token _ TokenColon }
  '->'     { Token _ TokenArrow }
  '=>'     { Token _ TokenFatArrow }
  '.'      { Token _ TokenDot }
  ','      { Token _ TokenComma }
  '('      { Token _ TokenLeftParen }
  ')'      { Token _ TokenRightParen }
  '{'      { Token _ TokenLeftCurly }
  '}'      { Token _ TokenRightCurly }
  '['      { Token _ TokenLeftSquaredBracket }
  ']'      { Token _ TokenRightSquaredBracket }
  'if'     { Token _ TokenIf }
  'else'   { Token _ TokenElse }
  'switch' { Token _ TokenSwitch }
  'case'   { Token _ TokenCase }
  '==='    { Token _ TokenTripleEq }
  false    { Token _ (TokenBool _) }
  true     { Token _ (TokenBool _) }
  'import' { Token _ TokenImport }
  'export' { Token _ TokenExport }
  'from'   { Token _ TokenFrom }
  '|'      { Token _ TokenPipe }
  '|>'     { Token _ TokenPipeOperator }
  'data'   { Token _ TokenData }

%left '==='
%left '+' '-'
%left '*' '/'
%right ','
%nonassoc '=' '=>' '::' ':'
%left '->' '|' '|>' 'ret'
%%

ast :: { Src.AST }
  : adt ast          %shift { $2 { Src.aadts =  [$1] <> Src.aadts $2 } }
  | adt              %shift { Src.AST { Src.aimports = [], Src.aexps = [], Src.aadts = [$1], Src.apath = Nothing } }
  | exp ast          %shift { $2 { Src.aexps = [$1] <> Src.aexps $2 } }
  | exp              %shift { Src.AST { Src.aimports = [], Src.aexps = [$1], Src.aadts = [], Src.apath = Nothing } }
  | importDecls ast  %shift { $2 { Src.aimports = $1, Src.apath = Nothing } }
  | {- empty -}      %shift { Src.AST { Src.aimports = [], Src.aexps = [], Src.aadts = [], Src.apath = Nothing } }
  | 'export' name '=' exp ast %shift { $5 { Src.aexps = (Located (tokenToLoc $1) (Src.Export (Located (tokenToLoc $2) (Src.Assignment (strV $2) $4)))) : Src.aexps $5 } }
  | rRet              { Src.AST { Src.aimports = [], Src.aexps = [], Src.aadts = [], Src.apath = Nothing } }
  | rRet ast          { $2 }
  | ast rRet          { $1 }

importDecls :: { [Src.Import] }
  : importDecl importDecls { $1:$2 }
  | importDecl             { [$1] }
  
importDecl :: { Src.Import }
  : 'import' '{' importNames '}' 'from' str rRet { Src.NamedImport $3 (strV $6) }
  | 'import' name 'from' str rRet                { Src.DefaultImport (strV $2) (strV $4) }

importNames :: { [Src.Name] }
  : importNames ',' name %shift { $1 <> [strV $3] }
  | name                 %shift { [strV $1] }

rRet :: { [TokenClass] }
  : 'ret'       { [] }
  -- | 'ret' rret { [] }

maybeRet :: { [TokenClass] }
  : 'ret'       { [] }
  | {- empty -} { [] }

rEq :: { [TokenClass] }
  : '='       { [] }
  | 'ret' '=' { [] }

rPipe :: { [TokenClass] }
  : '|'       { [] }
  | 'ret' '|' { [] }

rParenL :: { [TokenClass] }
  : '('       { [] }
  | '(' 'ret' { [] }

rComa :: { [TokenClass] }
  : ','       { [] }
  | ',' 'ret' { [] }
  | 'ret' ',' { [] }


adt :: { Src.ADT }
  : 'data' name adtParameters rEq adtConstructors %shift { Src.ADT { Src.adtname = strV $2, Src.adtparams = $3, Src.adtconstructors = $5 } }

adtParameters :: { [Src.Name] }
  : name adtParameters %shift { strV $1 : $2 }
  | name               %shift { [strV $1] }
  | {- empty -}               { [] }

adtConstructors :: { [Src.ADTConstructor] }
  : adtConstructor rPipe adtConstructors      %shift { $1:$3 }
  | adtConstructor rRet                       %shift { [$1] }

adtConstructor :: { Src.ADTConstructor }
  : name adtConstructorArgs %shift { Src.ADTConstructor { Src.adtcname = strV $1, Src.adtcargs = Just $2 } }
  | name                    %shift { Src.ADTConstructor { Src.adtcname = strV $1, Src.adtcargs = Nothing } }

adtConstructorArgs :: { [Src.Typing] }
  : typing                    { [$1] }
  | adtConstructorArgs typing { $1 <> [$2] }

typings :: { Src.Typing }
  : typing '->' typings          { Src.TRArr $1 $3 }
  | compositeTyping '->' typings { Src.TRArr $1 $3 }
  | compositeTyping              { $1 }
  | typing                       { $1 }

typing :: { Src.Typing }
  : name                       { Src.TRSingle $ strV $1 }
  | '(' compositeTyping ')'    { $2 }
  | '(' typing '->' typing ')' { Src.TRArr $2 $4 }
  | '{' recordTypingArgs '}'   { Src.TRRecord $2 }

compositeTyping :: { Src.Typing }
  : name compositeTypingArgs { Src.TRComp (strV $1) $2 }

compositeTypingArgs :: { [Src.Typing] }
  : name                     { [Src.TRSingle $ strV $1] }
  | name compositeTypingArgs { (Src.TRSingle $ strV $1) : $2 }

recordTypingArgs :: { M.Map Src.Name Src.Typing }
  : name '::' typing                      { M.fromList [(strV $1, $3)] }
  | recordTypingArgs ',' name '::' typing { M.insert (strV $3) $5 $1 }

type :: { Src.Typing }
  : name              { Src.TRSingle $ strV $1 }
  | name type         { Src.TRComp (strV $1) [$2] }
  | name '(' type ')' { Src.TRComp (strV $1) [$3] }
  | type '->' type    { Src.TRArr $1 $3 }

exp :: { Src.LExp }
  : literal                          { $1 }
  | record                           { $1 }
  | switch                           { $1 }
  | operation                        { $1 }
  | listConstructor          %shift  { $1 }
  | js                       %shift  { Located (tokenToLoc $1) (Src.JSExp $ strV $1) }
  | name '=' exp             %shift  { Located (tokenToLoc $1) (Src.Assignment (strV $1) $3) }
  | name                     %shift  { Located (tokenToLoc $1) (Src.Var $ strV $1) }
  | name rParenL args ')'    %shift  { buildApp (tokenToLoc $1) (Located (tokenToLoc $1) (Src.Var $ strV $1)) $3 }
  | exp '(' args ')'                 { buildApp (Src.getLoc $1) $1 $3 }
  | '(' exp ')' '(' args ')' %shift  { buildApp (Src.getLoc $2) $2 $5 }
  | '(' params ')' '=>' exp  %shift  { buildAbs (tokenToLoc $1) $2 $5 }
  | '(' exp ')'              %shift  { $2 }
  | exp '::' typings                 { Located (Src.getLoc $1) (Src.TypedExp $1 $3) }
  | exp '.' name                     { Located (Src.getLoc $1) (Src.FieldAccess $1 (Located (tokenToLoc $3) (Src.Var $ "." <> strV $3))) }
  | exp '.' name '(' args ')' %shift { buildApp (Src.getLoc $1) (Located (Src.getLoc $1) (Src.FieldAccess $1 (Located (tokenToLoc $3) (Src.Var $ "." <> strV $3)))) $5 }
  | 'if' '(' exp ')' '{' maybeRet exp maybeRet '}' maybeRet 'else' maybeRet '{' maybeRet exp maybeRet '}'
      { Located (tokenToLoc $1) (Src.If $3 $7 $15) }

  -- | 'if' '(' exp ')' '{' maybeRet exp maybeRet '}' maybeRet 'else' maybeRet '{' maybeRet exp maybeRet '}' {
  --   App { epos = tokenToLoc $1, etype = Nothing, eabs =
  --     App { epos = tokenToLoc $1, etype = Nothing, eabs = 
  --       App { epos = tokenToLoc $1, etype = Nothing, eabs = Var { epos = tokenToLoc $2, etype = Nothing, ename = "ifElse" }, earg = $3, efieldAccess = False }
  --   , earg = $7, efieldAccess = False }, earg = $15, efieldAccess = False
  --   }
  -- }


switch :: { Src.LExp }
  : 'switch' '(' exp ')' '{' maybeRet cases maybeRet '}' { Located (tokenToLoc $1) (Src.Switch $3 $7) }

cases :: { [Src.Case] }
  : 'case' pattern ':' exp             { [Src.Case { Src.casepos = tokenToLoc $1, Src.casetype = Nothing, Src.casepattern = $2, Src.caseexp = $4 }] }
  | cases 'ret' 'case' pattern ':' exp { $1 <> [Src.Case { Src.casepos = tokenToLoc $3, Src.casetype = Nothing, Src.casepattern = $4, Src.caseexp = $6 }] }

pattern :: { Src.Pattern }
  : nonCompositePattern { $1 }
  | compositePattern    { $1 }

nonCompositePattern :: { Src.Pattern }
  : name             { nameToPattern $ strV $1 }
  | int              { Src.PNum $ strV $1 }
  | str              { Src.PStr $ strV $1 }
  | true             { Src.PBool $ strV $1 }
  | false            { Src.PBool $ strV $1 }
  | recordPattern    { $1 }
  | '(' pattern ')'  { $2 }

-- Constructor pattern pattern
compositePattern :: { Src.Pattern }
  : name patterns %shift { Src.PCtor (strV $1) $2 }

patterns :: { [Src.Pattern] }
  : nonCompositePattern          { [$1] }
  | patterns nonCompositePattern { $1 <> [$2] }

recordPattern :: { Src.Pattern }
  : '{' recordFieldPatterns '}' { Src.PRecord $2 }

recordFieldPatterns :: { M.Map Src.Name Src.Pattern }
  : name ':' pattern { M.fromList [(strV $1, $3)] }
  | recordFieldPatterns ',' name ':' pattern { M.insert (strV $3) $5 $1 }


record :: { Src.LExp }
  : '{' recordFields '}' { Located (tokenToLoc $1) (Src.Record $2) }

recordFields :: { Src.Fields }
  : name ':' exp                  { M.fromList [(strV $1, $3)] }
  | recordFields ',' name ':' exp { M.insert (strV $3) $5 $1 }


operation :: { Src.LExp }
  : exp '+' exp  { Located (Src.getLoc $1) (Src.App
                      ((Located (Src.getLoc $1) (Src.App
                         (Located (tokenToLoc $2) (Src.Var "+")) 
                         $1))) 
                      $3)
                 }
  | exp '-' exp  { Located (Src.getLoc $1) (Src.App
                      ((Located (Src.getLoc $1) (Src.App
                         (Located (tokenToLoc $2) (Src.Var "-")) 
                         $1))) 
                      $3)
                 }
  | exp '*' exp  { Located (Src.getLoc $1) (Src.App
                      ((Located (Src.getLoc $1) (Src.App
                         (Located (tokenToLoc $2) (Src.Var "*")) 
                         $1))) 
                      $3)
                 }
  | exp '/' exp  { Located (Src.getLoc $1) (Src.App
                      ((Located (Src.getLoc $1) (Src.App
                         (Located (tokenToLoc $2) (Src.Var "/")) 
                         $1))) 
                      $3)
                 }
  | exp '===' exp  { Located (Src.getLoc $1) (Src.App
                      ((Located (Src.getLoc $1) (Src.App
                         (Located (tokenToLoc $2) (Src.Var "===")) 
                         $1))) 
                      $3)
                   }
  | exp '|>' exp  { Located (Src.getLoc $1) (Src.App
                      ((Located (Src.getLoc $1) (Src.App
                         (Located (tokenToLoc $2) (Src.Var "|>")) 
                         $1))) 
                      $3)
                  
                  }

listConstructor :: { Src.LExp }
  : '[' listItems ']' { Located (tokenToLoc $1) (Src.ListConstructor $2) }

listItems :: { [Src.LExp] }
  : exp               { [$1] }
  | exp ',' listItems { $1 : $3 }
  | {- empty -}       { [] }

literal :: { Src.LExp }
  : int                       { Located (tokenToLoc $1) (Src.LInt $ strV $1) }
  | str                       { Located (tokenToLoc $1) (Src.LStr $ strV $1) }
  | true                      { Located (tokenToLoc $1) (Src.LBool $ strV $1) }
  | false                     { Located (tokenToLoc $1) (Src.LBool $ strV $1) }

args :: { [Src.LExp] }
  : exp rComa args %shift { $1:$3 }
  | exp maybeRet   %shift { [$1] }

params :: { [Src.Name] }
  : name ',' params %shift { strV $1 : $3 }
  | name                   { [strV $1] }

{
buildAbs :: Loc -> [Src.Name] -> Src.LExp -> Src.LExp
buildAbs loc [param] body = Located loc (Src.Abs param body)
buildAbs loc (x:xs) body  = Located loc (Src.Abs x (buildAbs loc xs body))

buildApp :: Loc -> Src.LExp -> [Src.LExp] -> Src.LExp
buildApp loc f [arg]  = Located loc (Src.App f arg)
buildApp loc f xs     = Located loc (Src.App (buildApp loc f (init xs)) (last xs))

nameToPattern :: String -> Src.Pattern
nameToPattern n | n == "_"           = Src.PAny
                | n == "String"      = Src.PCon n
                | n == "Bool"        = Src.PCon n
                | n == "Num"         = Src.PCon n
                | (isUpper . head) n = Src.PCtor n []
                | otherwise          = Src.PVar n


lexerWrap :: (Token -> Alex a) -> Alex a
lexerWrap f = alexMonadScan >>= f

parseError :: Token -> Alex a
parseError (Token (Loc a l c) cls) =
  alexError (printf "Syntax error - line: %d, column: %d\nThe following token is not valid: %s" l c (show cls))

parse :: String -> Either String Src.AST
parse s = runAlex s parseMadlib
}
