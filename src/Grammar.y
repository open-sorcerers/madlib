{
module Grammar where
import Lexer
import Text.Printf
}

%name parseMadlib
%tokentype { Token }
%error { parseError }
%monad { Alex }
%lexer { lexerWrap } { Token _ TokenEOF }

%token
  const { Token _ TokenConst }
  int   { Token _ (TokenInt _) }
  str   { Token _ (TokenStr _) }
  name  { Token _ (TokenName _) }
  '='   { Token _ TokenEq }
  '+'   { Token _ TokenPlus }
  '-'   { Token _ TokenMinus }
  '/'   { Token _ TokenSlash }
  '*'   { Token _ TokenAsterisk }
  '::'  { Token _ TokenDoubleColon }
  '->'  { Token _ TokenArrow }
  '=>'  { Token _ TokenFatArrow }
  if    { Token _ TokenIf }
  ','   { Token _ TokenComa }
  '{'   { Token _ TokenLeftCurly }
  '}'   { Token _ TokenRightCurly }
  '('   { Token _ TokenLeftParen }
  ')'   { Token _ TokenRightParen }
  '===' { Token _ TokenTripleEq }
  false { Token _ (TokenBool _) }
  true  { Token _ (TokenBool _) }
%%

program :: { Program }
  : functionDefs { Program { functions = $1 } }

functionDefs :: { [FunctionDef] }
  : functionDef functionDefs { $1:$2 }
  | functionDef              { [$1] }

functionDef :: { FunctionDef }
-- Until we have inference, should we disallow that one ?
  : name '=' '(' params ')' '=>' body         { FunctionDef { ftype = Nothing
                                                            , ftypeDef = Nothing -- map (const "*") $4 ??
                                                            , fpos = tokenToPos $1
                                                            , fname = strV $1
                                                            , fparams = $4
                                                            , fbody = $7 }}
  | typing name '=' '(' params ')' '=>' body  { FunctionDef { ftype = Nothing
                                                            , ftypeDef = Just $1
                                                            , fpos = tpos $1
                                                            , fname = strV $2
                                                            , fparams = $5
                                                            , fbody = $8 }}

-- TODO: Make it a TypeDecl ?
typing :: { Typing }
  : name '::' types { Typing { tpos = tokenToPos $1, tfor = strV $1, ttypes = $3 } }

types :: { [Type] }
  : name '->' types { (strV $1) : $3 }
  | name            { [(strV $1)] }

exps :: { [Exp] }
  : exp exps            { $1 : $2 }
  | exp                 { [$1] }

exp :: { Exp }
  : int                     { IntLit    { etype = Just "Num", epos = tokenToPos $1} }
  | str                     { StringLit { etype = Just "String", epos = tokenToPos $1} }
  | false                   { BoolLit   { etype = Just "Bool", epos = tokenToPos $1} }
  | true                    { BoolLit   { etype = Just "Bool", epos = tokenToPos $1} }
  | exp operator exp        { Operation { etype = Nothing, epos = epos $1, eleft = $1, eoperator = $2, eright = $3 }}
  | name                    { VarAccess { etype = Nothing, epos = tokenToPos $1, ename = strV $1 }}

params :: { [Param] }
  : name ',' params { (strV $1) : $3 }
  | name            { [(strV $1)] }

body :: { Body }
  : exp { Body $1 }

operator :: { Operator }
  : '===' { TripleEq }
  | '+'   { Plus }
  | '-'   { Minus }
  | '/'   { Slash }
  | '*'   { Asterisk }

{

data Program = Program { functions :: [FunctionDef] } deriving(Eq, Show)

-- TODO: Remove ftype from FunctionDef ?
data FunctionDef = FunctionDef { ftype :: Maybe Type
                               , ftypeDef :: Maybe Typing
                               , fpos :: Pos
                               , fname :: String
                               , fparams :: [Param]
                               , fbody :: Body }
  deriving(Eq, Show)

data Typing = Typing { tpos :: Pos, tfor :: Name, ttypes :: [Type] } deriving(Eq, Show)

data Exp = IntLit    { etype :: Maybe Type, epos :: Pos }
         | StringLit { etype :: Maybe Type, epos :: Pos }
         | BoolLit   { etype :: Maybe Type, epos :: Pos }
         | Operation { etype :: Maybe Type, epos :: Pos, eleft :: Exp, eoperator :: Operator, eright :: Exp }
         | VarAccess { etype :: Maybe Type, epos :: Pos, ename :: Name }
  deriving(Eq, Show)

type Type  = String
type Param = String
type Name  = String

data Body = Body Exp deriving(Eq, Show)

data Operator = TripleEq 
              | Plus
              | Minus
              | Slash
              | Asterisk
  deriving(Eq, Show)

lexerWrap :: (Token -> Alex a) -> Alex a
lexerWrap cont = do
    token <- alexMonadScan
    cont token

parseError :: Token -> Alex a
parseError (Token (Pos a l c) cls) = alexError (printf "Syntax error - line: %d, column: %d\nThe following token is not valid: %s" l c (show cls))

parse :: String -> Either String Program
parse s = runAlex s parseMadlib
}
