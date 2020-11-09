{
{-# LANGUAGE NamedFieldPuns                 #-}
{-# LANGUAGE FlexibleContexts                 #-}
{-# LANGUAGE OverloadedStrings                 #-}
{-# LANGUAGE NoMonomorphismRestriction          #-}
{-# LANGUAGE CPP                                #-}
{-# OPTIONS_GHC -fno-warn-unused-binds          #-}
{-# OPTIONS_GHC -fno-warn-missing-signatures    #-}
{-# OPTIONS_GHC -fno-warn-unused-matches        #-}
{-# OPTIONS_GHC -fno-warn-unused-imports        #-}
{-# OPTIONS_GHC -fno-warn-name-shadowing        #-}
{-# OPTIONS_GHC -fno-warn-tabs                  #-}
{-# OPTIONS_GHC -funbox-strict-fields           #-}

module Parse.Lexer
  ( Alex(..)
  , AlexState(..)
  , alexEOF
  , Token(..)
  , Loc(..)
  , TokenClass(..)
  , alexError
  , alexMonadScan
  , runAlex
  , tokenToArea
  , strV
  )
where

import           Control.Monad.State
import           System.Exit
import           Debug.Trace
import qualified Data.Text     as T
import           Explain.Location
}

%wrapper "monadUserState"

$digit = 0-9                    -- digits
$alpha = [a-zA-Z]               -- alphabetic characters
$empty =  [\ \t\f\v\r]          -- equivalent to $white but without line return

tokens :-
  \°\-\°                                { mapToken (\_ -> TokenRightParen) }
  \°\-\°\(                              { mapToken (\_ -> TokenLeftParen) }
  \°\-\°\)                              { mapToken (\_ -> TokenRightParen) }
  import                                { mapToken (\_ -> TokenImport) }
  export                                { mapToken (\_ -> TokenExport) }
  from                                  { mapToken (\_ -> TokenFrom) }
  data                                  { mapToken (\_ -> TokenData) }
  const                                 { mapToken (\_ -> TokenConst) }
  if                                    { mapToken (\_ -> TokenIf) }
  else                                  { mapToken (\_ -> TokenElse) }
  where                                 { mapToken (\_ -> TokenWhere) }
  is                                    { mapToken (\_ -> TokenIs) }
  \=                                    { mapToken (\_ -> TokenEq) }
  $digit+                               { mapToken (\s -> TokenInt s) }
  "True"                                { mapToken (\_ -> (TokenBool "True")) }
  "False"                               { mapToken (\_ -> (TokenBool "False")) }
  "=="                                  { mapToken (\_ -> TokenDoubleEq) }
  \.                                    { mapToken (\_ -> TokenDot) }
  \,                                    { mapToken (\_ -> TokenComma) }
  \{                                    { mapToken (\_ -> TokenLeftCurly) }
  \}                                    { mapToken (\_ -> TokenRightCurly) }
  \[                                    { mapToken (\_ -> TokenLeftSquaredBracket) }
  \]                                    { mapToken (\_ -> TokenRightSquaredBracket) }
  \(                                    { mapToken (\_ -> TokenLeftParen) }
  \)                                    { mapToken (\_ -> TokenRightParen) }
  \:\:                                  { mapToken (\_ -> TokenDoubleColon) }
  \:                                    { mapToken (\_ -> TokenColon) }
  \-\>                                  { mapToken (\_ -> TokenArrow) }
  \=\>                                  { mapToken (\_ -> TokenFatArrow) }
  \|                                    { mapToken (\_ -> TokenPipe) }
  \;                                    { mapToken (\_ -> TokenSemiColon) }
  \n[\ ]*                               { updateIndent }
  [\n]                                  { mapToken (\_ -> TokenReturn) }
  [$alpha \_] [$alpha $digit \_ \']*    { mapToken (\s -> TokenName s) }
  [\n \ ]*\+                            { mapToken (\_ -> TokenPlus) }
  \-                                    { mapToken (\_ -> TokenDash) }
  [\n \ ]*\?                            { mapToken (\_ -> TokenQuestionMark) }
  \n[\ ]*\-                             { mapToken (\_ -> TokenDash) }
  [\n \ ]*\*                            { mapToken (\_ -> TokenStar) }
  [\n \ ]*\/                            { mapToken (\_ -> TokenSlash) }
  \|\>                                  { mapToken (\_ -> TokenPipeOperator) }
  \.\.\.                                { mapToken (\_ -> TokenSpreadOperator) }
  \.\.\.                                { mapToken (\_ -> TokenSpreadOperator) }
  \&\&                                  { mapToken (\_ -> TokenDoubleAmpersand) }
  \|\|                                  { mapToken (\_ -> TokenDoublePipe) }
  \>                                    { mapToken (\_ -> TokenRightChevron) }
  \<                                    { mapToken (\_ -> TokenLeftChevron) }
  \>\=                                  { mapToken (\_ -> TokenRightChevronEq) }
  \<\=                                  { mapToken (\_ -> TokenLeftChevronEq) }
  \!                                    { mapToken (\_ -> TokenExclamationMark) }
  \"($printable # \")+\"                { mapToken (\s -> TokenStr (sanitizeStr s)) }
  \#\- [$alpha $digit \" \_ \' \ \+ \. \, \( \) \; \: \{ \} \n \= \> \\ \/]* \-\#
    { mapToken (\s -> TokenJSBlock (sanitizeJSBlock s)) }
  [\ \n]*"//".*                         ; -- Comments
  $empty+                               ;

{
data AlexUserState = AlexUserState [Int] deriving(Eq, Show)

alexInitUserState :: AlexUserState
alexInitUserState = AlexUserState []

sanitizeStr :: String -> String
sanitizeStr = tail . init

sanitizeJSBlock :: String -> String
sanitizeJSBlock = strip . tail . tail . init . init

strip  = T.unpack . T.strip . T.pack


updateIndent :: AlexInput -> Int -> Alex Token
updateIndent input len = do
  let currentIndent = len - 1
  (AlexUserState indentStack) <- Alex $ \s@AlexState{alex_ust=ust} -> Right (s, ust)
  let previousIndent = if length indentStack > 0 then last indentStack else 0

  shouldAdd <- if length indentStack == 0
    then Alex $ \s -> Right (s { alex_ust = AlexUserState [currentIndent] }, True)
    else Alex $ \s -> Right (s, False)

  if shouldAdd
  then
    Alex $ \s@AlexState{alex_ust=ust, alex_inp, alex_pos = AlexPn a l c} -> Right (s { alex_inp = "°-°(" <> alex_inp,  alex_pos = AlexPn (a - 4) l (c - 4) }, ())
  else
    if currentIndent > previousIndent
    then do
      Alex $ \s@AlexState{alex_ust=ust} -> Right (s { alex_ust = AlexUserState $ indentStack <> [currentIndent] }, ())
      Alex $ \s@AlexState{alex_ust=ust, alex_inp, alex_pos = AlexPn a l c} -> Right (s { alex_inp = "°-°(" <> alex_inp,  alex_pos = AlexPn (a - 4) l (c - 4) }, ())
    else
      if currentIndent < previousIndent
      then do
        popIndents currentIndent
      else
        Alex $ \s -> Right (s, ())
  
  alexMonadScan


popIndents :: Int -> Alex ()
popIndents currentIndent = do
  (AlexUserState indentStack) <- Alex $ \s@AlexState{alex_ust=ust} -> Right (s, ust)
  let previousIndent = last indentStack

  if currentIndent < previousIndent && length indentStack > 1
  then do
    Alex $ \s@AlexState{alex_inp, alex_pos = AlexPn a l c} -> (Right (s { alex_inp = "°-°)" <> alex_inp,  alex_pos = AlexPn (a - 4) l (c - 4), alex_ust = AlexUserState $ init indentStack }, ()))
    popIndents currentIndent
  else do
    Alex $ \s@AlexState{alex_inp, alex_pos = AlexPn a l c} -> (Right (s { alex_inp = "°-°)" <> alex_inp,  alex_pos = AlexPn (a - 4) l (c - 4), alex_ust = AlexUserState $ init indentStack }, ()))
    Alex $ \s -> (Right (s, ()))

popAllIndents :: Alex ()
popAllIndents = do
  (AlexUserState indentStack) <- Alex $ \s@AlexState{alex_ust=ust} -> Right (s, ust)
  if length indentStack > 0
  then do
    Alex $ \s@AlexState{alex_inp, alex_pos = AlexPn a l c} -> (Right (s { alex_inp = "°-°)" <> alex_inp,  alex_pos = AlexPn (a - 4) l (c - 4), alex_ust = AlexUserState $ init indentStack }, ()))
    popAllIndents
  else
    Alex $ \s -> (Right (s, ()))



mapToken :: (String -> TokenClass) -> AlexInput -> Int -> Alex Token
mapToken tokenizer (posn, prevChar, pending, input) len = do
  s <- Alex $ \s@AlexState{alex_ust=ust} -> Right (s, ust)
  -- return $ Token (makeArea posn (take len input)) token
  return $ Token (makeArea posn (take len input)) (trace (show s) token)
  -- where token = tokenizer (take len input)
  where token = trace (show $ tokenizer (take len input)) (tokenizer (take len input))


makeArea :: AlexPosn -> String -> Area
makeArea (AlexPn a l c) tokenContent =
  let start         = Loc a l c
      contentLines  = lines tokenContent
      lastLine      = last contentLines
      numberOfLines = length contentLines
      end           = if numberOfLines > 1
                      then Loc (a + length tokenContent) (l + numberOfLines - 1) (length lastLine)
                      else Loc (a + length tokenContent) l (c + length tokenContent)
  in  Area start end

tokenToArea :: Token -> Area
tokenToArea (Token area _) = area

data Token = Token Area TokenClass deriving (Eq, Show)

data TokenClass
 = TokenConst
 | TokenInt  String
 | TokenStr  String
 | TokenName String
 | TokenDottedName String
 | TokenJSBlock String
 | TokenBool String
 | TokenIf
 | TokenElse
 | TokenWhere
 | TokenIs
 | TokenEq
 | TokenPlus
 | TokenDash
 | TokenStar
 | TokenSlash
 | TokenDoubleEq
 | TokenComma
 | TokenLeftCurly
 | TokenRightCurly
 | TokenLeftSquaredBracket
 | TokenRightSquaredBracket
 | TokenLeftParen
 | TokenRightParen
 | TokenDoubleColon
 | TokenColon
 | TokenQuestionMark
 | TokenDot
 | TokenArrow
 | TokenFatArrow
 | TokenEOF
 | TokenImport
 | TokenExport
 | TokenFrom
 | TokenPipe
 | TokenPipeOperator
 | TokenSpreadOperator
 | TokenData
 | TokenSemiColon
 | TokenReturn
 | TokenDoubleAmpersand
 | TokenDoublePipe
 | TokenRightChevron
 | TokenLeftChevron
 | TokenRightChevronEq
 | TokenLeftChevronEq
 | TokenExclamationMark
 deriving (Eq, Show)


strV :: Token -> String
strV (Token _ (TokenStr x))  = x
strV (Token _ (TokenInt x)) = x
strV (Token _ (TokenBool x)) = x
strV (Token _ (TokenName x)) = x
strV (Token _ (TokenJSBlock x)) = x


alexEOF :: Alex Token
alexEOF = do
  (AlexUserState indentStack) <- Alex $ \s@AlexState{alex_ust=ust} -> Right (s, ust)

  if length indentStack > 0
  then do
    popAllIndents
    alexMonadScan
  else
    return (Token (Area (Loc 1 1 1) (Loc 1 1 1)) TokenEOF)
}
