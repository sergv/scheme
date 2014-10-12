{
{-# LANGUAGE OverloadedStrings #-}

module SexpFrontend.Parser (parseTerm, parse, runParser) where

import Control.Applicative
import Control.Monad.Error
import Control.Monad.Reader
import Data.List.NonEmpty
import Data.Maybe
import Data.Monoid
import Data.Text.Lazy (Text)
import qualified Data.Text.Lazy as T

import ALaCarte
import Types
import SexpFrontend.Lexer
import qualified SexpFrontend.LexTok as LexTok

}

%name parseProgram program
%partial parseSexp sexp
%tokentype { LexTok.LexTok }
%monad { Parser } { (>>=) } { return }

%error { parseError }

%lexer { lexWrapper } { LexTok.EOF }

%token '('      { LexTok.OpenParen }
%token ')'      { LexTok.CloseParen }
%token '#('     { LexTok.HashOpenParen }
%token QUOTE    { LexTok.Quote }
%token '.'      { LexTok.Dot }
%token STRING   { LexTok.String $$ }
%token NUMBER   { LexTok.Number $$ }
%token REAL     { LexTok.Real $$ }
%token BOOLEAN  { LexTok.Boolean $$ }
%token NIL      { LexTok.TokNil }
%token SYMBOL   { LexTok.Symbol $$ }
%token EOF      { LexTok.EOF }

%%

program         :: { RawProgram }
                : sexpsNE { RawProgram $1 }

sexpsNE         :: { NonEmpty (Term (SchemeSexpF :&: Position)) }
                : sexp sexps { $1 :| $2 }

sexps           :: { [Term (SchemeSexpF :&: Position)] }
                : sexp sexps { $1 : $2 }
                | {- empty -} { [] }

sexp            :: { Term (SchemeSexpF :&: Position) }
                : pos QUOTE sexp { Term (iList (Term (iSymbol "quote" :&: $1))
                                               [$3]
                                               (Term (iNil :&: $1))
                                         :&: $1)}
                | pos STRING     { Term (iAString $2 :&: $1) }
                | pos NUMBER     { Term (iAInt $2 :&: $1) }
                | pos REAL       { Term (iADouble $2 :&: $1) }
                | pos BOOLEAN    { Term (iABool $2 :&: $1) }
                | pos NIL        { Term (iNil :&: $1) }
                | pos SYMBOL     { Term (iSymbol $2 :&: $1) }
                | list           { $1 }
                | vector         { $1 }

list            :: { Term (SchemeSexpF :&: Position) }
                : pos '(' ')'                  { Term (iNil :&: $1) }
                | pos '(' sexpsNE pos ')'      { let (head :| body) = $3 in
                                                 Term (iList head body (Term (iNil :&: $4)) :&: $1) }
                | pos '(' sexpsNE '.' sexp ')' { let (head :| body) = $3 in
                                                 Term (iList head body $5 :&: $1) }

vector          :: { Term (SchemeSexpF :&: Position) }
                : pos '#(' sexps ')' { Term (iVector $3 :&: $1) }

pos             :: { Position }
                : {- empty -} {% lift (liftM alexLexPos alexGetInput) >>= \(LexPos line col) ->
                                   ask >>= \filename ->
                                     return $ Position filename line col
                              }

{

-- reader over filename
type Parser a = ReaderT Text Alex a

parse :: Text -> String -> Either String RawProgram
parse = runParser parseProgram

parseTerm :: Text -> String -> Either String SchemeSexp
parseTerm filename input = stripA <$> runParser parseSexp filename input

runParser :: Parser a -> Text -> String -> Either String a
runParser action filename input =
  runAlex input $ runReaderT action filename

lexWrapper :: (LexTok.LexTok -> Parser a) -> Parser a
lexWrapper cont = lift alexMonadScan >>= cont

parseError :: LexTok.LexTok -> Parser a
parseError tok = do
  -- fname <- ask
  let fname = "unknown"
  LexTok.LexPos line col <- lift $ liftM alexLexPos alexGetInput
  throwError $ T.unpack $
    "Happy: " <> fname <> ":" <> show' line <> ":" <> show' col <> ": " <> show' tok
parseError EOF = throwError "unexpected end of file"

show' :: (Show a) => a -> Text
show' = T.pack . show

}
