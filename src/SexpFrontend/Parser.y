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
import qualified Data.Vector as V
import qualified Data.Text.Lazy as T

import ALaCarte
import Types
import SexpFrontend.Lexer
import qualified SexpFrontend.LexTok as LexTok
import Utils

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

sexpsNE         :: { NonEmpty (Term (SchemeSexpF :&: U Position)) }
                : sexp sexps { $1 :| $2 }

sexps           :: { [Term (SchemeSexpF :&: U Position)] }
                : sexp sexps { $1 : $2 }
                | {- empty -} { [] }

sexp            :: { Term (SchemeSexpF :&: U Position) }
                : pos QUOTE sexp { Term (iList (Term (iSymbol "quote" :&: $1))
                                               (V.singleton $3)
                                               (Term (iNil :&: $1))
                                         :&: $1)
                                 }
                | pos STRING     { Term (iAString $2 :&: $1) }
                | pos NUMBER     { Term (iAInt $2 :&: $1) }
                | pos REAL       { Term (iADouble $2 :&: $1) }
                | pos BOOLEAN    { Term (iABool $2 :&: $1) }
                | pos NIL        { Term (iNil :&: $1) }
                | pos SYMBOL     { Term (iSymbol $2 :&: $1) }
                | list           { $1 }
                | vector         { $1 }

list            :: { Term (SchemeSexpF :&: U Position) }
                : pos '(' ')'                  { Term (iNil :&: $1) }
                | pos '(' sexpsNE pos ')'      { let (head :| body) = $3 in
                                                 Term (iList head (V.fromList body) (Term (iNil :&: $4)) :&: $1) }
                | pos '(' sexpsNE '.' sexp ')' { let (head :| body) = $3 in
                                                 Term (iList head (V.fromList body) $5 :&: $1) }

vector          :: { Term (SchemeSexpF :&: U Position) }
                : pos '#(' sexps ')' { Term (iVect (V.fromList $3) :&: $1) }

-- dummy rule to get current position
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

parseTerm :: Text -> Text -> Either String (Term (SchemeSexpF :&: U Position))
parseTerm filename input = runParser parseSexp filename (T.unpack input)

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

}
