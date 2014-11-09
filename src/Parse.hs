----------------------------------------------------------------------------
-- |
-- Module      :  Parse
-- Copyright   :  (c) Sergey Vinokurov 2014
-- License     :  BSD3-style (see LICENSE)
--
-- Maintainer  :  serg.foo@gmail.com
-- Stability   :
-- Portability :
--
--
----------------------------------------------------------------------------

{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings     #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE TupleSections         #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE UndecidableInstances  #-}

module Parse (termParser, parseTerm) where

import Control.Applicative
import Data.List
import Data.Maybe (fromMaybe)
import Data.Text.Lazy (Text)
import Data.Vector (Vector)
import qualified Data.Vector as V
import qualified Data.Text.Lazy as T
import Text.ParserCombinators.UU hiding (Apply, Hole)
import Text.ParserCombinators.UU.BasicInstances hiding (Error)
import Text.ParserCombinators.UU.Utils hiding (listParser)

import ALaCarte
import Types

-- many1 :: (Alternative f) => f a -> f [a]
-- many1 p = ((:) <$> p <*> many p)

isWhitespace :: Char -> Bool
isWhitespace = (`elem` " \r\n\t")

ws :: Parser ()
ws = const () <$> pSatisfy isWhitespace ins
  where
    ins = Insertion "Insert character" ' ' 10

optionalSpace :: Parser ()
optionalSpace = const () <$> pMunch isWhitespace <?> "Optional whitespace"

mandatorySpace :: Parser ()
mandatorySpace = ws *> optionalSpace <?> "Mandatory whitespace"


parens :: ParserTrafo a a
parens p = pSym '(' *> p <* pSym ')'

numberParser :: forall f. (K AInt :<: f, K ADouble :<: f) => Parser (Term f)
numberParser =
  f <$> (consMb <$> sign <*> num)
    <*> pMaybe ((:) <$> dot <*> num)
    <*> pMaybe ((:) <$> e <*> (consMb <$> sign <*> num))
  where
    f :: String -> Maybe String -> Maybe String -> Term f
    f x Nothing Nothing = inject . K . AInt . read $ x
    f x y       z       = inject . K . ADouble . read $ x ++ y' ++ z'
      where
        y' = fromMaybe "" y
        z' = fromMaybe "" z
    sign = pMaybe (pSym '-' <|> pSym '+')
    -- num  = many1 pDigit
    dot  = pSym '.'
    e    = pSym 'e' <|> pSym 'E'

    num = (:) <$> pSatisfy isDigit ins <*> pMunch isDigit
    isDigit c = '0' <= c && c <= '9'
    ins = Insertion "Inserting character" 'Z' 10

    consMb :: Maybe a -> [a] -> [a]
    consMb (Just x) xs = x : xs
    consMb Nothing  xs = xs

-- TODO allow for \" inside strings, recognize \\, \n etc
-- todo replace pQuotedString by other version that is not surrounded with
-- lexeme
stringParser :: (K AString :<: f) => Parser (Term f)
stringParser = inject . K . AString . T.pack <$> pQuotedString

boolParser :: (K ABool :<: f) => Parser (Term f)
boolParser = inject . K . ABool <$> (pSym '#' *> (pure True <* pSym 't' <|>
                                                  pure False <* pSym 'f'))

symbolParser :: (K Nil :<: f, K Symbol :<: f) => Parser (Term f)
symbolParser = f . T.pack <$> ((:) <$> nondigitC <*> anyC)
  where
    f "nil" = Term iNil
    f x     = inject $ K $ Symbol x
    anyC = pMunch anySymbolChar
    anySymbolChar c = nonDigitSymbolChar c ||
                      '0' <= c && c <= '9'

    nondigitC = pSatisfy nonDigitSymbolChar ins
    nonDigitSymbolChar c = 'a' <= c && c <= 'z' ||
                           'A' <= c && c <= 'Z' ||
                           c == '-' ||
                           c == '+' ||
                           c == '*' ||
                           c == '/' ||
                           c == '!' ||
                           c == '?' ||
                           c == '<' ||
                           c == '>' ||
                           c == '=' ||
                           c == '_' ||
                           c == ':' ||
                           c == '.'
    ins = Insertion "Inserting character" 'Z' 10

listParser :: forall f. (List :<: f, K Nil :<: f) => Parser (Term f) -> Parser (Term f)
listParser p =
  parens $
    maybe (Term iNil) (\(h, (body, t)) -> inject $ List h body t) <$>
      pMaybe ((,) <$> p <*> tl)
  where
    tl :: Parser (Vector (Term f), Term f)
    tl = (mandatorySpace *>
           ((V.empty, ) <$> (pSym '.' *> mandatorySpace *> p) <<|>
            ((\x (xs, y) -> (V.cons x xs, y)) <$> p <*> tl)))
         <|> pure (V.empty, Term iNil)

-- listParser :: forall f. (List :<: f, K Nil :<: f) => Parser (Term f) -> Parser (Term f)
-- listParser p =
--   parens $
--     maybe (Term iNil) (\(h, body t) -> inject $ List h body t) <$>
--    -- pMaybe ((,,)    <$>
--    --         p       <*>
--    --         many p' <*>
--    --         (mandatorySpace *> pDot *> mandatorySpace *> p <|>
--    --          pure (Term iNil)))
--   -- where
--   --   p' = mandatorySpace *> p

-- TODO fix whitespace handling for vectors of one element, #(a) - space not
-- mandatory
vectorParser :: (Vect :<: f) => Parser (Term f) -> Parser (Term f)
vectorParser p = pSym '#' *> parens (inject . Vect . V.fromList <$> pListSep mandatorySpace p)

termParser :: (Vect :<: f, List :<: f, K Symbol :<: f,
               K AInt :<: f, K ADouble :<: f, K AString :<: f,
               K ABool :<: f, K Nil :<: f) =>
              Parser (Term f)
termParser = combine <$> pMaybe (pSym '\'' <* optionalSpace) <*> p
  where
    combine quote t =
      maybe t (const $ Term $ iList (Term $ iSymbol "quote") (V.singleton t) (Term iNil)) quote
    p =     numberParser
        <|> stringParser
        <|> boolParser
        <|> symbolParser
        <|> listParser termParser
        <|> vectorParser termParser

parseTerm :: (Vect :<: f, List :<: f, K Symbol :<: f,
              K AInt :<: f, K ADouble :<: f, K AString :<: f,
              K ABool :<: f, K Nil :<: f) =>
             String -> Text -> Term f
parseTerm fname src =
  case parse_h ((,) <$> termParser <*> pEnd) (Str src [] (LineColPos 0 0 0) False) of
    (res, []) -> res
    (_, errs) -> error $ "parseTerm: errors while parsing " ++ fname ++ ":\n" ++
                 intercalate "\n" (map show errs)

