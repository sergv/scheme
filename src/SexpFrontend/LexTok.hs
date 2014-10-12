----------------------------------------------------------------------------
-- |
-- Module      :  Frontend.LexTok
-- Copyright   :  (c) Sergey Vinokurov 2014
-- License     :  BSD3-style (see LICENSE)
--
-- Maintainer  :  serg.foo@gmail.com
-- Stability   :
-- Portability :
--
--
----------------------------------------------------------------------------

module SexpFrontend.LexTok where

import Data.Text.Lazy (Text)

-- line and column
data LexPos = LexPos !Int !Int
            deriving (Show, Eq, Ord)

data LexTok = OpenParen
            | CloseParen
            | HashOpenParen
            | Quote
            | Dot
            | TokNil
            | String Text
            | Number Integer
            | Real Double
            | Boolean Bool
            | Symbol Text
            | EOF
            deriving (Show, Eq, Ord)

