----------------------------------------------------------------------------
-- |
-- Module      :  Utils
-- Copyright   :  (c) Sergey Vinokurov 2014
-- License     :  BSD3-style (see LICENSE)
--
-- Maintainer  :  serg.foo@gmail.com
-- Stability   :
-- Portability :
--
--
----------------------------------------------------------------------------

{-# LANGUAGE DeriveFunctor              #-}
{-# LANGUAGE DeriveTraversable          #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module Utils where

import Control.Applicative
import Control.Monad.Error
import Data.Text.Lazy (Text)
import qualified Data.Text.Lazy as T

show' :: (Show a) => a -> Text
show' = T.pack . show

newtype Err a = Err { runErr :: Either Text a } -- ErrorT Text Identity a
              deriving (Functor, Applicative, Monad, MonadError Text)

