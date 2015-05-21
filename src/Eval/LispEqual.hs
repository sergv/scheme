----------------------------------------------------------------------------
-- |
-- Module      :  Eval.LispEqual
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
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE UndecidableInstances  #-}

module Eval.LispEqual where

import Data.Text.Lazy (Text)
-- import Data.Traversable (mapM)
import Data.Vector (Vector)
import qualified Data.Vector as V

import ALaCarte
import Types
import Utils

class LispEqual f h where
  lispEqual :: f (Term h) -> f (Term h) -> Bool

-- instance (LispEqual f h, LispEqual g h) => LispEqual (f :+: g) h where
--   lispEqual (Inl x) (Inl y) = lispEqual x y
--   lispEqual (Inl _) (Inr _) = False
--   lispEqual (Inr _) (Inl _) = False
--   lispEqual (Inr x) (Inr y) = lispEqual x y

instance (Eq (f (Term h))) => LispEqual f h where
  lispEqual = (==)
