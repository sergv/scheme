----------------------------------------------------------------------------
-- |
-- Module      :  Types
-- Copyright   :  (c) Sergey Vinokurov 2014
-- License     :  BSD3-style (see LICENSE)
--
-- Maintainer  :  serg.foo@gmail.com
-- Stability   :
-- Portability :
--
--
----------------------------------------------------------------------------

{-# LANGUAGE DeriveFoldable        #-}
{-# LANGUAGE DeriveFunctor         #-}
{-# LANGUAGE DeriveTraversable     #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE KindSignatures        #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings     #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE StandaloneDeriving    #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE TemplateHaskell       #-}
{-# LANGUAGE TupleSections         #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE ViewPatterns          #-}
{-# LANGUAGE UndecidableInstances  #-}

module Types where

import Control.Monad.Except
import Data.Foldable (Foldable)
import Data.List.NonEmpty
import Data.Map (Map)
import Data.Text.Lazy (Text)
import Data.Traversable (Traversable)

import ALaCarte
import ALaCarte.TH

import Prelude hiding (mapM)

-- Compound types

-- filename, line, column
data Position = Position !Text !Int !Int
              deriving (Show, Eq, Ord)

newtype RawProgram = RawProgram (NonEmpty (Term (SchemeSexpF :&: Position)))
                   deriving (Show, Eq, Ord)

--- Basic types

newtype AInt    = AInt { getAInt :: Integer }
                deriving (Show, Eq, Ord)
newtype ADouble = ADouble { getADouble :: Double }
                deriving (Show, Eq, Ord)
newtype AString = AString { getAString :: Text }
                deriving (Show, Eq, Ord)
newtype ABool   = ABool { getABool :: Bool }
                deriving (Show, Eq, Ord)
data Nil        = Nil
                deriving (Show, Eq, Ord)

type AtomF = K Symbol :+: K AInt :+: K ADouble :+: K AString :+: K ABool :+: K Nil

-- data Atom = AInt Integer
--           | ADouble Double
--           | AString Text
--           | ABool Bool
--           | Nil
--           deriving (Show, Eq, Ord)

newtype Symbol = Symbol { getSymbol :: Text }
               deriving (Show, Eq, Ord)

data List f = List f [f] f
            deriving (Show, Eq, Ord, Functor, Foldable, Traversable)

data Vector f = Vector [f]
              deriving (Show, Eq, Ord, Functor, Foldable, Traversable)

type SchemeSexpF = Vector :+: List :+: AtomF

type SchemeSexp = Term SchemeSexpF

--- Closer to evaluation

newtype Address = Address { getAddress :: Int }
                deriving (Show, Eq, Ord)

newtype Frame = Frame (Map Symbol Address)
              deriving (Show, Eq, Ord)

newtype Env = Env [Frame]
            deriving (Show, Eq, Ord)

-- data Lambda f = Lambda Env [Symbol] f
data Lambda f = Lambda [Symbol] f
              deriving (Show, Eq, Ord, Functor, Foldable, Traversable)


data Primitive f = PrimitiveAdd f f
                 | PrimitiveSub f f
                 | PrimitiveMul f f
                 | PrimitiveDiv f f
                 | PrimitiveEq f f
                 -- Primitive Text ([SchemeData] -> f)
                 deriving (Show, Eq, Ord, Functor, Foldable, Traversable)

-- instance Show (Primitive f) where
--   show (Primitive tag _) = "Primitive " ++ tag

-- instance Eq (Primitive f) where
--   Primitive tag _ == Primitive tag' _ = tag == tag'
--
-- instance Ord (Primitive f) where
--   compare (Primitive tag _) (Primitive tag' _) = compare tag tag'

-- data Variable = Variable Symbol
--               deriving (Show, Eq, Ord)

newtype Quote = Quote SchemeSexp
              deriving (Show, Eq, Ord)

data Assign f = Assign f f
              deriving (Show, Eq, Ord, Functor, Foldable, Traversable)

data Define f = Define Symbol f
              deriving (Show, Eq, Ord, Functor, Foldable, Traversable)

data If f = If f f f
          deriving (Show, Eq, Ord, Functor, Foldable, Traversable)

data Begin f = Begin [f]
             deriving (Show, Eq, Ord, Functor, Foldable, Traversable)

data Apply f = Apply f [f]
             deriving (Show, Eq, Ord, Functor, Foldable, Traversable)

data Let f = Let [(f, f)] f
           deriving (Show, Eq, Ord, Functor, Foldable, Traversable)


data Cond f = Cond [(f, f)]
            deriving (Show, Eq, Ord, Functor, Foldable, Traversable)

data And f = And f f
           deriving (Show, Eq, Ord, Functor, Foldable, Traversable)

data Or f = Or f f
          deriving (Show, Eq, Ord, Functor, Foldable, Traversable)

data Not f = Not f
           deriving (Show, Eq, Ord, Functor, Foldable, Traversable)


-- no Lists since all lists must go away during translation
type SchemeExprF = Not :+: Or :+: And :+: Cond :+: Let :+: Apply :+: Begin :+:
                   If :+: Define :+: Assign :+: K Quote :+:
                   {-K Variable :+: Primitive :+:-} Lambda :+: Vector :+: AtomF
                                                          -- :+: SchemeSexpF
type SchemeExpr = Term SchemeExprF


isNil :: (K Nil :<: f) => f (Term (f :&: p)) -> Bool
isNil t = case proj t of
            Just (K Nil) -> True
            Nothing      -> False

isNilTerm :: (K Nil :<: f) => Term (f :&: p) -> Bool
isNilTerm (Term (t :&: _)) = isNil t


$(deriveInjectingConstructor ''AInt)
$(deriveInjectingConstructor ''ADouble)
$(deriveInjectingConstructor ''AString)
$(deriveInjectingConstructor ''ABool)
$(deriveInjectingConstructor ''Nil)
$(deriveInjectingConstructor ''Symbol)
$(deriveInjectingConstructor ''List)
$(deriveInjectingConstructor ''Vector)
$(deriveInjectingConstructor ''Lambda)

$(deriveInjectingConstructor ''Quote)
$(deriveInjectingConstructor ''Assign)
$(deriveInjectingConstructor ''Define)
$(deriveInjectingConstructor ''If)
$(deriveInjectingConstructor ''Begin)
$(deriveInjectingConstructor ''Apply)
$(deriveInjectingConstructor ''Let)
$(deriveInjectingConstructor ''Cond)
$(deriveInjectingConstructor ''And)
$(deriveInjectingConstructor ''Or)
$(deriveInjectingConstructor ''Not)

