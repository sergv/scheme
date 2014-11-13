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
{-# LANGUAGE OverloadedLists       #-}
{-# LANGUAGE OverloadedStrings     #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE StandaloneDeriving    #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE TemplateHaskell       #-}
{-# LANGUAGE TupleSections         #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE ViewPatterns          #-}
{-# LANGUAGE UndecidableInstances  #-}

-- {-# OPTIONS_GHC -ddump-splices #-}

{-# OPTIONS_GHC -fcontext-stack=100 #-}

module Types where

import Control.Applicative
import Control.Monad.Error
import Data.Foldable (Foldable)
import Data.IntMap (IntMap)
import qualified Data.IntMap as IM
import Data.List.NonEmpty
import Data.Map (Map)
import qualified Data.Map as M
import Data.Monoid
import Data.Text.Lazy (Text)
import Data.Traversable (Traversable)
import Data.Vector (Vector)
import qualified Data.Vector as V

import Text.PrettyPrint.Leijen.Text (Pretty, Doc)
import qualified Text.PrettyPrint.Leijen.Text as PP

import ALaCarte
import ALaCarte.TH
import Utils

import Prelude hiding (mapM)

-- Compound types

-- filename, line, column
data Position = Position !Text !Int !Int
              deriving (Show, Eq, Ord)

showPos :: Position -> Text
showPos (Position file line col) =
  file <> ":" <>  show' line <> ":" <> show' col <> ": "

newtype RawProgram = RawProgram (NonEmpty (Term (SchemeSexpF :&: U Position)))
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

newtype Symbol = Symbol { getSymbol :: Text }
               deriving (Show, Eq, Ord)

data List f = List f (Vector f) f
            deriving (Show, Eq, Ord, Functor, Foldable, Traversable)

data Vect f = Vect (Vector f)
            deriving (Show, Eq, Ord, Functor, Foldable, Traversable)

type SchemeSexpF = Vect :+: List :+: AtomF

type SchemeSexp = Term SchemeSexpF

--- prettyprinter for scheme sexps

showSexp :: (Pretty a) => a -> Text
showSexp = PP.displayT . PP.renderPretty 0.8 80 . PP.pretty

class PrettyAlg f g where
  prettyAlg :: f (Doc, Term g) -> Doc

instance (PrettyAlg f h, PrettyAlg g h) => PrettyAlg (f :+: g) h where
  prettyAlg (Inl f) = prettyAlg f
  prettyAlg (Inr g) = prettyAlg g

instance PrettyAlg (K AInt) g where
  prettyAlg (K (AInt n)) = PP.integer n
instance PrettyAlg (K ADouble) g where
  prettyAlg (K (ADouble x)) = PP.double x
instance PrettyAlg (K AString) g where
  prettyAlg (K (AString s)) = PP.dquotes $ PP.text s
instance PrettyAlg (K ABool) g where
  prettyAlg (K (ABool b)) = PP.text $ if b == True then "#t" else "#f"
instance PrettyAlg (K Nil) g where
  prettyAlg (K Nil) = PP.text "nil"
instance PrettyAlg (K Symbol) g where
  prettyAlg (K (Symbol sym)) = PP.text sym
instance (K Nil :<: g) => PrettyAlg List g where
  prettyAlg (List (x, _) xs (t, tExpr)) =
    case (xs, project tExpr) of
      ([], Just (K Nil)) -> PP.parens x
      (_, Just (K Nil))  -> PP.parens $ x PP.<+> PP.align (PP.sep $ V.toList $ V.map fst xs)
      (_, Nothing)       -> PP.parens $ x PP.<+> PP.align (PP.sep $ V.toList (V.map fst xs) ++ [PP.dot, t])
instance PrettyAlg Vect g where
  prettyAlg (Vect xs) =
    PP.text "#(" <> PP.cat (V.toList $ V.map fst xs) <> PP.text ")"
instance Pretty SchemeSexp where
  pretty = para prettyAlg

--- Closer to evaluation, this is the abstract syntax

-- syntactic lambda form
data Lambda f = Lambda (Vector Symbol) f
              deriving (Show, Eq, Ord, Functor, Foldable, Traversable)

newtype Quote = Quote SchemeSexp
              deriving (Show, Eq, Ord)

data Assign f = Assign Symbol f
              deriving (Show, Eq, Ord, Functor, Foldable, Traversable)

data Define f = Define Symbol f
              deriving (Show, Eq, Ord, Functor, Foldable, Traversable)

data If f = If f f f
          deriving (Show, Eq, Ord, Functor, Foldable, Traversable)

data Begin f = Begin (Vector f)
             deriving (Show, Eq, Ord, Functor, Foldable, Traversable)

data Apply f = Apply f (Vector f)
             deriving (Show, Eq, Ord, Functor, Foldable, Traversable)

data Let f = Let (Vector (Symbol, f)) f
           deriving (Show, Eq, Ord, Functor, Foldable, Traversable)


data Cond f = Cond
                (Vector (f, f)) -- cases
                (Maybe f) -- optional else clause
            deriving (Show, Eq, Ord, Functor, Foldable, Traversable)

data And f = And f f
           deriving (Show, Eq, Ord, Functor, Foldable, Traversable)

data Or f = Or f f
          deriving (Show, Eq, Ord, Functor, Foldable, Traversable)

data Not f = Not f
           deriving (Show, Eq, Ord, Functor, Foldable, Traversable)

type SpecialFormF = Not :+: Or :+: And :+: Cond :+: Let :+: Apply :+: Begin :+:
                    If :+: Define :+: Assign :+: K Quote :+: Lambda

-- no Lists since all lists must go away during translation
type SchemeExprF = Concat SpecialFormF (Vect :+: AtomF)
type SchemeExpr = Term SchemeExprF

-- Form without Cond.
type CoreSpecialFormF = Not :+: Or :+: And :+: Let :+: Apply :+: Begin :+:
                        If :+: Define :+: Assign :+: K Quote :+: Lambda
type SchemeCoreExprF = Concat CoreSpecialFormF (Vect :+: AtomF)
type SchemeCoreExpr = Term SchemeCoreExprF


isNil :: (K Nil :<: f) => f ix -> Bool
isNil t = case proj t of
            Just (K Nil) -> True
            Nothing      -> False

isNilTerm :: (K Nil :<: f) => Term (f :&: p) -> Bool
isNilTerm = isNil . unTerm . stripA

-- Values that evaluation produces

newtype Memory v = Memory { getMemory :: IntMap v }
                 deriving (Show, Eq, Ord)

lookupMem :: Address -> Memory v -> Maybe v
lookupMem (Address n) (Memory m) = IM.lookup n m

newtype Address = Address { getAddress :: Int }
                deriving (Show, Eq, Ord)

addToMemory :: Address -> v -> Memory v -> Memory v
addToMemory (Address n) obj (Memory items) = Memory $ IM.insert n obj items

newtype Frame = Frame { getFrame :: Map Symbol Address }
              deriving (Show, Eq, Ord)

addToFrame :: Symbol -> Address -> Frame -> Frame
addToFrame sym addr = Frame . M.insert sym addr . getFrame

newtype Env = Env { getEnv :: Vector Frame }
            deriving (Show, Eq, Ord)

addFrame :: Frame -> Env -> Env
addFrame frame = Env . V.cons frame . getEnv

data Closure e = Closure Env (Vector Symbol) (Term e)

iClosure :: (K (Closure e) :<: f) => Env -> Vector Symbol -> Term e -> f a
iClosure env args body = inj $ K $ Closure env args body

deriving instance (Show (Term e)) => Show (Closure e)
deriving instance (Eq (Term e)) => Eq (Closure e)
deriving instance (Ord (Term e)) => Ord (Closure e)

data PrimitiveAdd   = PrimitiveAdd deriving (Show, Eq, Ord)
data PrimitiveSub   = PrimitiveSub deriving (Show, Eq, Ord)
data PrimitiveMul   = PrimitiveMul deriving (Show, Eq, Ord)
data PrimitiveDiv   = PrimitiveDiv deriving (Show, Eq, Ord)
data PrimitiveEq    = PrimitiveEq deriving (Show, Eq, Ord)
data PrimitiveLt    = PrimitiveLt deriving (Show, Eq, Ord)
data PrimitiveLe    = PrimitiveLe deriving (Show, Eq, Ord)
data PrimitiveGt    = PrimitiveGt deriving (Show, Eq, Ord)
data PrimitiveGe    = PrimitiveGe deriving (Show, Eq, Ord)
data PrimitiveCons  = PrimitiveCons deriving (Show, Eq, Ord)
data PrimitiveCar   = PrimitiveCar deriving (Show, Eq, Ord)
data PrimitiveCdr   = PrimitiveCdr deriving (Show, Eq, Ord)
data PrimitiveIsNil = PrimitiveIsNil deriving (Show, Eq, Ord)

type PrimitiveFunc =
  K PrimitiveAdd :+: K PrimitiveSub :+: K PrimitiveMul :+: K PrimitiveDiv :+:
  K PrimitiveEq :+: K PrimitiveLt :+: K PrimitiveLe :+:
  K PrimitiveGt :+: K PrimitiveGe :+:
  K PrimitiveCons :+: K PrimitiveCar :+: K PrimitiveCdr :+: K PrimitiveIsNil

type SchemeValF e = Concat PrimitiveFunc (K (Closure e) :+: List :+: Vect :+: AtomF)
type SchemeVal e = Term (SchemeValF e)

lookupInEnv :: Symbol -> Frame -> Env -> Maybe Address
lookupInEnv sym frame (Env frames) =
  lookInFrame frame <|> V.foldl' (<|>) empty (V.map lookInFrame frames)
  where
    lookInFrame :: Frame -> Maybe Address
    lookInFrame (Frame table) = M.lookup sym table


$(deriveInjectingConstructor ''AInt)
$(deriveInjectingConstructor ''ADouble)
$(deriveInjectingConstructor ''AString)
$(deriveInjectingConstructor ''ABool)
$(deriveInjectingConstructor ''Nil)
$(deriveInjectingConstructor ''Symbol)
$(deriveInjectingConstructor ''List)
$(deriveInjectingConstructor ''Vect)
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

$(deriveInjectingConstructor ''PrimitiveAdd)
$(deriveInjectingConstructor ''PrimitiveSub)
$(deriveInjectingConstructor ''PrimitiveMul)
$(deriveInjectingConstructor ''PrimitiveDiv)
$(deriveInjectingConstructor ''PrimitiveEq)
$(deriveInjectingConstructor ''PrimitiveLt)
$(deriveInjectingConstructor ''PrimitiveLe)
$(deriveInjectingConstructor ''PrimitiveGt)
$(deriveInjectingConstructor ''PrimitiveGe)
$(deriveInjectingConstructor ''PrimitiveCons)
$(deriveInjectingConstructor ''PrimitiveCar)
$(deriveInjectingConstructor ''PrimitiveCdr)
$(deriveInjectingConstructor ''PrimitiveIsNil)
