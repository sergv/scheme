----------------------------------------------------------------------------
-- |
-- Module      :  ALaCarte
-- Copyright   :  (c) Sergey Vinokurov 2014
-- License     :  BSD3-style (see LICENSE)
--
-- Maintainer  :  serg.foo@gmail.com
-- Stability   :
-- Portability :
--
--
----------------------------------------------------------------------------

{-# LANGUAGE DeriveFoldable         #-}
{-# LANGUAGE DeriveFunctor          #-}
{-# LANGUAGE DeriveTraversable      #-}
{-# LANGUAGE EmptyDataDecls         #-}
{-# LANGUAGE FlexibleContexts       #-}
{-# LANGUAGE FlexibleInstances      #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE GADTs                  #-}
{-# LANGUAGE KindSignatures         #-}
{-# LANGUAGE MultiParamTypeClasses  #-}
{-# LANGUAGE OverlappingInstances   #-}
{-# LANGUAGE RankNTypes             #-}
{-# LANGUAGE ScopedTypeVariables    #-}
{-# LANGUAGE StandaloneDeriving     #-}
{-# LANGUAGE TupleSections          #-}
{-# LANGUAGE TypeOperators          #-}
{-# LANGUAGE UndecidableInstances   #-}

module ALaCarte where

import Control.Applicative
import Control.Monad hiding (mapM, sequence)
import Data.Foldable (Foldable)
import Data.Traversable (Traversable, mapM)
import Data.Void
import Prelude hiding (mapM, sequence)

data (:+:) f g ix = Inl (f ix)
                  | Inr (g ix)
                  deriving (Eq, Ord, Functor, Foldable, Traversable)

instance (Show (f ix), Show (g ix)) => Show ((f :+: g) ix) where
  showsPrec n (Inl f) = showsPrec n f
  showsPrec n (Inr g) = showsPrec n g
  -- show (Inl f) = show f
  -- show (Inr g) = show g

infixr 6 :+:

data (:&:) f p ix = f ix :&: p
                  deriving (Eq, Ord, Show, Functor, Foldable, Traversable)

infixl 6 :&:

ann :: (f :&: p) ix -> p
ann (_ :&: p) = p

remA :: (f :&: p) ix -> f ix
remA (f :&: _) = f

stripA :: (Functor f) => Term (f :&: p) -> Term f
stripA = cata (Term . remA)

-- instance (Functor f, Functor g) => Functor (f :+: g) where
--   fmap h (Inl f) = Inl $ fmap h f
--   fmap h (Inr g) = Inr $ fmap h g

class f :<: g where
  inj  :: f a -> g a
  proj :: g a -> Maybe (f a)

instance f :<: f where
  inj  = id
  proj = Just

instance f :<: (f :+: g) where
  inj = Inl
  proj (Inl x) = Just x
  proj _       = Nothing

instance (f :<: g) => f :<: (h :+: g) where
  inj = Inr . inj
  proj (Inr x) = proj x
  proj _       = Nothing

newtype K a b = K { unK :: a }
              deriving (Eq, Ord, Functor, Foldable, Traversable)

instance (Show a) => Show (K a b) where
  showsPrec n (K a) = showParen (n == 11) $ \xs -> "K " ++ showsPrec 11 a xs

data Hole
data NoHole

data Ctx :: * -> (* -> *) -> * -> * where
  Term :: f (Ctx h f a) -> Ctx h f a
  Hole :: a -> Ctx Hole f a

-- deriving instance (Show (f (Ctx h f a)), Show a) => Show (Ctx h f a)
instance (Show (f (Ctx h f a)), Show a) => Show (Ctx h f a) where
  showsPrec n (Term t) = showParen (n == 11) $ \xs -> "Term " ++ showsPrec 11 t xs
  showsPrec n (Hole x) = showParen (n == 11) $ \xs -> "Hole " ++ showsPrec 11 x xs

deriving instance (Eq (f (Ctx h f a)), Eq a) => Eq (Ctx h f a)
deriving instance (Ord (f (Ctx h f a)), Ord a) => Ord (Ctx h f a)

type Term f = Ctx NoHole f Void
type Context f a = Ctx Hole f a

-- Symbol to symbol term homomorphism transformation>
symToSym :: (Functor f) => Term f -> Context f (Term f)
symToSym (Term t) = Term $ fmap Hole t

inject :: (f :<: g) => f (Ctx h g a) -> Ctx h g a
inject = Term . inj

project :: (f :<: g) => Ctx h g a -> Maybe (f (Ctx h g a))
project (Term t) = proj t
project (Hole _) = Nothing

unTerm :: Term f -> f (Term f)
unTerm (Term t) = t

-- unTerm :: Ctx h f a -> f (Ctx h f a)
-- unTerm (Term t) = t
-- unTerm (Hole _) = error "error: unTerm applied to Hole"

unTermSafe :: Ctx h f a -> Maybe (f (Ctx h f a))
unTermSafe (Term t) = Just t
unTermSafe (Hole _) = Nothing

cata :: (Functor f) => Alg f a -> Term f -> a
cata alg (Term t) = alg $ fmap (cata alg) t

cataM :: (Traversable t, Monad m) => AlgM m t a -> Term t -> m a
cataM alg (Term t) = alg =<< mapM (cataM alg) t

-- cata :: (Functor f) => (f a -> a) -> Term f -> a
para :: (Functor f) => (f (a, Term f) -> a) -> Term f -> a
para alg (Term t) = alg $ fmap g $ t
  where
    g x = (para alg x, x)

paraM :: (Traversable t, Functor m, Monad m) => (t (a, Term t) -> m a) -> Term t -> m a
paraM alg (Term t) = alg =<< mapM g t
  where
    g x = (,x) <$> paraM alg x

free :: (Functor f) => (a -> b) -> (Alg f b) -> Ctx h f a -> b
free g alg (Term t) = alg $ fmap (free g alg) t
free g _   (Hole x) = g x

freeM :: (Traversable t, Monad m) => (a -> m b) -> (AlgM m t b) -> Ctx h t a -> m b
freeM g alg (Term t) = alg =<< mapM (freeM g alg) t
freeM g _   (Hole x) = g x

paraFree :: forall f h. (Functor f, Functor h) => (f (Term h, Term f) -> Context h (Term h)) -> Term f -> Term h
paraFree alg (Term t) = applyCtx $ alg $ fmap g $ t
  where
    g :: Term f -> (Term h, Term f)
    g x = (paraFree alg x, x)

paraFreeM :: forall f h m. (Traversable f, Traversable h, Functor m, Monad m) =>
             (f (Term h, Term f) -> m (Context h (Term h))) -> Term f -> m (Term h)
paraFreeM alg (Term t) = fmap applyCtx . alg =<< mapM g t
  where
    g :: Term f -> m (Term h, Term f)
    g x = (,x) <$> paraFreeM alg x

histo :: forall f a. (Functor f) =>
         (f (Term (f :&: a)) -> a) -> Term f -> a
histo alg = ann . unTerm . f
  where
    f :: Term f -> Term (f :&: a)
    -- f = cata (Term . uncurry (:&:) . (id &&& alg))
    f = cata (\x -> Term (x :&: alg x))

histoFutu :: forall f h. (Functor f, Functor h) =>
             (f (Term (f :&: Term h)) -> Context h (Term h)) -> Term f -> Term h
histoFutu alg = histo (applyCtx . alg)

histoM :: forall f m a. (Traversable f, Functor m, Monad m) =>
          (f (Term (f :&: a)) -> m a) -> Term f -> m a
histoM alg = fmap (ann . unTerm) . cataM g
  where
    g :: AlgM m f (Term (f :&: a))
    g f = do
      a <- alg f
      return $ Term $ f :&: a

histoFutuM :: forall f h m. (Traversable f, Functor h, Functor m, Monad m) =>
              (f (Term (f :&: Term h)) -> m (Context h (Term h))) -> Term f -> m (Term h)
histoFutuM alg = histoM (fmap applyCtx . alg)

-- histoFutu :: forall f h. (Functor f, Functor h) =>
--              (f (Term (f :&: (Term h))) -> Context h (Term h)) -> Term f -> Term h
-- histoFutu alg (Term t) = applyCtx $ alg $ fmap g $ t
--   where
--     g :: Term f -> Term (f :&: (Term h))
--     g t@(Term x) = y
--       where
--         y :: Term (f :&: (Term h))
--         y = Term $ fmap g x :&: histoFutu alg t


applyCtx :: (Functor f) => Context f (Ctx h f a) -> Ctx h f a
applyCtx = free id Term

type Alg f a = f a -> a
type AlgM m f a = f a -> m a
type TermHom f g = forall a . f a -> Context g a

-- For f :: TermHom f g
-- termHom f == free (applyCtx . f), but termHom has more general type
-- due to use of GADTs.
termHom :: (Functor f, Functor g) => TermHom f g -> Ctx h f a -> Ctx h g a
termHom f (Term t) = applyCtx $ f $ fmap (termHom f) t
termHom _ (Hole x) = Hole x

(<.>) :: (Functor f, Functor g, Functor h) => TermHom g h -> TermHom f g -> TermHom f h
(<.>) g f = termHom g . f

