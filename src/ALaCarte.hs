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

{-# LANGUAGE ConstraintKinds        #-}
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
{-# LANGUAGE TypeFamilies           #-}
{-# LANGUAGE TupleSections          #-}
{-# LANGUAGE TypeOperators          #-}
{-# LANGUAGE UndecidableInstances   #-}

module ALaCarte where

import Control.Applicative
import Control.Arrow
import Control.Monad hiding (mapM, sequence)
import Data.Foldable (Foldable)
import Data.Monoid
import Data.Traversable (Traversable, mapM)
import Data.Void
import Prelude hiding (mapM, sequence)

import qualified Data.Foldable as F
import qualified Data.Traversable as Tr


data (:+:) f g ix = Inl (f ix)
                  | Inr (g ix)
                  deriving (Eq, Ord, Functor, Foldable, Traversable)

instance (Show (f ix), Show (g ix)) => Show ((f :+: g) ix) where
  showsPrec n (Inl f) = showsPrec n f
  showsPrec n (Inr g) = showsPrec n g
  -- show (Inl f) = show f
  -- show (Inr g) = show g

infixr 6 :+:

type family Concat xs ys where
  Concat (x :+: xs) ys = x :+: Concat xs ys
  Concat x          ys = x :+: ys

type family ToConstraint xs h where
  ToConstraint (x :+: xs) h = (x :<: h, ToConstraint xs h)
  ToConstraint x          h = x :<: h

-- inductive tuples
data a :*: b = a :*: b
             deriving (Show, Eq, Ord)

infixl 6 :*:

-- one-unit tuple
newtype U a = U { getU :: a }
            deriving (Show, Eq, Ord)

data (f :&: annIx) ix where
  (:&:) :: f ix -> a -> (f :&: (U a)) ix
  (:^:) :: (f :&: annIx) ix -> a -> (f :&: (annIx :*: a)) ix

instance (Functor f) => Functor (f :&: annIx) where
  fmap g (f  :&: a) = fmap g f :&: a
  fmap g (af :^: a) = fmap g af :^: a

instance (Foldable f) => Foldable (f :&: annIx) where
  -- foldMap :: Monoid m => (a -> m) -> t a -> m
  foldMap g (f  :&: _) = F.foldMap g f
  foldMap g (af :^: _) = F.foldMap g af

instance (Traversable f) => Traversable (f :&: annIx) where
  -- traverse :: Applicative f => (a -> f b) -> t a -> f (t b)
  traverse g (f  :&: a) = (:&: a) <$> Tr.traverse g f
  traverse g (af :^: a) = (:^: a) <$> Tr.traverse g af

instance (Show (f ix), Show (ClearU annIx)) => Show ((f :&: annIx) ix) where
  showsPrec n f = showParen (n == 11) $
    \xs -> showsPrec 11 (remA f) $ " :&: " ++ showsPrec 11 (ann f) xs

  -- showsPrec n (f :&: a) = showParen (n == 11) $
  --   \xs -> showsPrec 11 f $ " :&: " ++ showsPrec 11 (U a) xs
  -- showsPrec n (af :^: a) = showParen (n == 11) $
  --   \xs -> showsPrec 11 af $ " :^: " ++ showsPrec 11 a xs

instance (Eq (f ix), Eq (ClearU annIx)) => Eq ((f :&: annIx) ix) where
  f == g = remA f == remA g && ann f == ann g

instance (Ord (f ix), Ord (ClearU annIx)) => Ord ((f :&: annIx) ix) where
  f `compare` g = (remA f `compare` remA g) <> (ann f `compare` ann g)

infixl 5 :&:
infixl 4 :^:

type family ClearU a where
  ClearU (U a)      = a
  ClearU (af :*: a) = ClearU af :*: a

type family AddU a where
  AddU (af :*: a) = AddU af :*: a
  AddU a          = U a

-- annU :: (f :&: p) ix -> ClearU p
-- annU (_    :&: a) = a
-- annU (rest :^: a) = annU rest :*: a

onCarrier :: (f ix -> g ix') -> (f :&: p) ix -> (g :&: p) ix'
onCarrier h (f    :&: a) = h f :&: a
onCarrier h (rest :^: a) = onCarrier h rest :^: a

splitAnn :: (f :&: p) ix -> (f ix, p)
splitAnn (f    :&: a) = (f, U a)
splitAnn (rest :^: a) = second (:*: a) $ splitAnn rest

ann' :: (f :&: p) ix -> p
ann' (_    :&: a) = U a
ann' (rest :^: a) = ann' rest :*: a

ann :: (f :&: p) ix -> ClearU p
ann (_    :&: a) = a
ann (rest :^: a) = ann rest :*: a

type family AnnLast a where
  AnnLast (U a) = a
  AnnLast (af :*: a) = a

annLast :: (f :&: p) ix -> AnnLast p
annLast (_ :&: a) = a
annLast (_ :^: a) = a

remA :: (f :&: p) ix -> f ix
remA (f :&: _) = f
remA (f :^: _) = remA f

stripA :: (Functor f) => Term (f :&: p) -> Term f
stripA = cata (Term . remA)

remOuterA :: (f :&: p :*: p') ix -> (f :&: p) ix
remOuterA (f :^: _) = f

stripOuterA :: (Functor f) => Term (f :&: p :*: p') -> Term (f :&: p)
stripOuterA = cata (Term . remOuterA)


class AddAnn p where
  addAnn :: p -> f ix -> (f :&: p) ix

instance (AddAnn a) => AddAnn (a :*: b) where
  addAnn (a :*: b) f = addAnn a f :^: b

instance AddAnn (U p) where
  addAnn (U p) f = f :&: p

annotate :: (Functor f, AddAnn p) => p -> Cxt h f a -> Cxt h (f :&: p) a
annotate p (Term e) = Term $ addAnn p $ fmap (annotate p) e
annotate _ (Hole x) = Hole x

-- data (:&:) f p ix = f ix :&: p
--                   deriving (Eq, Ord, Show, Functor, Foldable, Traversable)
--
-- infixl 6 :&:
--
-- ann :: (f :&: p) ix -> p
-- ann (_ :&: p) = p
--
-- remA :: Ann (f ix) p -> f ix
-- remA (f :&: _) = f
--
-- stripA :: (Functor f) => Term (f :&: p) -> Term f
-- stripA = cata (Term . remA)



-- data AnnotHelper f where
--   NoAnnot   :: f ix -> AnnotHelper (f ix)
--   Annotated :: p -> AnnotHelper (f ix) -> AnnotHelper ((f :&: p) ix)
--
-- class BuildAnnotHelper a where
--   mkAnnotHelper :: a -> AnnotHelper a
--
-- instance BuildAnnotHelper (f ix) where
--   mkAnnotHelper f = NoAnnot f
--
-- instance (BuildAnnotHelper (f ix)) => BuildAnnotHelper ((f :&: p) ix) where
--   mkAnnotHelper (f :&: p) = Annotated p $ mkAnnotHelper f
--
-- stripA :: (BuildAnnotHelper (f ix)) ->


-- class StripAnnotations f g where
--   strip :: f ix -> g ix
--
-- instance StripAnnotations f f where
--   strip x = x
--
-- instance (StripAnnotations f g) => StripAnnotations (f :&: p) g where
--   strip (f :&: _) = strip f
--
-- stripA :: (Functor f, StripAnnotations f g) => Term f -> Term g
-- stripA = cata (Term . strip)



-- instance (Functor f, Functor g) => Functor (f :+: g) where
--   fmap h (Inl f) = Inl $ fmap h f
--   fmap h (Inr g) = Inr $ fmap h g

class (Functor f, Functor g) => f :<: g where
  inj  :: f a -> g a
  proj :: g a -> Maybe (f a)

instance (Functor f) => f :<: f where
  inj  = id
  proj = Just

instance (Functor f, Functor g) => f :<: (f :+: g) where
  inj = Inl
  proj (Inl x) = Just x
  proj _       = Nothing

instance (Functor f, Functor g, Functor h, f :<: g) => f :<: (h :+: g) where
  inj = Inr . inj
  proj (Inr x) = proj x
  proj _       = Nothing

newtype K a b = K { unK :: a }
              deriving (Eq, Ord, Functor, Foldable, Traversable)

instance (Show a) => Show (K a b) where
  showsPrec n (K a) = showParen (n == 11) $ \xs -> "K " ++ showsPrec 11 a xs

data Hole
data NoHole

data Cxt :: * -> (* -> *) -> * -> * where
  Term :: f (Cxt h f a) -> Cxt h f a
  Hole :: a -> Cxt Hole f a

-- deriving instance (Show (f (Cxt h f a)), Show a) => Show (Cxt h f a)
instance (Show (f (Cxt h f a)), Show a) => Show (Cxt h f a) where
  showsPrec n (Term t) = showParen (n == 11) $ \xs -> "Term " ++ showsPrec 11 t xs
  showsPrec n (Hole x) = showParen (n == 11) $ \xs -> "Hole " ++ showsPrec 11 x xs

deriving instance (Eq (f (Cxt h f a)), Eq a) => Eq (Cxt h f a)
deriving instance (Ord (f (Cxt h f a)), Ord a) => Ord (Cxt h f a)

type Term f = Cxt NoHole f Void
type Context f a = Cxt Hole f a

-- Symbol to symbol term homomorphism transformation
symToSym :: (Functor f) => Term f -> Context f (Term f)
symToSym (Term t) = Term $ fmap Hole t

-- Lax version of symToSym mainly for convenience.
symToSym' :: (Functor f) => f a -> Context f a
symToSym' = Term . fmap Hole

inject :: (f :<: g) => f (Cxt h g a) -> Cxt h g a
inject = Term . inj

project :: (f :<: g) => Cxt h g a -> Maybe (f (Cxt h g a))
project (Term t) = proj t
project (Hole _) = Nothing

unTerm :: Term f -> f (Term f)
unTerm (Term t) = t

-- unTerm :: Cxt h f a -> f (Cxt h f a)
-- unTerm (Term t) = t
-- unTerm (Hole _) = error "error: unTerm applied to Hole"

unTermSafe :: Cxt h f a -> Maybe (f (Cxt h f a))
unTermSafe (Term t) = Just t
unTermSafe (Hole _) = Nothing

cata :: (Functor f) => Alg f a -> Term f -> a
cata alg (Term t) = alg $ fmap (cata alg) t

cataM :: (Traversable t, Monad m) => AlgM m t a -> Term t -> m a
cataM alg (Term t) = alg =<< mapM (cataM alg) t

cataAnn :: (Functor f) => AlgAnn (ClearU p) f a -> Term (f :&: p) -> a
cataAnn alg = cata (\(f :&: p) -> alg p f)

cataAnnM :: (Functor f, Traversable f, Monad m)
         => AlgAnnM m (ClearU p) f a
         -> Term (f :&: p)
         -> m a
cataAnnM alg = cataM (\(f :&: p) -> alg p f)

ana :: (Functor f) => Coalg f a -> a -> Term f
ana coalg = Term . fmap (ana coalg) . coalg

futu :: (Functor f) => (a -> Context f a) -> a -> Term f
futu coalg = free (futu coalg) Term . coalg

futuM :: (Functor f, Traversable f, Monad m)
      => (a -> m (Context f a))
      -> a
      -> m (Term f)
futuM coalg = freeM (futuM coalg) (return . Term) <=< coalg

-- futuM :: (Functor f, Traversable f, Monad m)
--       => (a -> m (Context f a))
--       -> a
--       -> m (Term f)
-- futuM coalg = freeM (futuM coalg) (return . Term) <=< coalg

-- cata :: (Functor f) => (f a -> a) -> Term f -> a
para :: (Functor f) => (f (a, Term f) -> a) -> Term f -> a
para alg (Term t) = alg $ fmap g $ t
  where
    g x = (para alg x, x)

paraAnn :: (Functor f) => (ClearU p -> f (a, Term (f :&: p)) -> a) -> Term (f :&: p) -> a
paraAnn alg = para (\(f :&: p) -> alg p f)

paraM :: (Traversable t, Functor m, Monad m) => (t (a, Term t) -> m a) -> Term t -> m a
paraM alg (Term t) = alg =<< mapM g t
  where
    g x = (,x) <$> paraM alg x

free :: (Functor f) => (a -> b) -> Alg f b -> Cxt h f a -> b
free g alg (Term t) = alg $ fmap (free g alg) t
free g _   (Hole x) = g x

freeM :: (Traversable t, Monad m) => (a -> m b) -> AlgM m t b -> Cxt h t a -> m b
freeM g alg (Term t) = alg =<< mapM (freeM g alg) t
freeM g _   (Hole x) = g x

paraFutu :: forall f h. (Functor f, Functor h)
         => (f (Term h, Term f) -> Context h (Term h))
         -> Term f
         -> Term h
paraFutu alg (Term t) = applyCxt $ alg $ fmap g $ t
  where
    g :: Term f -> (Term h, Term f)
    g x = (paraFutu alg x, x)

paraFutuM :: forall f h m. (Traversable f, Traversable h, Functor m, Monad m)
          => (f (Term h, Term f)
          -> m (Context h (Term h)))
          -> Term f
          -> m (Term h)
paraFutuM alg (Term t) = fmap applyCxt . alg =<< mapM g t
  where
    g :: Term f -> m (Term h, Term f)
    g x = (,x) <$> paraFutuM alg x

histo :: forall f a. (Functor f) =>
         (f (Term (f :&: U a)) -> a) -> Term f -> a
histo alg = ann . unTerm . f
  where
    f :: Term f -> Term (f :&: U a)
    -- f = cata (Term . uncurry (:&:) . (id &&& alg))
    f = cata (\x -> Term (x :&: alg x))

histoFutu :: forall f h. (Functor f, Functor h) =>
             (f (Term (f :&: U (Term h))) -> Context h (Term h)) -> Term f -> Term h
histoFutu alg = histo (applyCxt . alg)

histoM :: forall f m a. (Traversable f, Functor m, Monad m) =>
          (f (Term (f :&: U a)) -> m a) -> Term f -> m a
histoM alg = fmap (ann . unTerm) . cataM g
  where
    g :: AlgM m f (Term (f :&: U a))
    g f = do
      a <- alg f
      return $ Term $ f :&: a

histoFutuM :: forall f h m. (Traversable f, Functor h, Functor m, Monad m)
           => (f (Term (f :&: U (Term h))) -> m (Context h (Term h)))
           -> Term f
           -> m (Term h)
histoFutuM alg = histoM (fmap applyCxt . alg)

histoMAnn :: forall f m p a. (Traversable f, Functor m, Monad m)
          => (p -> f (Term (f :&: U p :*: a)) -> m a)
          -> Term (f :&: U p)
          -> m a
histoMAnn alg = fmap (annLast . unTerm) . cataM g
  where
    g :: AlgM m (f :&: U p) (Term (f :&: U p :*: a))
    g fp@(f :&: p) = do
      a <- alg p f
      return $ Term $ fp :^: a

-- Automatically carries annotations through so algebra does not has to worry
-- about it.
histoFutuMAnn :: forall f h m p. (Traversable f, Functor h, Functor m, Monad m)
              => (p -> f (Term (f :&: U p :*: Term (h :&: U p))) -> m (Context h (Term (h :&: U p))))
              -> Term (f :&: U p)
              -> m (Term (h :&: U p))
histoFutuMAnn alg = histoMAnn (\p f -> applyCxt . annotate (U p) <$> alg p f)


-- liftToAnn :: ((f a -> b) -> Term f -> m b) -> (f )


-- histoFutu :: forall f h. (Functor f, Functor h) =>
--              (f (Term (f :&: (Term h))) -> Context h (Term h)) -> Term f -> Term h
-- histoFutu alg (Term t) = applyCxt $ alg $ fmap g $ t
--   where
--     g :: Term f -> Term (f :&: (Term h))
--     g t@(Term x) = y
--       where
--         y :: Term (f :&: (Term h))
--         y = Term $ fmap g x :&: histoFutu alg t


applyCxt :: (Functor f) => Context f (Cxt h f a) -> Cxt h f a
applyCxt = free id Term

type Alg f a = f a -> a
type AlgAnn p f a = p -> f a -> a
type AlgM m f a = f a -> m a
type AlgAnnM m p f a = p -> f a -> m a
type TermHom f g = forall a . f a -> Context g a
type TermHomM m f g = forall a . f a -> m (Context g a)
type Coalg f a = a -> f a

-- For f :: TermHom f g
-- termHom f == free (applyCxt . f), but termHom has more general type
-- due to use of GADTs.
termHom :: (Functor f, Functor g) => TermHom f g -> Cxt h f a -> Cxt h g a
termHom f (Term t) = applyCxt $ f $ fmap (termHom f) t
termHom _ (Hole x) = Hole x

termHomAnn :: forall f g h p a. (Functor f, Functor g, AddAnn p)
           => TermHom f g
           -> Cxt h (f :&: p) a
           -> Cxt h (g :&: p) a
termHomAnn f (Term t) = applyCxt $ annotate p $ f $ fmap (termHomAnn f) t'
  where
    t' :: f (Cxt h (f :&: p) a)
    p  :: p
    (t', p) = splitAnn t
termHomAnn _ (Hole x) = Hole x

termHomM :: (Functor f, Traversable f, Functor g, Monad m) => TermHomM m f g -> Cxt h f a -> m (Cxt h g a)
termHomM f (Term t) = liftM applyCxt $ f =<< mapM (termHomM f) t
termHomM _ (Hole x) = return $ Hole x

-- -- Term homomorphisms that can inspect immediate results of children
-- -- - less general than the histomorphism where algebra can inspect
-- -- children at any level.
-- type TermHom' f g = forall a . f (g a) -> Context g a
--
-- -- For f :: TermHom f g
-- -- termHom f == free (applyCxt . f), but termHom has more general type
-- -- due to use of GADTs.
-- termHom' :: forall f g h a. (Functor f, Functor g) => TermHom' f g -> Cxt h f (g a) -> Cxt h g a
-- -- termHom' f (Term t) = applyCxt $ f $ fmap (termHom' f) t
-- termHom' f (Term t) = applyCxt $ f $ fmap (termHom' f) t
--   case fmap getHole t of
--     Just t' -> undefined
--     Nothing -> fmap (termHom' f) t
-- termHom' _ (Hole x) = Term $ fmap Hole x
--
-- getHole :: Cxt h g a -> Maybe a
-- getHole (Term _) = Nothing
-- getHole (Hole x) = Just x

type TermTransAlg f g h = f (Term g) -> Term h
type TermTransAlgM m f g h = f (Term g) -> m (Term h)

termTransHistoAnn :: forall f h p. (Functor f)
                  => (p -> TermTransAlg f (f :&: U p :*: Term h) h) -- f (Term (f :&: U p :*: Term h)) -> Term h)
                  -> Term (f :&: U p)
                  -> Term h
termTransHistoAnn alg = annLast . unTerm . cataAnn alg'
  where
    alg' :: p -> f (Term (f :&: U p :*: Term h)) -> Term (f :&: U p :*: Term h)
    alg' p f = Term $ f :&: p :^: alg p f

-- | Does not do automatial sequencing of monadic actions so it's not
-- the etalon termTransHistoAnnM.
termTransHistoAnnM' :: forall f m h p. (Functor f, Monad m)
                    => (p -> TermTransAlgM m f (f :&: U p :*: m (Term h)) h) -- f (Term (f :&: U p :*: Term h)) -> Term h)
                    -> Term (f :&: U p)
                    -> m (Term h)
termTransHistoAnnM' alg = annLast . unTerm . cataAnn alg'
  where
    alg' :: p -> f (Term (f :&: U p :*: m (Term h))) -> Term (f :&: U p :*: m (Term h))
    alg' p f = Term $ f :&: p :^: alg p f

-- alg . fmap (cata alg) . unTerm

-- termHomAnn :: (Functor f, Functor g)
--            => (ClearU p -> TermHom f g)
--            -> Cxt h (f :&: p) a
--            -> Cxt h (g :&: p) a
-- termHomAnn f (Term (t :&: p)) = applyCxt $ free Hole (Term . (:&: p)) $ f p $ fmap (termHomAnn f) t
-- termHomAnn _ (Hole x)         = Hole x

-- termHomAnnM :: (Functor f, Traversable f, Functor g, Traversable g, Monad m)
--             => (ClearU p -> TermHomM m f g)
--             -> Cxt h (f :&: p) a
--             -> m (Cxt h (g :&: p) a)
-- termHomAnnM f (Term (t :&: p)) =
--   liftM applyCxt $
--   freeM (return . Hole) (return . Term . (:&: p)) =<< f p =<< mapM (termHomAnnM f) t
-- termHomAnnM _ (Hole x)         = return $ Hole x

-- term homomorphism composition
(<.>) :: (Functor f, Functor g, Functor h) => TermHom g h -> TermHom f g -> TermHom f h
(<.>) g f = termHom g . f

--- Translate from one sum type into another.

class Translate f g where
  translateAlg :: f (Term g) -> Term g

instance (f :<: h, Translate g h) => Translate (f :+: g) h where
  translateAlg (Inl x) = translateAlg x
  translateAlg (Inr y) = translateAlg y

instance (f :<: g) => Translate f g where
  translateAlg = inject

retranslate :: (Translate f g, Functor f) => Term f -> Term g
retranslate = cata translateAlg

