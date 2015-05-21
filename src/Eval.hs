----------------------------------------------------------------------------
-- |
-- Module      :  Eval
-- Copyright   :  (c) Sergey Vinokurov 2014
-- License     :  BSD3-style (see LICENSE)
--
-- Maintainer  :  serg.foo@gmail.com
-- Stability   :
-- Portability :
--
--
----------------------------------------------------------------------------

{-# LANGUAGE ConstraintKinds            #-}
{-# LANGUAGE DeriveFoldable             #-}
{-# LANGUAGE DeriveFunctor              #-}
{-# LANGUAGE DeriveTraversable          #-}
{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE KindSignatures             #-}
{-# LANGUAGE GADTs                      #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses      #-}
{-# LANGUAGE MultiWayIf                 #-}
{-# LANGUAGE NamedFieldPuns             #-}
{-# LANGUAGE OverlappingInstances       #-}
{-# LANGUAGE OverloadedLists            #-}
{-# LANGUAGE OverloadedStrings          #-}
{-# LANGUAGE PatternGuards              #-}
{-# LANGUAGE RankNTypes                 #-}
{-# LANGUAGE StandaloneDeriving         #-}
{-# LANGUAGE ScopedTypeVariables        #-}
{-# LANGUAGE TemplateHaskell            #-}
{-# LANGUAGE TupleSections              #-}
{-# LANGUAGE TypeFamilies               #-}
{-# LANGUAGE TypeOperators              #-}
{-# LANGUAGE ViewPatterns               #-}
{-# LANGUAGE UndecidableInstances       #-}

{-# LANGUAGE InstanceSigs #-}

{-# OPTIONS_GHC -fcontext-stack=100 #-}

module Eval where

import Control.Applicative
import Control.Monad.Error hiding (mapM)
import Control.Monad.Reader hiding (mapM)
import Control.Monad.State hiding (mapM)
import Data.Maybe
import Data.Monoid
import Data.Text.Lazy (Text)
-- import Data.Traversable (mapM)
import Data.Vector (Vector)
import qualified Data.Vector as V

import ALaCarte
import Eval.EvalM
import Eval.ExtractProgram
import Eval.Desugar
import Eval.LispEqual
import Types
import Utils

import Prelude hiding (mapM)

-- instance Error Text where
--   noMsg  = T.empty
--   strMsg = T.pack

-- Evaluator

-- eval :: (Functor f, EvalProgram f f h) => Term (f :&: U Position) -> Either Text (Term h)
eval :: Term (SchemeCoreExprF :&: U Position) -> Either Text (SchemeVal (SchemeCoreExprF :&: U Position))
eval term = runEvalM (paraAnn evalProgramAlg term) initBindings
  where
    initBindings :: [(Symbol, SchemeVal (SchemeCoreExprF :&: U Position))]
    initBindings = [ (Symbol "+",     Term iPrimitiveAdd)
                   , (Symbol "-",     Term iPrimitiveSub)
                   , (Symbol "*",     Term iPrimitiveMul)
                   , (Symbol "/",     Term iPrimitiveDiv)
                   , (Symbol "eq?",   Term iPrimitiveEq)
                   , (Symbol "cons",  Term iPrimitiveCons)
                   , (Symbol "car",   Term iPrimitiveCar)
                   , (Symbol "cdr",   Term iPrimitiveCdr)
                   , (Symbol "null?", Term iPrimitiveIsNil)
                   ]

-- f - source type
-- g - type trick
-- h - output types
class EvalProgram f g h where
  evalProgramAlg :: Position
                 -> f (EvalM (Term h) (Term h), Term (g :&: U Position))
                 -> EvalM (Term h) (Term h)

instance (EvalProgram f g h, EvalProgram f' g h) => EvalProgram (f :+: f') g h where
  evalProgramAlg p (Inl x) = evalProgramAlg p x
  evalProgramAlg p (Inr y) = evalProgramAlg p y

instance (K Nil :<: h) => EvalProgram (K Nil) g h where
  evalProgramAlg _ (K Nil) =
    return $ Term iNil

instance (K ABool :<: h) => EvalProgram (K ABool) g h where
  evalProgramAlg _ (K (ABool x)) =
    return $ Term $ iABool x

instance (K AString :<: h) => EvalProgram (K AString) g h where
  evalProgramAlg _ (K (AString x)) =
    return $ Term $ iAString x

instance (K ADouble :<: h) => EvalProgram (K ADouble) g h where
  evalProgramAlg _ (K (ADouble x)) =
    return $ Term $ iADouble x

instance (K AInt :<: h) => EvalProgram (K AInt) g h where
  evalProgramAlg _ (K (AInt x)) =
    return $ Term $ iAInt x

lookupInEnvM :: (MonadReader Env m, MonadState (EvalState v) m, MonadError Text m)
             => Symbol
             -> m (Maybe Address)
lookupInEnvM sym = do
  currFrame <- gets evalStateCurrFrame
  env       <- ask
  return $ lookupInEnv sym currFrame env

instance EvalProgram (K Symbol) g h where
  evalProgramAlg pos (K sym) = do
    mem  <- gets evalStateMem
    addr <- maybe err return =<< lookupInEnvM sym
    maybe err' return $ lookupMem addr mem
    where
      err = errorAt pos $ "unbound variable: " <> getSymbol sym
      err' = errorAt pos $ "bound variable absent in mem: " <> getSymbol sym

instance (Vect :<: h) => EvalProgram Vect g h where
  evalProgramAlg _ (Vect xs) =
    Term . iVect <$> V.mapM fst xs

instance (Functor g, K (Closure (g :&: U Position)) :<: h) => EvalProgram Lambda g h where
  evalProgramAlg _ (Lambda args (_, body)) = do
    currFrame <- gets evalStateCurrFrame
    env       <- ask
    return $ Term $ iClosure (addFrame currFrame env) args body

instance (ToConstraint SchemeSexpF h) => EvalProgram (K Quote) g h where
  evalProgramAlg _ (K (Quote sexp)) = return $ retranslate sexp

instance (K Nil :<: h, Show (Term h)) => EvalProgram Assign g h where
  evalProgramAlg _ (Assign var (val, _)) = do
    val' <- val
    addr <- lookupInEnvM var
    case addr of
      Nothing -> do
        modify (addNewObject var val')
      Just addr -> do
        modify (modifyObject addr val')
    return $ Term iNil

instance (K Nil :<: h) => EvalProgram Define g h where
  evalProgramAlg pos (Define sym (body, _)) = do
    addr <- lookupInEnvM sym
    case addr of
      Nothing -> do
        val <- body
        modify (addNewObject sym val)
        return $ Term iNil
      Just _ -> do
        errorAt pos $ "define cannot overwrite already set symbol " <> show' sym

instance (K ABool :<: h, K Nil :<: h) => EvalProgram If g h where
  evalProgramAlg _ (If (cond, _) (true, _) (false, _)) = do
    cond' <- cond
    if booleanValue cond'
      then true
      else false

instance (K Nil :<: h) => EvalProgram Begin g h where
  evalProgramAlg _ (Begin body) = do
    V.sequence_ $ V.init body'
    V.last body'
    where
      body' = V.map fst body

instance (Callable h h) => EvalProgram Apply g h where
  evalProgramAlg pos (Apply (func, _) args) = do
    func' <- func
    args' <- V.mapM fst args
    apply pos (unTerm func') args'

instance EvalProgram Let g h where
  evalProgramAlg _ (Let bindings (body, _)) = do
    bindings' <- V.mapM (\(sym, (v, _)) -> (sym, ) <$> v) bindings
    withNewFrame $ do
      populateFrame bindings'
      body
    where
      populateFrame :: (MonadState (EvalState (Term h)) m) => Vector (Symbol, Term h) -> m ()
      populateFrame bindings =
        modify $ \state -> V.foldr (\(sym, v) -> addNewObject sym v) state bindings

booleanValue :: (K ABool :<: f, K Nil :<: f) => Term f -> Bool
booleanValue (Term x)
  | Just (K (ABool b)) <- proj x = b
  | Just (K Nil)       <- proj x = False
  | otherwise                    = True

instance (K ABool :<: h, K Nil :<: h) => EvalProgram And g h where
  evalProgramAlg _ (And (x, _) (y, _)) = do
    x' <- x
    if booleanValue x'
    then do
      y' <- y
      return $ Term $ iABool $ booleanValue y'
    else return $ Term $ iABool False

instance (K ABool :<: h, K Nil :<: h) => EvalProgram Or g h where
  evalProgramAlg _ (Or (x, _) (y, _)) = do
    x' <- x
    if booleanValue x'
    then return $ Term $ iABool True
    else do
      y' <- y
      return $ Term $ iABool $ booleanValue y'

instance (K ABool :<: h, K Nil :<: h) => EvalProgram Not g h where
  evalProgramAlg _ (Not (x, _)) = do
    x' <- x
    return $ Term $ iABool $ not $ booleanValue x'

-- class TransformSchemeVal f h where
--   transformSchemeVal :: (e -> e') -> f e (Term (h e)) -> Term (h e)
--
-- instance (TransformSchemeVal f h, TransformSchemeVal g h) => TransformSchemeVal (f e :+: g) h where
--   transformSchemeVal transform (Inl f) = transformSchemeVal transform f
--   transformSchemeVal transform (Inr g) = transformSchemeVal transform g
--
-- instance (f :<: h) => TransformSchemeVal f h where
--   transformSchemeVal _ f = inject f

class Callable f h where
  apply :: Position
        -> f (Term h)
        -> Vector (Term h)
        -> EvalM (Term h) (Term h)

instance (Callable f h, Callable g h) => Callable (f :+: g) h where
  apply p (Inl f) args = apply p f args
  apply p (Inr g) args = apply p g args

instance (Functor g, EvalProgram g g h) =>
         Callable (K (Closure (g :&: U Position))) h where
  apply pos (K (Closure env args body)) values = do
    inEnv env $ do
      populateFrame
      paraAnn evalProgramAlg body
    where
      populateFrame :: (MonadError Text m, MonadState (EvalState (Term h)) m) => m ()
      populateFrame
        | argCount == valCount = do
          modify $ \state ->
            V.foldr
              (\(arg, val) -> addNewObject arg val)
              state
              (V.zip args values)
        | otherwise                  =
          errorAt pos msg
      msg = "wrong number of arguments supplied for lambda: " <>
            "expected " <> show' argCount <> " but got " <> show' valCount
      argCount = V.length args
      valCount = V.length values

arith :: forall m h. (MonadError Text m, K AInt :<: h, K ADouble :<: h, Show (Term h))
      => Position
      -> (forall a. (Num a) => a -> a -> a)
      -- -> (forall a. (Num a) => a)
      -> Integer
      -> Double
      -> (Double -> Double -> Double)
      -> Vector (Term h)
      -> m (Term h)
arith pos f defInt defDbl combine args = do
  (ints, doubles, isInt) <- V.foldM add (defInt, defDbl, True) args
  if isInt
    then return $ Term $ iAInt ints
    else return $ Term $ iADouble $ combine (fromIntegral ints) doubles
  where
    add :: (MonadError Text m) => (Integer, Double, Bool) -> Term h -> m (Integer, Double, Bool)
    add (ints, doubles, isInt) v
      | Just (K (AInt n))    <- project v
      = return (f ints n, doubles,     isInt)
      | Just (K (ADouble x)) <- project v
      = return (ints,     f doubles x, False)
      | otherwise
      = errorAt pos $ "cannot add non-number " <> show' v

instance (K AInt :<: h, K ADouble :<: h, Show (Term h)) => Callable (K PrimitiveAdd) h where
  apply pos (K PrimitiveAdd) values = arith pos (+) 0 0 (+) values

instance (K AInt :<: h, K ADouble :<: h, Show (Term h)) => Callable (K PrimitiveSub) h where
  apply pos (K PrimitiveSub) values
    | V.null values =
      errorAt pos "cannot apply subtraction to zero arguments"
    | otherwise     = do
      (defInt, defDbl) <- mkDefs
      arith pos (-) defInt defDbl (+) (V.tail values)
    where
      v = V.head values
      mkDefs
        | Just (K (AInt n))    <- project v = return (n, 0)
        | Just (K (ADouble x)) <- project v = return (0, x)
        | otherwise                         =
          errorAt pos $ "invalid argument type for subtraction: " <> show' v

instance (K AInt :<: h, K ADouble :<: h, Show (Term h)) => Callable (K PrimitiveMul) h where
  apply pos (K PrimitiveMul) values = arith pos (*) 1 1 (*) values

instance (K AInt :<: h, K ADouble :<: h, Show (Term h)) => Callable (K PrimitiveDiv) h where
  apply pos (K PrimitiveDiv) [x, y] = do
    z <- (/) <$> x' <*> y'
    return $ Term $ iADouble z
    where
      x' | Just (K (AInt n))    <- project x = return $ fromIntegral n
         | Just (K (ADouble d)) <- project x = return d
         | otherwise                      =
           errorAt pos $ "invalid first argument to division: " <> show' x
      y' | Just (K (AInt n))    <- project y = return $ fromIntegral n
         | Just (K (ADouble d)) <- project y = return $ d
         | otherwise                      =
           errorAt pos $ "invalid second argument to division: " <> show' y
  apply pos (K PrimitiveDiv) args =
    errorAt pos $ "cannot apply division to arguments " <> show' args

instance (LispEqual h h, K ABool :<: h, Show (Term h)) => Callable (K PrimitiveEq) h where
  apply _ (K PrimitiveEq) [Term x, Term y] =
    return $ Term $ iABool $ lispEqual x y
  apply pos (K PrimitiveEq) args =
    errorAt pos $ "eq? requires two arguments, but got " <> show' args

instance (List :<: h, Show (Term h)) => Callable (K PrimitiveCons) h where
  apply _ (K PrimitiveCons) [x, y]
    | Just (List h body t) <- project y = return $ Term $ iList x (V.cons h body) t
    | otherwise                         = return $ Term $ iList x V.empty y
  apply pos (K PrimitiveCons) args =
    errorAt pos $ "cons requires two arguments, but got " <> show' args

instance (List :<: h, Show (Term h)) => Callable (K PrimitiveCar) h where
  apply pos (K PrimitiveCar) [x]
    | Just (List h _body _t) <- project x = return h
    | otherwise                           =
    errorAt pos $ "invalid argument type to car, expected list but got " <> show' x
  apply pos (K PrimitiveCar) args =
    errorAt pos $ "car requires one argument, but got " <> show' args

instance (List :<: h, Show (Term h)) => Callable (K PrimitiveCdr) h where
  apply pos (K PrimitiveCdr) [x]
    | Just (List _h body t) <- project x =
      case body of
        [] -> return t
        _  -> return $ Term $ iList (V.head body) (V.tail body) t
    | otherwise                          =
    errorAt pos $ "invalid argument type to cdr, expected cons pair but got " <> show' x
  apply pos (K PrimitiveCdr) args =
    errorAt pos $ "cdr requires one argument, but got " <> show' args

instance (K Nil :<: h, K ABool :<: h, Show (Term h)) => Callable (K PrimitiveIsNil) h where
  apply _ (K PrimitiveIsNil) [Term x]
    | Just (K Nil) <- proj x = return $ Term $ iABool True
    | otherwise              = return $ Term $ iABool False
  apply pos (K PrimitiveIsNil) args =
    errorAt pos $ "cannot apply null? to arguments " <> show' args

instance (Show (f (Term h)), Show (Term h)) => Callable f h where
  apply pos expr args =
    errorAt pos $ "cannot apply " <> show' expr <> " to args " <> show' args


evalPipeline :: Term (SchemeSexpF :&: U Position) -> Either Text (SchemeVal (SchemeCoreExprF :&: U Position))
evalPipeline = getProgram >=> eval . desugar

-- main :: IO ()
-- main = do
--   print $ (runParser "test" parser "(foo)" :: SchemeSexp)

