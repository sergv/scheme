----------------------------------------------------------------------------
-- |
-- Module      :  MCEval
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

module MCEval where

import Control.Arrow
import Control.Applicative
import Control.Monad.Error hiding (mapM)
import Control.Monad.Reader hiding (mapM)
import Control.Monad.State hiding (mapM)
import qualified Data.IntMap as IM
import qualified Data.Map as M
import Data.Monoid
import Data.Text.Lazy (Text)
import Data.Traversable (mapM)
import Data.Vector (Vector)
import qualified Data.Vector as V

import Text.PrettyPrint.Leijen.Text (Pretty, Doc)
import qualified Text.PrettyPrint.Leijen.Text as PP

import ALaCarte
import Types
import Utils

import Prelude hiding (mapM)


newtype Err a = Err { runErr :: Either Text a } -- ErrorT Text Identity a
              deriving (Functor, Applicative, Monad, MonadError Text)


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


-- instance Error Text where
--   noMsg  = T.empty
--   strMsg = T.pack

-- class Depth f g where
--   depthAlg :: f (Term (g :&: Int)) -> Int
--
-- instance ({-f :<: g', g :<: g',-} Depth f g', Depth g g') => Depth (f :+: g) g' where
--   depthAlg (Inl x) = depthAlg x
--   depthAlg (Inr y) = depthAlg y
--
-- instance Depth List SchemeSexpF where
--   depthAlg (List h xs t) = 1 + (maximum $ map (\(_ :&: ann) -> ann) $ map unTerm $ h : t : xs)
--
-- instance Depth (K AInt) SchemeSexpF where
--   depthAlg _ = 1
-- instance Depth (K ADouble) SchemeSexpF where
--   depthAlg _ = 1
-- instance Depth (K AString) SchemeSexpF where
--   depthAlg _ = 1
-- instance Depth (K ABool) SchemeSexpF where
--   depthAlg _ = 1
-- instance Depth (K Nil) SchemeSexpF where
--   depthAlg _ = 1
-- instance Depth (K Symbol) SchemeSexpF where
--   depthAlg _ = 1
-- instance Depth Vect SchemeSexpF where
--   depthAlg _ = 1

-- Basically (Term g) goes to (Term h) which involves
-- histomorphism recursion and term homomorphisms in result.
-- Also conversion may fail, hence Err monad.
-- (f :<: g, f :<: h) =>
class GetProgram f h where
  -- getProgramAlg :: f (Term h, Term g) -> Err (Context h (Term h))
  getProgramAlg :: Position
                -> f (Term (SchemeSexpF :&: U Position :*: Term h))
                -> Err (Context h (Term h))

instance (GetProgram f h', GetProgram g h') => GetProgram (f :+: g) h' where
  getProgramAlg p (Inl x) = getProgramAlg p x
  getProgramAlg p (Inr y) = getProgramAlg p y

instance (K AInt :<: h) => GetProgram (K AInt) h where
  getProgramAlg _pos = return . symToSym . inject . K . unK
  -- getProgramAlg (K x@(AInt _))    = return . symToSym . inject $ K x
instance (K ADouble :<: h) => GetProgram (K ADouble) h where
  getProgramAlg _pos = return . symToSym . inject . K . unK
instance (K AString :<: h) => GetProgram (K AString) h where
  getProgramAlg _pos = return . symToSym . inject . K . unK
instance (K ABool :<: h) => GetProgram (K ABool) h where
  getProgramAlg _pos = return . symToSym . inject . K . unK
instance (K Nil :<: h) => GetProgram (K Nil) h where
  getProgramAlg _pos = return . symToSym . inject . K . unK
instance (K Symbol :<: h) => GetProgram (K Symbol) h where
  getProgramAlg _pos = return . symToSym . inject . K . unK

instance forall h. (ToConstraint SpecialFormF h) => GetProgram List h where
  getProgramAlg sexpPos sexp@(List (Term (hSexp :&: _ :^: hExpr))
                                   xs
                                   (isNilTerm -> True)) =
    case proj hSexp of
      Just (K (Symbol "lambda"))
        | not (V.null xs)
        , Term (argList :&: argListPos :^: _) <- V.head xs
        , body                                <- V.tail xs ->
          if | Just (List h' xs' (isNilTerm -> True)) <- proj argList -> do
               args <- parseArgs $ V.cons h' xs'
               return $ Term $ iLambda args $ mkBegin body
             | isNil argList ->
               return $ Term $ iLambda V.empty $ mkBegin body
             | otherwise     ->
               err argListPos "invalid argument list of lambda form" argList
        | otherwise ->
          errSexp "invalid lambda form"
      Just (K (Symbol "quote"))  ->
        case V.map (unTerm . stripA) xs of
          [x] -> return $ symToSym $ Term $ iQuote $ Term x
          _   -> errSexp "invalid quote form"
      Just (K (Symbol "set!"))   ->
        twoArgs iAssign "invalid set! form"
      Just (K (Symbol "define"))
        | not (V.null xs)
        , Term (argList :&: _ :^: _) <- V.head xs
        , body                       <- V.tail xs ->
          if | Just (K var@(Symbol _)) <- proj argList ->
               return $ Term $ iDefine var $ mkBegin body
             | Just (List (Term (h :&: _ :^: _)) args (isNilTerm -> True)) <- proj argList,
               Just (K funcName@(Symbol _)) <- proj h -> do
               args' <- parseArgs args
               return $
                 Term $ iDefine funcName $
                 Term $ iLambda args' $ mkBegin body
             | otherwise ->
               errSexp "invalid define form"
        | otherwise ->
          errSexp "invalid define form"
        -- twoArgs iDefine "invalid define form"
      Just (K (Symbol "if"))     ->
        threeArgs iIf "invalid if form"
      Just (K (Symbol "begin"))  ->
        return $ mkBegin xs
      Just (K (Symbol "let"))
        | not (V.null xs)
        , Term (bindings :&: _ :^: _) <- V.head xs
        , body                        <- V.tail xs ->
          if | Just (List h' xs' (isNilTerm -> True)) <- proj bindings -> do
               bindings' <- V.mapM destructLetBinding $ V.cons h' xs'
               let bindings'' = V.map (Hole *** Hole) bindings'
               return $ Term $ iLet bindings'' $ mkBegin body
             | isNil bindings ->
               return $ Term $ iLet V.empty $ mkBegin body
             | otherwise ->
               errSexp "invalid let form"
        | otherwise ->
          errSexp "invalid let form"
      Just (K (Symbol "cond"))  -> do
        clauses <- V.mapM destructCondClause xs
        return $ Term $ iCond clauses
      Just (K (Symbol "and"))   ->
        twoArgs iAnd "invalid and form"
      Just (K (Symbol "or"))    ->
        twoArgs iOr "invalid or form"
      Just (K (Symbol "not"))   ->
        singleArg iNot "invalid not form"
      _                         ->
        return $ symToSym $ Term $ iApply hExpr $ V.map (annLast . unTerm) xs
     where
       errSexp :: Text -> Err a
       errSexp msg = err sexpPos msg $ inj sexp
       err :: Position -> Text -> SchemeSexpF (Term (SchemeSexpF :&: p)) -> Err a
       err pos msg sexp =
         throwError $ showPos pos <> msg <> ": " <> showSexp (Term $ fmap stripA sexp)
       mkBegin :: Vector (Term (a :&: U Position :*: Term h)) -> Context h (Term h)
       mkBegin = symToSym . Term . iBegin . V.map (annLast . unTerm)
       parseArgs :: Vector (Term (SchemeSexpF :&: U Position :*: a)) -> Err (Vector Symbol)
       parseArgs = V.mapM (toSymbol "invalid function argument" . stripA)
       singleArg :: (Term h -> h (Term h))
                 -> Text
                 -> Err (Context h (Term h))
       singleArg cons msg =
         case V.map (annLast . unTerm) xs of
           [x] -> return $ symToSym $ Term $ cons x
           _   -> errSexp msg
       twoArgs :: (Term h -> Term h -> h (Term h))
               -> Text
               -> Err (Context h (Term h))
       twoArgs cons msg =
         case V.map (annLast . unTerm) xs of
           [x, y] -> return $ symToSym $ Term $ cons x y
           _      -> errSexp msg
       threeArgs :: (Term h -> Term h -> Term h -> h (Term h))
                 -> Text
                 -> Err (Context h (Term h))
       threeArgs cons msg =
         case V.map (annLast . unTerm) xs of
           [x, y, z] -> return $ symToSym $ Term $ cons x y z
           _         -> errSexp msg

       destructLetBinding :: Term (SchemeSexpF :&: U Position :*: Term h) -> Err (Term h, Term h)
       destructLetBinding (Term (binding :&: bindPos :^: _)) =
         case proj binding of
           Just (List (Term (origNameExpr :&: origNameExprPos :^: nameExpr))
                      [Term (_ :^: valExpr)]
                      (isNilTerm -> True)) -> do
             case proj origNameExpr of
               Just (K (Symbol _)) -> return (nameExpr, valExpr)
               _                   ->
                 err origNameExprPos "invalid bound variable name in let form" origNameExpr
           _                           ->
             err bindPos "invalid let form binding" binding
       destructCondClause :: Term (SchemeSexpF :&: U Position :*: Term h) ->
                             Err (Context h (Term h), Context h (Term h))
       destructCondClause (Term (clause :&: clausePos :^: _)) =
         case proj clause of
           Just (List (Term (_ :^: condition))
                      body
                      (isNilTerm -> True)) ->
             return (symToSym condition, mkBegin body)
           _                           ->
             err clausePos "invalid cond form clause" clause

       toSymbol :: (K Symbol :<: g, Pretty (Term g)) => Text -> Term g -> Err Symbol
       toSymbol errMsg t =
         case project t of
           Just (K sym@(Symbol _)) -> return sym
           _                       -> throwError $ errMsg <>
                                      ", symbol expected: " <> showSexp t
  getProgramAlg sexpPos x =
    throwError $ showPos sexpPos <> "cannot exctract program from " <>
    showSexp (inject $ fmap stripA x :: SchemeSexp)

instance (Vect :<: h) => GetProgram Vect h where
  getProgramAlg _ (Vect vs) =
    return . symToSym . Term . iVect $ V.map (annLast . unTerm) vs

getProgram :: Term (SchemeSexpF :&: U Position) -> Either Text SchemeExpr
getProgram = -- runIdentity . runErrorT .
             runErr . histoFutuMAnn getProgramAlg

-- Evaluator

data EvalState v = EvalState
  { evalStateMem       :: Memory v
  , evalStateFreshAddr :: Int
  , evalStateCurrFrame :: Frame
  }
  deriving (Show, Eq, Ord)

addNewObject :: Symbol -> v -> EvalState v -> EvalState v
addNewObject sym obj (EvalState {evalStateMem, evalStateFreshAddr, evalStateCurrFrame}) =
  EvalState evalStateMem' evalStateFreshAddr' evalStateCurrFrame'
  where
    addr                = Address evalStateFreshAddr
    evalStateMem'       = addToMemory addr obj evalStateMem
    evalStateFreshAddr' = evalStateFreshAddr + 1
    evalStateCurrFrame' = addToFrame sym addr evalStateCurrFrame

modifyObject :: Address -> v -> EvalState v -> EvalState v
modifyObject addr obj s =
  s { evalStateMem = addToMemory addr obj $ evalStateMem s }

newtype EvalM v a =
  EvalM (ReaderT Env (StateT (EvalState v) Err) a)
  deriving ( Functor
           , Applicative
           , Monad
           , MonadReader Env
           , MonadState (EvalState v)
           , MonadError Text
           )

-- withNewFrame :: EvalM v a -> EvalM v a
-- withNewFrame action = do
--   frame <- gets evalStateCurrFrame
--   modify (\s -> s { evalStateCurrFrame = Frame M.empty })
--   res <- local (addFrame frame) action
--   modify (\s -> s { evalStateCurrFrame = frame })
--   return res

inEnv :: Env -> EvalM v a -> EvalM v a
inEnv env action = do
  frame <- gets evalStateCurrFrame
  modify (\s -> s { evalStateCurrFrame = Frame M.empty })
  res <- local (const env) action
  modify (\s -> s { evalStateCurrFrame = frame })
  return res

runEvalM :: EvalM v a -> Either Text a
runEvalM (EvalM action) =
  runErr $ evalStateT (runReaderT action emptyEnv) emptyState
  where
    emptyState = EvalState (Memory IM.empty) 0 (Frame M.empty)
    emptyEnv   = Env V.empty

eval :: (Functor f, EvalProgram f f h) => Term (f :&: U Position) -> Either Text (Term h)
eval = runEvalM . termTransHistoAnnM' evalProgramAlg

class EvalProgram f g h where
  evalProgramAlg :: Position
                 -> TermTransAlgM
                      (EvalM (Term h))
                      f
                      (g :&: U Position :*: EvalM (Term h) (Term h))
                      h
  -- evalProgramAlg :: Position
  --                -> f (EvalM (Term h) (Term h), Term g)
  --                -> EvalM (Term h) (Term h)

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
      err = throwError $ showPos pos <> "unbound variable: " <> getSymbol sym
      err' = throwError $ showPos pos <> "bound variable absent in mem: " <> getSymbol sym

instance (Vect :<: h) => EvalProgram Vect g h where
  evalProgramAlg _ (Vect xs) =
    Term . iVect <$> V.mapM (annLast . unTerm) xs

instance (K (Closure (g :&: U Position)) :<: h, Functor g) => EvalProgram Lambda g h where
  evalProgramAlg _ (Lambda args body) = do
    currFrame <- gets evalStateCurrFrame
    env       <- ask
    return $ Term $ iClosure (addFrame currFrame env) args body'
    where
      body' :: Term (g :&: U Position)
      body' = stripOuterA body

instance (ToConstraint SchemeSexpF h) => EvalProgram (K Quote) g h where
  evalProgramAlg _ (K (Quote sexp)) = return $ retranslate sexp

instance (K Symbol :<: h, K Nil :<: h, Show (Term h)) => EvalProgram Assign g h where
  evalProgramAlg pos (Assign (Term (_ :^: var)) (Term (_ :^: val))) = do
    var' <- var
    val' <- val
    case project var' of
      Just (K sym@(Symbol _)) -> do
        addr <- lookupInEnvM sym
        case addr of
          Nothing -> do
            modify (addNewObject sym val')
          Just addr -> do
            modify (modifyObject addr val')
        return $ Term iNil
      _ -> throwError $ showPos pos <> " cannot assign to non-variable " <> show' var'

instance (K Nil :<: h) => EvalProgram Define g h where
  evalProgramAlg pos (Define sym (Term (_ :^: body))) = do
    addr <- lookupInEnvM sym
    case addr of
      Nothing -> do
        val <- body
        modify (addNewObject sym val)
        return $ Term iNil
      Just _ -> do
        throwError $ showPos pos <> " define cannot overwrite already set symbol " <> show' sym

instance (K ABool :<: h, K Nil :<: h) => EvalProgram If g h where
  evalProgramAlg _ (If (Term (_ :^: cond)) (Term (_ :^: true)) (Term (_ :^: false))) = do
    cond' <- cond
    if booleanValue cond'
      then true
      else false

instance (K Nil :<: h) => EvalProgram Begin g h where
  evalProgramAlg _ (Begin body) = do
    V.sequence_ $ V.init body'
    V.last body'
    where
      body' = V.map (annLast . unTerm) body

class Applicable f h where
  apply :: Position
        -> f (Term h)
        -> Vector (Term h)
        -> EvalM (Term h) (Term h)

instance (Functor g, EvalProgram g g h) =>
         Applicable (K (Closure (g :&: U Position))) h where
  apply :: Position
        -> K (Closure (g :&: U Position)) (Term h)
        -> Vector (Term h)
        -> EvalM (Term h) (Term h)
  apply pos (K (Closure env args body)) values = do
    inEnv env $ do
      populateFrame
      termTransHistoAnnM' evalProgramAlg body
    where
      populateFrame :: (MonadError Text m, MonadState (EvalState (Term h)) m) => m ()
      populateFrame
        | argCount == valCount = do
          state <- get
          let state' = V.foldr
                         (\(arg, val) state -> addNewObject arg val state)
                         state
                         (V.zip args values)
          put state'
        | otherwise                  =
          throwError msg
      msg = showPos pos <> "wrong number of arguments supplied for lambda: " <>
            "expected " <> show' argCount <> " but got " <> show' valCount
      argCount = V.length args
      valCount = V.length values

-- instance (Functor g, EvalProgram g g h) => Applicable Lambda (g :&: U Position) h where
--   apply pos (Lambda args body) values = do
--     withNewFrame $ do
--       populateFrame
--       paraAnn evalProgramAlg body
--     where
--       populateFrame :: (MonadError Text m, MonadState (EvalState (Term h)) m) => m ()
--       populateFrame
--         | argCount == valCount = do
--           state <- get
--           let state' = V.foldr
--                          (\(arg, val) state -> addNewObject arg val state)
--                          state
--                          (V.zip args values)
--           put state'
--         | otherwise                  =
--           throwError msg
--       msg = showPos pos <> "wrong number of arguments supplied for lambda: " <>
--             "expected " <> show' argCount <> " but got " <> show' valCount
--       argCount = V.length args
--       valCount = V.length values

instance (Applicable h h) => EvalProgram Apply g h where
  evalProgramAlg :: Position
                 -> TermTransAlgM
                      (EvalM (Term h))
                      Apply
                      (g :&: U Position :*: EvalM (Term h) (Term h))
                      h
  evalProgramAlg pos (Apply (Term (_ :^: func)) args) = do
    func' <- func
    args' <- V.mapM (annLast . unTerm) args
    apply pos (unTerm func') args'

booleanValue :: (K ABool :<: f, K Nil :<: f) => Term f -> Bool
booleanValue (Term x)
  | Just (K (ABool b)) <- proj x = b
  | Just (K Nil)       <- proj x = False
  | otherwise                    = True

instance (K ABool :<: h, K Nil :<: h) => EvalProgram And g h where
  evalProgramAlg _ (And (Term (_ :^: x)) (Term (_ :^: y))) = do
    x' <- x
    if booleanValue x'
    then do
      y' <- y
      return $ Term $ iABool $ booleanValue y'
    else return $ Term $ iABool False

instance (K ABool :<: h, K Nil :<: h) => EvalProgram Or g h where
  evalProgramAlg _ (Or (Term (_ :^: x)) (Term (_ :^: y))) = do
    x' <- x
    if booleanValue x'
    then return $ Term $ iABool True
    else do
      y' <- y
      return $ Term $ iABool $ booleanValue y'

instance (K ABool :<: h, K Nil :<: h) => EvalProgram Not g h where
  evalProgramAlg _ (Not (Term (_ :^: x))) = do
    x' <- x
    return $ Term $ iABool $ not $ booleanValue x'

-- main :: IO ()
-- main = do
--   print $ (runParser "test" parser "(foo)" :: SchemeSexp)

-- -- these things may come up dering evaluation
-- data SchemeDataF f = DAtom (AtomF f)
--                    | DSymbol Symbol
--                    | DList f [f] f
--                    | DLambda (Lambda f)
--                    | DPrimitive (Primitive f)
--                    deriving (Show, Eq, Ord, Functor, Foldable, Traversable)
--
-- type SchemeData = Fix SchemeDataF
--
--
-- -- Program data type
-- data SchemeExprF f = SelfEvaluating (AtomF f)
--                    | Variable Symbol
--                    | Quote SchemeSexp
--                    | Assign f f
--                    | Define f f
--                    | If f f f
--                    | LambdaProc (Lambda f)
--                    | PrimitiveProc (Primitive f)
--                    | Begin [f]
--                    | Cond [(f, f)]
--                    | Call f [f]
--                    | And f f
--                    | Or f f
--                    | Let [(f, f)] f
--                    deriving (Show, Eq, Ord, Functor, Foldable, Traversable)
--
-- type SchemeExpr = Fix SchemeExprF
--
-- -- readProgram :: forall m. (MonadError Text m) => SchemeSexp -> m SchemeExpr
-- -- readProgram = paraM alg
-- --   where
-- --     alg :: SchemeSexpF (SchemeExpr, SchemeSexp) -> m SchemeExpr
-- --     alg (SAtom atom)                                                     =
-- --       return $ Fix $ SelfEvaluating atom
-- --     alg (SSymbol sym)                                                    =
-- --       return $ Fix $ Variable sym
-- --     alg (SList (_, SSymbol (Symbol "quote")) [(_, Fix sexp)] (_, Fix (SAtom Nil))) =
-- --       return $ Fix $ Quote sexp
-- --     alg (SList (_, SSymbol (Symbol "quote")) _           _)              =
-- --       throwError $ "invalid quote expression: " <> showSexp
-- --     alg (SList (_, SSymbol (Symbol "set!")) [(_, _), (_, _)])            =
-- --       undefined
-- --
-- --     -- alg (SPair (Fix (Variable (Symbol "quote"))) y)  = Fix $ Quote y
-- --     -- alg (SPair (Fix (Variable (Symbol "lambda"))) y) = Fix $ LambdaProc $ Lambda undefined
-- --     -- alg (SPair (Fix (Variable (Symbol "set!"))) y)   = Fix $ Quote y
-- --     -- alg (SPair x y)                                  = Fix $ Call x $ pairsToList y
-- --
-- --     -- pairsToList :: SchemeExpr
-- --
