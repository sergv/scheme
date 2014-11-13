----------------------------------------------------------------------------
-- |
-- Module      :  Eval.EvalM
-- Copyright   :  (c) Sergey Vinokurov 2014
-- License     :  BSD3-style (see LICENSE)
--
-- Maintainer  :  serg.foo@gmail.com
-- Stability   :
-- Portability :
--
--
----------------------------------------------------------------------------

{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE NamedFieldPuns             #-}

module Eval.EvalM where

import Control.Applicative
import Control.Monad.Error
import Control.Monad.Reader
import Control.Monad.State
import qualified Data.IntMap as IM
import qualified Data.Map as M
import Data.Text.Lazy (Text)
import qualified Data.Vector as V

import Types
import Utils

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

withNewFrame :: EvalM v a -> EvalM v a
withNewFrame action = do
  frame <- gets evalStateCurrFrame
  modify (\s -> s { evalStateCurrFrame = Frame M.empty })
  res <- local (addFrame frame) action
  modify (\s -> s { evalStateCurrFrame = frame })
  return res

inEnv :: Env -> EvalM v a -> EvalM v a
inEnv env action = do
  frame <- gets evalStateCurrFrame
  modify (\s -> s { evalStateCurrFrame = Frame M.empty })
  res <- local (const env) action
  modify (\s -> s { evalStateCurrFrame = frame })
  return res

runEvalM :: EvalM v a -> [(Symbol, v)] -> Either Text a
runEvalM (EvalM action) initBindings =
  runErr $ evalStateT (runReaderT action initEnv) emptyState
  where
    emptyState = EvalState (Memory mem) freeAddress (Frame M.empty)
    initEnv    = Env $ V.singleton $ Frame frame
    (freeAddress, frame, mem) =
      foldr
        (\(sym, val) (n, frame, mem) ->
           (n + 1 , M.insert sym (Address n) frame , IM.insert n val mem))
        (0, M.empty, IM.empty)
        initBindings

