----------------------------------------------------------------------------
-- |
-- Module      :  Eval.Desugar
-- Copyright   :  (c) Sergey Vinokurov 2014
-- License     :  BSD3-style (see LICENSE)
--
-- Maintainer  :  serg.foo@gmail.com
-- Stability   :
-- Portability :
--
--
----------------------------------------------------------------------------

{-# LANGUAGE ConstraintKinds       #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE MultiWayIf            #-}
{-# LANGUAGE NamedFieldPuns        #-}
{-# LANGUAGE OverlappingInstances  #-}
{-# LANGUAGE OverloadedLists       #-}
{-# LANGUAGE OverloadedStrings     #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE TupleSections         #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE UndecidableInstances  #-}

{-# OPTIONS_GHC -fcontext-stack=100 #-}

module Eval.Desugar where

import qualified Data.Vector as V

import ALaCarte
import Types

-- Desugarer

desugar :: Term (SchemeExprF :&: U Position) -> Term (SchemeCoreExprF :&: U Position)
desugar = termHomAnn desugarAlg

class Desugar f h where
  desugarAlg :: TermHom f h

instance (Desugar f h, Desugar g h) => Desugar (f :+: g) h where
  desugarAlg (Inl f) = desugarAlg f
  desugarAlg (Inr g) = desugarAlg g

instance (f :<: h) => Desugar f h where
  desugarAlg f = inject $ fmap Hole f

instance (If :<: h, K Symbol :<: h, K Nil :<: h) => Desugar Cond h where
  desugarAlg (Cond cases elseClause) =
    V.foldr
      (\(test, body) ifFalse -> Term $ iIf (Hole test) (Hole body) ifFalse)
      (maybe (Term iNil) Hole elseClause)
      cases

