----------------------------------------------------------------------------
-- |
-- Module      :  Main
-- Copyright   :  (c) Sergey Vinokurov 2014
-- License     :  BSD3-style (see LICENSE)
--
-- Maintainer  :  serg.foo@gmail.com
-- Stability   :
-- Portability :
--
--
----------------------------------------------------------------------------

{-# LANGUAGE GADTs #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeOperators #-}

module Main where

import Data.Maybe (isJust)

import ALaCarte
import MCEval
import Test.Tasty
-- import Test.Tasty.SmallCheck as SC
-- import Test.Tasty.QuickCheck as QC
import Test.Tasty.HUnit

import Text.ParserCombinators.UU
import Text.ParserCombinators.UU.Utils


projectsTo :: forall f g. (f :<: g) => Term g -> f (Term g) -> Assertion
projectsTo t _ = assertBool "projectsTo failed" $
                 isJust $ (project t :: Maybe (f (Term g)))

tests :: TestTree
tests = testGroup "Tests" [parserTests]

parserTests :: TestTree
parserTests = testGroup "Parser tests"
  [ testCase "Parse integer" $
    runParser "test" parseTerm "1" @?= (inject (K $ AInt 1) :: SchemeSexp)
  , testCase "Parse double" $
    projectsTo (runParser "test" parseTerm "1.1" :: SchemeSexp) (K $ ADouble undefined)
  , testCase "Parse cons pair" $
    runParser "test" parseTerm "(foo . bar)" @?=
    (inject $ List (inject $ K $ Symbol "foo")
                   []
                   (inject $ K $ Symbol "bar")
                   :: SchemeSexp)
  , testCase "Parse sample sexp" $
    runParser "test" parseTerm "(1 #t \"foo\" . foo)" @?=
    (inject $ List (inject $ K $ AInt 1)
                   [ inject $ K $ ABool True
                   , inject $ K $ AString "foo"
                   ]
                   (inject $ K $ Symbol "foo")
                   :: SchemeSexp)
  , testCase "Parse empty sexp" $
    runParser "test" parseTerm "()" @?=
    (inject $ K Nil :: SchemeSexp)
  , testCase "Parse singleton int sexp" $
    runParser "test" parseTerm "(10)" @?=
    (inject $ List (inject $ K $ AInt 10)
                   []
                   nil :: SchemeSexp)
  , testCase "Parse sample vector" $
    runParser "test" parseTerm "#(1 2 #t)" @?=
    (inject $ Vector [ inject $ K $ AInt 1
                     , inject $ K $ AInt 2
                     , inject $ K $ ABool True
                     ]
                     :: SchemeSexp)
  ]

main :: IO ()
main = defaultMain tests

