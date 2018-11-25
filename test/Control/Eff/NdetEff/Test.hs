{-# LANGUAGE FlexibleContexts, NoMonomorphismRestriction #-}
{-# LANGUAGE TypeOperators, DataKinds #-}
{-# LANGUAGE TemplateHaskell #-}

module Control.Eff.NdetEff.Test (testGroups, gen_testCA, gen_ifte_test) where

import Test.HUnit hiding (State)
import Control.Applicative
import Control.Eff
import Control.Eff.Lift
import Control.Eff.NdetEff
import Control.Eff.Writer.Strict
import Control.Monad (msum, guard, mzero, mplus)
import Utils

import Test.Framework.TH
import Test.Framework.Providers.HUnit

testGroups = [ $(testGroupGenerator) ]

-- TODO: add quickcheck test to test conformance of different
-- implementations of 'makeChoiceA' and 'msplit'.

-- TODO: add benchmarks for different implementations of 'makeChoiceA'
-- and 'msplit'.

gen_testCA :: (Integral a) => a -> Eff (NdetEff ': r) a
gen_testCA x = do
  i <- msum . fmap return $ [1..x]
  guard (i `mod` 2 == 0)
  return i

case_NdetEff_testCA :: Assertion
case_NdetEff_testCA = [2, 4..10] @=? (run $ makeChoiceA (gen_testCA 10))

gen_ifte_test x = do
  n <- gen x
  ifte (do
           d <- gen x
           guard $ d < n && n `mod` d == 0
           -- _ <- trace ("d: " ++ show d) (return ())
       )
    (\_ -> mzero)
    (return n)
    where gen x = msum . fmap return $ [2..x]


case_NdetEff_ifte :: Assertion
case_NdetEff_ifte =
  let primes = ifte_test_run
  in
    assertEqual "NdetEff: test ifte using primes"
    [2,3,5,7,11,13,17,19,23,29] primes
  where
    ifte_test_run :: [Int]
    ifte_test_run = run . makeChoiceA $ (gen_ifte_test 30)


-- called reflect in the LogicT paper
case_NdetEff_reflect :: Assertion
case_NdetEff_reflect =
  let tsplitr10 = run $ runListWriter $ makeChoiceA tsplit
      tsplitr11 = run $ runListWriter $ makeChoiceA (msplit tsplit >>= reflect)
      tsplitr20 = run $ makeChoiceA $ runListWriter tsplit
      tsplitr21 = run $ makeChoiceA $ runListWriter (msplit tsplit >>= reflect)
  in
    assertEqual "tsplitr10" expected1 tsplitr10
    >> assertEqual "tsplitr11" expected1 tsplitr11
    >> assertEqual "tsplitr20" expected2 tsplitr20
    >> assertEqual "tsplitr21" expected21 tsplitr21
  where
    expected1 = ([1, 2],["begin", "end"])
    expected2 = [(1, ["begin"]), (2, ["end"])]
    expected21 = [(1, ["begin"]), (2, ["begin", "end"])]

    tsplit =
      (tell "begin" >> return 1) `mplus`
      (tell "end"   >> return 2)

case_NdetEff_monadBaseControl :: Assertion
case_NdetEff_monadBaseControl = runLift (makeChoiceA $ doThing (return 1 <|> return 2)) @=? Just [1,2]
