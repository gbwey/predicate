{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE LambdaCase #-}
module TestPred where
import Test.Tasty ( testGroup, TestTree )
import Test.Tasty.HUnit ( testCase, assertFailure )
import PredState
import Text.Show.Functions ()

suite :: TestTree
suite = testGroup "TestPred"
  [ testCase "peq.fail" $ expectLeft (runPred @() (peq 7) (8::Int))
  , testCase "peq.ok" $ expectRight (runPred @() (peq 7) (7::Int))
  , testCase "palg8.fail1 out of bounds" $ expectLeft (runPred @() alg8 0)
  , testCase "palg8.ok1" $ expectRight (runPred @() alg8 1)
  , testCase "palg8.ok2" $ expectRight (runPred @() alg8 2)
  , testCase "palg8.fail1 except 3" $ expectLeft (runPred @() alg8 3)
  , testCase "palg8.fail2 except 4" $ expectLeft (runPred @() alg8 4)
  , testCase "palg8.ok5" $ expectRight (runPred @() alg8 5)
  , testCase "palg8.fail3 except 6" $ expectLeft (runPred @() alg8 6)
  , testCase "palg8.ok7" $ expectRight (runPred @() alg8 7)
  , testCase "palg8.fail4 out of bounds" $ expectLeft (runPred @() alg8 8)
  , testCase "pexists_range.ok1" $ expectRight (runPred @() (PExists (PRange 4 6) `POr` PNull) ([]::[Int]))
  , testCase "pexists_range.ok2" $ expectRight (runPred @() (PExists (PRange 4 6) `POr` PNull) [3::Int ..7])
  , testCase "pexists_range.fail" $ expectLeft (runPred @() (PExists (PRange 4 6) `POr` PNull) ([7::Int ..10]++[1..3]))
  , testCase "pexists_range.ok3" $ expectRight (runPred @() (PExists (PRange 4 6) `POr` PNull) [6::Int ..9])
  , testCase "ppred_at_index.fail1" $ expectLeft (runPred @() (PIx 3 pfalse (peq 'z')) ("abcdef"::String))
  , testCase "ppred_at_index.fail2" $ expectLeft (runPred @() (PIx 3 pfalse (peq 'z')) (""::String))
  , testCase "ppred_at_index.ok1" $ expectRight (runPred @() (PIx 3 pfalse (peq 'z')) ("abcz"::String))
  , testCase "ppred_at_index.fail3" $ expectLeft (runPred @() (PIx 3 pfalse (peq 'z')) ("zzz_zzzz"::String))
  , testCase "pmixed.ok1" $ expectRight (runPred @() (pge 10 `PAnd` ple 20 `PXor` peq 10 `PAnd` plt 30) (11::Int))
  , testCase "pmixed.fail1" $ expectLeft (runPred @() (pge 10 `PAnd` ple 20 `PXor` peq 10 `PAnd` plt 30) (7::Int))
  , testCase "pnum.ok1" $ expectRight (runPred @() ((peq 20 + peq 22 + pgt 24) * (-peq 25) * (-peq 26)) (22::Int))
  , testCase "pnum.ok2" $ expectRight (runPred @() ((peq 20 + peq 22 + pgt 24) * (-peq 25) * (-peq 26)) (28::Int))
  , testCase "pnum.fail1" $ expectLeft (runPred @() ((peq 20 + peq 22 + pgt 24) * (-peq 25) * (-peq 26)) (25::Int))
  ]

alg1 :: Pred z Int
alg1 = pgt 10 `PAnd` pgt 20 `POr` peq 15

alg7 :: Pred z Int
alg7 = (peq 20 `POr` peq 24 `POr` peq 27) `PAnd` PNot (peq 25) `PAnd` PNot (peq 26)

alg8 :: Pred z Int
alg8 = (PRange 1 5 `POr` peq 7) `PAnd` PNot (peq 4 `POr` peq 3)

alg9 :: Pred z [Int]
alg9 = PLen (PRange 2 7)

alg10 :: Pred z Int
alg10 = PRange 2 7

expectLeft :: Show b => Either a b -> IO ()
expectLeft = \case
  Left _ -> pure ()
  Right e -> assertFailure $ "expected Left but found Right " ++ show e

expectRight :: Show a => Either a b -> IO ()
expectRight = \case
  Right _ -> pure ()
  Left e -> assertFailure $ "expected Right but found Left " ++ show e


