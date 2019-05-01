{-# OPTIONS -Wall #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE OverloadedStrings #-}
module Main where
import Control.Monad
import EasyTest
import PredState

main :: IO ()
main = run suite

suite :: Test ()
suite = tests
  [ scope "peq.fail" $ void $ expectLeft (runPred @() (peq 7) (8::Int))
  , scope "peq.ok" $ void $ expectRight (runPred @() (peq 7) (7::Int))
  , scope "palg8.fail1 out of bounds" $ void $ expectLeft (runPred @() alg8 0)
  , scope "palg8.ok1" $ void $ expectRight (runPred @() alg8 1)
  , scope "palg8.ok2" $ void $ expectRight (runPred @() alg8 2)
  , scope "palg8.fail except 3" $ void $ expectLeft (runPred @() alg8 3)
  , scope "palg8.fail except 4" $ void $ expectLeft (runPred @() alg8 4)
  , scope "palg8.ok5" $ void $ expectRight (runPred @() alg8 5)
  , scope "palg8.fail except 6" $ void $ expectLeft (runPred @() alg8 6)
  , scope "palg8.ok7" $ void $ expectRight (runPred @() alg8 7)
  , scope "palg8.fail2 out of bounds" $ void $ expectLeft (runPred @() alg8 8)
  , scope "pexists_range.ok1" $ void $ expectRight (runPred @() (PExists (PRange 4 6) `POr` PNull) ([]::[Int]))
  , scope "pexists_range.ok2" $ void $ expectRight (runPred @() (PExists (PRange 4 6) `POr` PNull) [3::Int ..7])
  , scope "pexists_range.fail" $ void $ expectLeft (runPred @() (PExists (PRange 4 6) `POr` PNull) ([7::Int ..10]++[1..3]))
  , scope "pexists_range.ok3" $ void $ expectRight (runPred @() (PExists (PRange 4 6) `POr` PNull) [6::Int ..9])
  , scope "ppred_at_index.fail1" $ void $ expectLeft (runPred @() (PIx 3 pfalse (peq 'z')) ("abcdef"::String))
  , scope "ppred_at_index.fail2" $ void $ expectLeft (runPred @() (PIx 3 pfalse (peq 'z')) (""::String))
  , scope "ppred_at_index.ok1" $ void $ expectRight (runPred @() (PIx 3 pfalse (peq 'z')) ("abcz"::String))
  , scope "ppred_at_index.fail3" $ void $ expectLeft (runPred @() (PIx 3 pfalse (peq 'z')) ("zzz_zzzz"::String))
  , scope "pmixed.ok1" $ void $ expectRight (runPred @() (pge 10 `PAnd` ple 20 `PXor` peq 10 `PAnd` plt 30) (11::Int))
  , scope "pmixed.fail1" $ void $ expectLeft (runPred @() (pge 10 `PAnd` ple 20 `PXor` peq 10 `PAnd` plt 30) (7::Int))
  , scope "pnum.ok1" $ void $ expectRight (runPred @() ((peq 20 + peq 22 + pgt 24) * (-peq 25) * (-peq 26)) (22::Int))
  , scope "pnum.ok2" $ void $ expectRight (runPred @() ((peq 20 + peq 22 + pgt 24) * (-peq 25) * (-peq 26)) (28::Int))
  , scope "pnum.fail1" $ void $ expectLeft (runPred @() ((peq 20 + peq 22 + pgt 24) * (-peq 25) * (-peq 26)) (25::Int))
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


