{-# OPTIONS -Wall #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TupleSections #-}
module TestRegexHelper where
import Control.Monad
import Test.Tasty
import Test.Tasty.HUnit
import RegexHelper
import Text.Regex.Applicative
import Data.Either
import Control.Arrow
--import Test.QuickCheck

main :: IO ()
main = suite

suite :: IO ()
suite = defaultMain $ testGroup "TestRegexHelper"
  [ testCase "stringci.ok1" $ (@?=) ("AbC" =~ stringCI "aBc") (Just "AbC")
  , testCase "tokenizespaces.ok1" $ (@?=) ("   abc def  g   " =~ tokenizeSpaces) (Just ["abc","def","g"])
  , testCase "tokenizeN.ok1" $ (@?=) ("abc_----def_g " =~ tokenizeN (`elem` ['_','-'])) (Just ["abc","def","g "])
  , testCase "oneOf.ok1" $ (@?=) ("fred" =~ oneOf ["hello", "bye", "fred",""]) (Just "fred")
  , testCase "oneOf.fail1" $ (@?=) ("xxx" =~ oneOf ["hello", "bye", "fred",""]) Nothing
  , testCase "findLongestPrefix.ok1" $ (@?=) (findLongestPrefix (intersperseP' (replicateM 4) (sym '.') int) "123.44.111.23.3") (Just ([123,44,111,23,3],""))
  , testCase "findLongestPrefix.ok2" $ (@?=) (findLongestPrefix (intersperseP' few (sym '.') int) "123.44.111.23.333") (Just ([123,44,111,23,333],""))
  , testCase "findLongestPrefix.ok3" $ (@?=) (findLongestPrefix (intersperseP' some (sym '.') int) "123.44.111.23.333") (Just ([123,44,111,23,333],""))
  , testCase "findLongestPrefix.ok4" $ (@?=) (findLongestPrefix (intersperseP' many (sym '.') int) "123.44.111.23.333") (Just ([123,44,111,23,333],""))
  , testCase "int.ok1" $ (@?=) ("+123" =~ int) (Just 123)
  , testCase "int.ok2" $ (@?=) ("123" =~ int) (Just 123)
  , testCase "int.ok3" $ (@?=) ("-123" =~ int) (Just (-123))
  , testCase "double.ok1" $ (@?=) ("-0.2345" =~ double) (Just (-0.2345))
  , testCase "double.ok2" $ expectAll' (Just 0) (=~ double) ["0","+0","-0","-00000","0.000"]
  , testCase "double.fail1" $ expectAll' Nothing (=~ double) ["0.",".0","x","-"]
  , testCase "quoted.ok1" $ (@?=) ("\"abc\"" =~ quoted) (Just "abc")
  , testCase "quoted.fail1" $ expectAll' Nothing (=~ quoted) ["\"\""," \"aa\"","abc","","\"","\"abc" ]
  , testCase "quoted.ok1" $ (@?=) ("\"abc\"" =~ quoted) (Just "abc")
  ]

liftMaybe :: Eq a => a -> a -> Either (a,a) ()
liftMaybe expected actual | expected == actual = Right ()
                          | otherwise = Left (expected, actual)

expectAll' :: (Show a, Show a1, Eq a, Eq a1) => a1 -> (a -> a1) -> [a] -> IO ()
expectAll' w p = expectAll (liftMaybe w . p)

expectAll :: (Eq a, Show a, HasCallStack, Show b) => (a -> Either b ()) -> [a] -> IO ()
expectAll p as = case lefts (map (\a -> left (a,) (p a)) as) of
                   [] -> pure ()
                   xs@(_:_) -> assertFailure $ "expected all to succeed but " <> show (length xs) <> " failed " <> show xs


{-
>quickCheck (\(a::Double) -> abs(fromJust (show a =~ double) - a) < 0.000000001)
+++ OK, passed 100 tests.
it :: ()

>quickCheck (\(a::Int) -> Just a == (show a =~ int))
+++ OK, passed 100 tests.
it :: ()
-}
