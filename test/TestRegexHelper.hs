{-# OPTIONS -Wall #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE OverloadedStrings #-}
module TestRegexHelper where
import Control.Monad
import EasyTest hiding (int, int', double)
import RegexHelper
import Text.Regex.Applicative
--import Test.QuickCheck

main :: IO ()
main = run suite

suite :: Test ()
suite = tests
  [ scope "stringci.ok1" $ expectEq ("AbC" =~ stringCI "aBc") (Just "AbC")
  , scope "tokenizespaces.ok1" $ expectEq ("   abc def  g   " =~ tokenizeSpaces) (Just ["abc","def","g"])
  , scope "tokenizeN.ok1" $ expectEq ("abc_----def_g " =~ tokenizeN (`elem` ['_','-'])) (Just ["abc","def","g "])
  , scope "oneOf.ok1" $ expectEq ("fred" =~ oneOf ["hello", "bye", "fred",""]) (Just "fred")
  , scope "oneOf.fail1" $ expectEq ("xxx" =~ oneOf ["hello", "bye", "fred",""]) Nothing
  , scope "findLongestPrefix.ok1" $ expectEq (findLongestPrefix (intersperseP' (replicateM 4) (sym '.') int) "123.44.111.23.3") (Just ([123,44,111,23,3],""))
  , scope "findLongestPrefix.ok2" $ expectEq (findLongestPrefix (intersperseP' few (sym '.') int) "123.44.111.23.333") (Just ([123,44,111,23,333],""))
  , scope "findLongestPrefix.ok3" $ expectEq (findLongestPrefix (intersperseP' some (sym '.') int) "123.44.111.23.333") (Just ([123,44,111,23,333],""))
  , scope "findLongestPrefix.ok4" $ expectEq (findLongestPrefix (intersperseP' many (sym '.') int) "123.44.111.23.333") (Just ([123,44,111,23,333],""))
  , scope "int.ok1" $ expectEq ("+123" =~ int) (Just 123)
  , scope "int.ok2" $ expectEq ("123" =~ int) (Just 123)
  , scope "int.ok3" $ expectEq ("-123" =~ int) (Just (-123))
  , scope "double.ok1" $ expectEq ("-0.2345" =~ double) (Just (-0.2345))
  , scope "double.ok2" $ expectAll' (Just 0) (=~ double) ["0","+0","-0","-00000","0.000"]
  , scope "double.fail1" $ expectAll' Nothing (=~ double) ["0.",".0","x","-"]
  , scope "quoted.ok1" $ expectEq ("\"abc\"" =~ quoted) (Just "abc")
  , scope "quoted.fail1" $ expectAll' Nothing (=~ quoted) ["\"\""," \"aa\"","abc","","\"","\"abc" ]
  , scope "quoted.ok1" $ expectEq ("\"abc\"" =~ quoted) (Just "abc")
  ]
{-
>quickCheck (\(a::Double) -> abs(fromJust (show a =~ double) - a) < 0.000000001)
+++ OK, passed 100 tests.
it :: ()

>quickCheck (\(a::Int) -> Just a == (show a =~ int))
+++ OK, passed 100 tests.
it :: ()
-}
