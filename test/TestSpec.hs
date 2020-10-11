module Main where
import qualified TestPred
import qualified TestRegexHelper
import Test.Tasty ( defaultMain, testGroup )

main :: IO ()
main =
  defaultMain $ testGroup "alltests"
    [ TestPred.suite
    , TestRegexHelper.suite
    ]
