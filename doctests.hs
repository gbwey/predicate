import Test.DocTest
-- main = doctest ["src", "--verbose"]
main :: IO ()
main = doctest ["src"]

{-
C:\haskell\predicate>stack exec doctest -- "src/PredState.hs"
Examples: 198  Tried: 198  Errors: 0  Failures: 0

C:\haskell\predicate>stack exec doctest -- "src/Pred.hs"
Examples: 198  Tried: 198  Errors: 0  Failures: 0

-- just specify the directory
C:\haskell\predicate>stack exec doctest -- src
Examples: 398  Tried: 398  Errors: 0  Failures: 0
-}