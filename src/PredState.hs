{-# OPTIONS -Wall #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
module PredState where
import Data.Foldable
import Control.Lens
import Control.Lens.Extras
import Data.Function
import Data.Tree
import Data.Tree.Lens
import Data.Tree.Pretty
import Data.Coerce
import Data.Proxy
import Data.List.NonEmpty (NonEmpty(..))
import qualified Data.List.NonEmpty as N
import qualified Data.Text as T
import Data.Text (Text)
import Data.Aeson
import Data.Aeson.Lens
import Data.Char
import Data.String
import Control.Arrow
import PredHelper
import RegexHelper
import VinylHelper
import Data.Either
import Data.These
import Data.These.Combinators
import Data.List hiding (uncons)
import Data.Time
import Data.Time.Lens
import qualified Data.Sequence as Seq
import Data.Sequence (Seq)
import qualified Data.Map.Strict as M
import Data.Map.Strict (Map)
import qualified Control.Monad.State.Strict as S
import qualified Data.HashMap.Strict as H
import Data.HashMap.Strict (HashMap)
import Data.Hashable
import Data.Scientific
import Data.Vector (Vector)
import JsonHelper
import Data.Maybe
import qualified Control.Monad.Reader as R
import Control.Monad
import Data.Vinyl
import qualified Data.Vinyl.Functor as V
import Data.Vinyl.TypeLevel
import qualified GHC.TypeLits as G
import Text.Regex.Applicative

import PredJson -- needed for doctest

data Pred z a where
  -- | leaf constructor that sets the final state. see 'BoolPE'
  --
  --   >>> pe2' (ptrue' "true predicate") ()
  --   <BLANKLINE>
  --   TrueP  PConst a=() | true predicate
  --   <BLANKLINE>
  --
  --   >>> pe2' (pfalse' "false predicate") ()
  --   <BLANKLINE>
  --   FalseP PConst a=() | false predicate
  --   <BLANKLINE>
  --
  --   >>> pe2' (pfail "failed predicate") ()
  --   <BLANKLINE>
  --   [Error failed predicate] PConst a=()
  --   <BLANKLINE>
  --
  PConst      :: BoolPE -> Pred z a
  -- | lifts a predicate function
  --
  --   >>> pe1' (PLift "or" or) [True,False,True]
  --   <BLANKLINE>
  --   TrueP  PLift or | a=[True,False,True]
  --   <BLANKLINE>
  --
  PLift       :: String -> (a -> Bool) -> Pred z a
  -- this gives us the contravariance we need
  -- can encode all functions with PFn or PFnPartial
  -- we skip traceability on the a->b part and lose equality entirely
  -- but traceability comes back on Pred z b
  -- | applies a normal function to the value in 'Pred'
  PFn         :: Show b => String -> (a -> b) -> Pred z b -> Pred z a

  -- | lifts a string to a 'Pred' using 'StringOperator' and case sensitivity
  --
  --   >>> pe' (sinfix "abc") "xxxAbCyyy"
  --   <BLANKLINE>
  --   TrueP  PStringCI "abc" `isInfixOf` "xxxAbCyyy"
  --   <BLANKLINE>
  --
  PString     :: SConv s => Case -> StringOperator -> s -> Pred z s
  -- | finds the levenshtein distance between the two strings
  --
  --   runs the predicate Pred Int using that calculated distance
  --
  --   >>> pe1' (PDist CS "abc" $ plt 2) "abCd"
  --   <BLANKLINE>
  --   FalseP PDistCS | dist=2 | s=abc | t=abCd
  --   |
  --   `- FalseP 2 < 2
  --   <BLANKLINE>
  --
  --   >>> pe1' (PDist CS "abc" 1) "abc"
  --   <BLANKLINE>
  --   TrueP  PDistCS | dist=0 | s=abc | t=abc
  --   |
  --   `- TrueP  PConst a=0
  --   <BLANKLINE>
  --
  --   >>> pe1' (PDist CS "abc" 1) "Abc"
  --   <BLANKLINE>
  --   TrueP  PDistCS | dist=1 | s=abc | t=Abc
  --   |
  --   `- TrueP  PConst a=1
  --   <BLANKLINE>
  --
  --   >>> pe1' (PDist CS "abc" 1) "Abcxyz"
  --   <BLANKLINE>
  --   TrueP  PDistCS | dist=4 | s=abc | t=Abcxyz
  --   |
  --   `- TrueP  PConst a=4
  --   <BLANKLINE>
  --
  --   >>> pe1' (PDist CI "abc" 1) "Abcxyz"
  --   <BLANKLINE>
  --   TrueP  PDistCI | dist=3 | s=abc | t=Abcxyz
  --   |
  --   `- TrueP  PConst a=3
  --   <BLANKLINE>
  --
  PDist       :: SConv s => Case -> s -> Pred z Int -> Pred z s

  -- | compare the value using the 'CmpOperator'
  --
  --   >>> pe2' (PCmp Gt 4 * PCmp Lt 10) 12
  --   <BLANKLINE>
  --   FalseP PAnd
  --   |
  --   +- TrueP  12 > 4
  --   |
  --   `- FalseP 12 < 10
  --   <BLANKLINE>
  --
  PCmp        :: Ord a => CmpOperator -> a -> Pred z a

  -- | compare the value using 'Eq' instance only so doesnt require 'Ord' instance
  --
  --   >>> pe' (PEq False 'x') 'y'
  --   <BLANKLINE>
  --   TrueP  'y' /= 'x'
  --   <BLANKLINE>
  --
  --   >>> pe' (PEq True 'x') 'y'
  --   <BLANKLINE>
  --   FalseP 'y' == 'x'
  --   <BLANKLINE>
  --
  --   >>> pe' (PEq True 'x') 'x'
  --   <BLANKLINE>
  --   TrueP  'x' == 'x'
  --   <BLANKLINE>
  --
  PEq         :: Eq a => Bool -> a -> Pred z a
  -- | compare the values in a tuple using the 'CmpOperator'
  --
  --   >>> pe2' plt2 (14,13)
  --   <BLANKLINE>
  --   FalseP PCmp2 14 < 13
  --   <BLANKLINE>
  --
  --   >>> pe1' (PCmp2 Gt * PEq2 True + PFst (pgt 10) + PBoth 1 0) (12,11)
  --   <BLANKLINE>
  --   TrueP  POr
  --   |
  --   +- TrueP  POr
  --   |  |
  --   |  +- FalseP PAnd
  --   |  |  |
  --   |  |  +- TrueP  PCmp2 12 > 11
  --   |  |  |
  --   |  |  `- FalseP PEq2 12 == 11
  --   |  |
  --   |  `- TrueP  PFst a=12 snd=11
  --   |     |
  --   |     `- TrueP  12 > 10
  --   |
  --   `- FalseP PBoth
  --      |
  --      +- TrueP  PConst a=12
  --      |
  --      `- FalseP PConst a=11
  --   <BLANKLINE>
  --
  PCmp2       :: (a' ~ a, Show a', Ord a) => CmpOperator -> Pred z (a, a')
  -- | compare the values in a tuple using (==) (/=) using only Eq constraint
  --
  --   >>> pe' (PEq2 True) (14,4)
  --   <BLANKLINE>
  --   FalseP PEq2 14 == 4
  --   <BLANKLINE>
  --
  --   >>> pe' (PEq2 False) (14,4)
  --   <BLANKLINE>
  --   TrueP  PEq2 14 /= 4
  --   <BLANKLINE>
  --
  --   >>> pe' (PCmp2 Lt) (14,4)
  --   <BLANKLINE>
  --   FalseP PCmp2 14 < 4
  --   <BLANKLINE>
  --
  --   >>> pe' (PCmp2 Gt) (14,4)
  --   <BLANKLINE>
  --   TrueP  PCmp2 14 > 4
  --   <BLANKLINE>
  --
  PEq2        :: (a' ~ a, Show a', Eq a) => Bool -> Pred z (a, a')
  -- same as String but works any foldables: case sensitivity doesnt come into it
  -- would be cool if we could somehow piggyback off PString and ignore case
  -- | simple matching using prefix/infix etc. for case matching use 'PString'
  PMatch      :: (Foldable t, Eq a, Show a) => StringOperator -> [a] -> Pred z (t a)

-- Pred z (Int,[b],[a])   Pred z ([b],[a]) -- not much diff between success and failure
-- so if Int==0 then success
-- returns how many were not processed and the results from each one and the remainder
-- todo: should be (Int,Int) ie how many of how many so if PFst peq2 then good
  -- | matches sequentially each regex until completed or fails
  PRegexs     :: (Foldable t, Eq a, Show a, Show b) =>
         [(RType, RE a b)] --  list or regex and how to process them using 'RType'
      -> Pred z ((Int,Int), ([b],[a])) -- how many failed/succeeded and the list of good outputs and the remainder after the run
      -> Pred z (t a) --  foldable list predicate

  -- | matches sequentially each regex until completed or fails (using Vinyl)
  --
  --   >>> :set -XTypeApplications
  --   >>> :set -XDataKinds
  --   >>> import Text.Regex.Applicative.Common (digit)
  --   >>> pe1' (PRegexV (double :& sym 'x' :& string "abc" :& digit :& RNil) 0 $ PFst $ pri @0 (pgt 33)) "234.56xabc7zzzz"
  --   <BLANKLINE>
  --   TrueP  PRegexV (4) | matched all | leftovers=zzzz
  --   |
  --   +- TrueP  PFst a={234.56, 'x', "abc", 7} snd="zzzz"
  --   |  |
  --   |  `- TrueP  PFn @0 | a={234.56, 'x', "abc", 7} | b=234.56
  --   |     |
  --   |     `- TrueP  234.56 > 33.0
  --   |
  --   `- matched all | leftovers=zzzz
  --      |
  --      +- i=0 | a=234.56 | used=234.56 | remaining=xabc7zzzz
  --      |
  --      +- i=1 | a='x' | used=x | remaining=abc7zzzz
  --      |
  --      +- i=2 | a="abc" | used=abc | remaining=7zzzz
  --      |
  --      `- i=3 | a=7 | used=7 | remaining=zzzz
  --   <BLANKLINE>
  --
  --   >>> :set -XTypeApplications
  --   >>> :set -XDataKinds
  --   >>> import Text.Regex.Applicative.Common (digit)
  --   >>> pe1' (PRegexV (double :& sym 'x' :& string "abc" :& digit :& RNil) 0 $ PFst $ pri @0 (pgt 33)) "234.56xabczzzz"
  --   <BLANKLINE>
  --   FalseP PRegexV (4) | only matched 3 of 4 | leftovers=zzzz
  --   |
  --   +- FalseP PConst a="zzzz"
  --   |
  --   `- only matched 3 of 4 | leftovers=zzzz
  --      |
  --      +- i=0 | a=234.56 | used=234.56 | remaining=xabczzzz
  --      |
  --      +- i=1 | a='x' | used=x | remaining=abczzzz
  --      |
  --      `- i=2 | a="abc" | used=abc | remaining=zzzz
  --   <BLANKLINE>
  --
  --   >>> import Text.Regex.Applicative.Common (digit)
  --   >>> pe1' (PRegexV (double :& sym 'x' :& string "abc" :& digit :& RNil) 0 $ PFst $ prx (pgt 33)) "234.56xabc7zzzz"
  --   <BLANKLINE>
  --   FalseP PRegexV (4) | matched all | leftovers=zzzz
  --   |
  --   +- FalseP PFst a={234.56, 'x', "abc", 7} snd="zzzz"
  --   |  |
  --   |  `- FalseP PFn prx | a={234.56, 'x', "abc", 7} | b=7
  --   |     |
  --   |     `- FalseP 7 > 33
  --   |
  --   `- matched all | leftovers=zzzz
  --      |
  --      +- i=0 | a=234.56 | used=234.56 | remaining=xabc7zzzz
  --      |
  --      +- i=1 | a='x' | used=x | remaining=abc7zzzz
  --      |
  --      +- i=2 | a="abc" | used=abc | remaining=7zzzz
  --      |
  --      `- i=3 | a=7 | used=7 | remaining=zzzz
  --   <BLANKLINE>
  --
  --   >>> import Text.Regex.Applicative.Common (digit)
  --   >>> pe1' (PRegexV (double :& sym 'x' :& string "abc" :& digit :& RNil) 0 $ PFst $ prx (peq 'y')) "234.56xabc7zzzz"
  --   <BLANKLINE>
  --   FalseP PRegexV (4) | matched all | leftovers=zzzz
  --   |
  --   +- FalseP PFst a={234.56, 'x', "abc", 7} snd="zzzz"
  --   |  |
  --   |  `- FalseP PFn prx | a={234.56, 'x', "abc", 7} | b='x'
  --   |     |
  --   |     `- FalseP 'x' == 'y'
  --   |
  --   `- matched all | leftovers=zzzz
  --      |
  --      +- i=0 | a=234.56 | used=234.56 | remaining=xabc7zzzz
  --      |
  --      +- i=1 | a='x' | used=x | remaining=abc7zzzz
  --      |
  --      +- i=2 | a="abc" | used=abc | remaining=7zzzz
  --      |
  --      `- i=3 | a=7 | used=7 | remaining=zzzz
  --   <BLANKLINE>
  --
  --   >>> :set -XOverloadedStrings
  --   >>> pe1' (PRegexV (ratio :& void spaces1 :& int :& void spaces1 :& word :& RNil) 0 $ PFst $ prx "HELlo" * prx (pgt (9999::Int))) "12367   99  hellx world"
  --   <BLANKLINE>
  --   FalseP PRegexV (5) | matched all | leftovers= world
  --   |
  --   +- FalseP PFst a={12367 % 1, (), 99, (), "hellx"} snd=" world"
  --   |  |
  --   |  `- FalseP PAnd
  --   |     |
  --   |     +- FalseP PFn prx | a={12367 % 1, (), 99, (), "hellx"} | b="hellx"
  --   |     |  |
  --   |     |  `- FalseP PStringCI "hellx" == "HELlo"
  --   |     |
  --   |     `- FalseP PFn prx | a={12367 % 1, (), 99, (), "hellx"} | b=99
  --   |        |
  --   |        `- FalseP 99 > 9999
  --   |
  --   `- matched all | leftovers= world
  --      |
  --      +- i=0 | a=12367 % 1 | used=12367 | remaining=   99  hellx world
  --      |
  --      +- i=1 | a=() | used=    | remaining=99  hellx world
  --      |
  --      +- i=2 | a=99 | used=99 | remaining=  hellx world
  --      |
  --      +- i=3 | a=() | used=   | remaining=hellx world
  --      |
  --      `- i=4 | a="hellx" | used=hellx | remaining= world
  --   <BLANKLINE>
  --
  --   >>> :set -XTypeApplications
  --   >>> :set -XDataKinds
  --   >>> pe1' (PRegexV (ratio :& void spaces1 :& int :& void spaces1 :& word :& RNil) 0 $ PFst $ prx "HELlo" * pri @2 (pgt 9999)) "12367   99  hellx world"
  --   <BLANKLINE>
  --   FalseP PRegexV (5) | matched all | leftovers= world
  --   |
  --   +- FalseP PFst a={12367 % 1, (), 99, (), "hellx"} snd=" world"
  --   |  |
  --   |  `- FalseP PAnd
  --   |     |
  --   |     +- FalseP PFn prx | a={12367 % 1, (), 99, (), "hellx"} | b="hellx"
  --   |     |  |
  --   |     |  `- FalseP PStringCI "hellx" == "HELlo"
  --   |     |
  --   |     `- FalseP PFn @2 | a={12367 % 1, (), 99, (), "hellx"} | b=99
  --   |        |
  --   |        `- FalseP 99 > 9999
  --   |
  --   `- matched all | leftovers= world
  --      |
  --      +- i=0 | a=12367 % 1 | used=12367 | remaining=   99  hellx world
  --      |
  --      +- i=1 | a=() | used=    | remaining=99  hellx world
  --      |
  --      +- i=2 | a=99 | used=99 | remaining=  hellx world
  --      |
  --      +- i=3 | a=() | used=   | remaining=hellx world
  --      |
  --      `- i=4 | a="hellx" | used=hellx | remaining= world
  --   <BLANKLINE>
  --
  --   >>> import Text.Regex.Applicative.Common (digit)
  --   >>> pe1' (PRegexV (_d :& ratio :& _w :& ipaddr :& _w :& digit :& RNil) 0 $ PFst $ prx $ (plt 102)) "927.34a27.11.4.33c9junk"
  --   <BLANKLINE>
  --   TrueP  PRegexV (6) | matched all | leftovers=junk
  --   |
  --   +- TrueP  PFst a={'9', 1367 % 50, 'a', IP:27.11.4.33, 'c', 9} snd="junk"
  --   |  |
  --   |  `- TrueP  PFn prx | a={'9', 1367 % 50, 'a', IP:27.11.4.33, 'c', 9} | b=9
  --   |     |
  --   |     `- TrueP  9 < 102
  --   |
  --   `- matched all | leftovers=junk
  --      |
  --      +- i=0 | a='9' | used=9 | remaining=27.34a27.11.4.33c9junk
  --      |
  --      +- i=1 | a=1367 % 50 | used=27.34 | remaining=a27.11.4.33c9junk
  --      |
  --      +- i=2 | a='a' | used=a | remaining=27.11.4.33c9junk
  --      |
  --      +- i=3 | a=IP:27.11.4.33 | used=27.11.4.33 | remaining=c9junk
  --      |
  --      +- i=4 | a='c' | used=c | remaining=9junk
  --      |
  --      `- i=5 | a=9 | used=9 | remaining=junk
  --   <BLANKLINE>
  --
  --   >>> :set -XTypeApplications
  --   >>> pe2' (PRegexV (_d :& word :& gregorian :& "abc" :& RNil) 0 $ PFst $ prx @Day (PView days (pgt 12) * PView years (plt 2000))) "9hello2018-12-22abcXYZ"
  --   <BLANKLINE>
  --   FalseP PRegexV (4) | matched all | leftovers=XYZ
  --   |
  --   +- FalseP PFst a={'9', "hello", 2018-12-22, "abc"} snd="XYZ"
  --   |  |
  --   |  `- FalseP PFn prx | a={'9', "hello", 2018-12-22, "abc"} | b=2018-12-22
  --   |     |
  --   |     `- FalseP PAnd
  --   |        |
  --   |        +- TrueP  PView s=2018-12-22 a=22
  --   |        |  |
  --   |        |  `- TrueP  22 > 12
  --   |        |
  --   |        `- FalseP PView s=2018-12-22 a=2018
  --   |           |
  --   |           `- FalseP 2018 < 2000
  --   |
  --   `- matched all | leftovers=XYZ
  --      |
  --      +- i=0 | a='9' | used=9 | remaining=hello2018-12-22abcXYZ
  --      |
  --      +- i=1 | a="hello" | used=hello | remaining=2018-12-22abcXYZ
  --      |
  --      +- i=2 | a=2018-12-22 | used=2018-12-22 | remaining=abcXYZ
  --      |
  --      `- i=3 | a="abc" | used=abc | remaining=XYZ
  --   <BLANKLINE>
  --
  --   >>> pe2' (PRegexV ("abc" :& ratio :& _w :& hex :& RNil) 0 1) "abc123.456Za805f__"
  --   <BLANKLINE>
  --   TrueP  PRegexV (4) | matched all | leftovers=__
  --   |
  --   +- TrueP  PConst a=({"abc", 15432 % 125, 'Z', 688223},"__")
  --   |
  --   `- matched all | leftovers=__
  --      |
  --      +- i=0 | a="abc" | used=abc | remaining=123.456Za805f__
  --      |
  --      +- i=1 | a=15432 % 125 | used=123.456 | remaining=Za805f__
  --      |
  --      +- i=2 | a='Z' | used=Z | remaining=a805f__
  --      |
  --      `- i=3 | a=688223 | used=a805f | remaining=__
  --   <BLANKLINE>
  --
  --   >>> :set -XTypeApplications
  --   >>> import Text.Regex.Applicative.Common (digit)
  --   >>> pe1' (PRegexV (_d :& ratio :& _w :& ipaddr :& _w :& digit :& RNil) 0 $ PFst $ pri @5 (plt 102)) "927.34a27.11.4.33c9junk"
  --   <BLANKLINE>
  --   TrueP  PRegexV (6) | matched all | leftovers=junk
  --   |
  --   +- TrueP  PFst a={'9', 1367 % 50, 'a', IP:27.11.4.33, 'c', 9} snd="junk"
  --   |  |
  --   |  `- TrueP  PFn @5 | a={'9', 1367 % 50, 'a', IP:27.11.4.33, 'c', 9} | b=9
  --   |     |
  --   |     `- TrueP  9 < 102
  --   |
  --   `- matched all | leftovers=junk
  --      |
  --      +- i=0 | a='9' | used=9 | remaining=27.34a27.11.4.33c9junk
  --      |
  --      +- i=1 | a=1367 % 50 | used=27.34 | remaining=a27.11.4.33c9junk
  --      |
  --      +- i=2 | a='a' | used=a | remaining=27.11.4.33c9junk
  --      |
  --      +- i=3 | a=IP:27.11.4.33 | used=27.11.4.33 | remaining=c9junk
  --      |
  --      +- i=4 | a='c' | used=c | remaining=9junk
  --      |
  --      `- i=5 | a=9 | used=9 | remaining=junk
  --   <BLANKLINE>
  --
  --   >>> import Text.Regex.Applicative.Common (digit)
  --   >>> pe1' (PRegexV (_d :& ratio :& _w :& ipaddr :& _w :& digit :& RNil) 0 $ PFst $ prx (plt 102)) "927.34a27.11.4.33c9junk"
  --   <BLANKLINE>
  --   TrueP  PRegexV (6) | matched all | leftovers=junk
  --   |
  --   +- TrueP  PFst a={'9', 1367 % 50, 'a', IP:27.11.4.33, 'c', 9} snd="junk"
  --   |  |
  --   |  `- TrueP  PFn prx | a={'9', 1367 % 50, 'a', IP:27.11.4.33, 'c', 9} | b=9
  --   |     |
  --   |     `- TrueP  9 < 102
  --   |
  --   `- matched all | leftovers=junk
  --      |
  --      +- i=0 | a='9' | used=9 | remaining=27.34a27.11.4.33c9junk
  --      |
  --      +- i=1 | a=1367 % 50 | used=27.34 | remaining=a27.11.4.33c9junk
  --      |
  --      +- i=2 | a='a' | used=a | remaining=27.11.4.33c9junk
  --      |
  --      +- i=3 | a=IP:27.11.4.33 | used=27.11.4.33 | remaining=c9junk
  --      |
  --      +- i=4 | a='c' | used=c | remaining=9junk
  --      |
  --      `- i=5 | a=9 | used=9 | remaining=junk
  --   <BLANKLINE>
  --
  --   >>> pe2' (PRegexV (_d :& word :& gregorian :& "abc":& RNil) 0 $ PFst $ prx @Day (PView days (pgt 12) * PView years (plt 2000))) "9hello2018-12-22abcXYZ"
  --   <BLANKLINE>
  --   FalseP PRegexV (4) | matched all | leftovers=XYZ
  --   |
  --   +- FalseP PFst a={'9', "hello", 2018-12-22, "abc"} snd="XYZ"
  --   |  |
  --   |  `- FalseP PFn prx | a={'9', "hello", 2018-12-22, "abc"} | b=2018-12-22
  --   |     |
  --   |     `- FalseP PAnd
  --   |        |
  --   |        +- TrueP  PView s=2018-12-22 a=22
  --   |        |  |
  --   |        |  `- TrueP  22 > 12
  --   |        |
  --   |        `- FalseP PView s=2018-12-22 a=2018
  --   |           |
  --   |           `- FalseP 2018 < 2000
  --   |
  --   `- matched all | leftovers=XYZ
  --      |
  --      +- i=0 | a='9' | used=9 | remaining=hello2018-12-22abcXYZ
  --      |
  --      +- i=1 | a="hello" | used=hello | remaining=2018-12-22abcXYZ
  --      |
  --      +- i=2 | a=2018-12-22 | used=2018-12-22 | remaining=abcXYZ
  --      |
  --      `- i=3 | a="abc" | used=abc | remaining=XYZ
  --   <BLANKLINE>
  --
  --   >>> pe2' (PRegexV ("abc" :& ratio :& _w :& hex :& RNil) 0 1) "abc123.456Z805f__"
  --   <BLANKLINE>
  --   TrueP  PRegexV (4) | matched all | leftovers=__
  --   |
  --   +- TrueP  PConst a=({"abc", 15432 % 125, 'Z', 32863},"__")
  --   |
  --   `- matched all | leftovers=__
  --      |
  --      +- i=0 | a="abc" | used=abc | remaining=123.456Z805f__
  --      |
  --      +- i=1 | a=15432 % 125 | used=123.456 | remaining=Z805f__
  --      |
  --      +- i=2 | a='Z' | used=Z | remaining=805f__
  --      |
  --      `- i=3 | a=32863 | used=805f | remaining=__
  --   <BLANKLINE>
  --
  --   >>> pe2' (PRegexV ("abc" :& ratio :& _w :& hex :& RNil) 0 1) "abc123.456ZG805f__"
  --   <BLANKLINE>
  --   FalseP PRegexV (4) | only matched 3 of 4 | leftovers=G805f__
  --   |
  --   +- FalseP PConst a="G805f__"
  --   |
  --   `- only matched 3 of 4 | leftovers=G805f__
  --      |
  --      +- i=0 | a="abc" | used=abc | remaining=123.456ZG805f__
  --      |
  --      +- i=1 | a=15432 % 125 | used=123.456 | remaining=ZG805f__
  --      |
  --      `- i=2 | a='Z' | used=Z | remaining=G805f__
  --   <BLANKLINE>
  --
  PRegexV
    ::  (RecordToList rs, ReifyConstraint Show V.Identity rs, RMap rs, RecAll V.Identity rs Show, RecAll RXHolder rs Show) =>
        Rec (RE Char) rs
     -> Pred z String -- leftovers
     -> Pred z (Rec V.Identity rs, String)
     -> Pred z String

  -- | tries to match the given regex using prefix search
  --
  --   >>> pe1' (PRegex RLong ipaddr 0 $ PFst $ pfn (^.. folded) $ PShow 1) "123.2.11.22xxx"
  --   <BLANKLINE>
  --   TrueP  PRegex RLong as="123.2.11.22xxx" b=IP:123.2.11.22 rs="xxx"
  --   |
  --   `- TrueP  PFst a=IP:123.2.11.22 snd="xxx"
  --      |
  --      `- TrueP  PFn | a=IP:123.2.11.22 | b=[123,2,11,22]
  --         |
  --         `- TrueP  PShow
  --            |
  --            +- TrueP  PConst a=[123,2,11,22]
  --            |
  --            `- ===== PShow =====
  --               |
  --               +- i=0 a=123
  --               |
  --               +- i=1 a=2
  --               |
  --               +- i=2 a=11
  --               |
  --               `- i=3 a=22
  --   <BLANKLINE>
  --
  --   >>> :set -XOverloadedStrings
  --   >>> pe2' (PRegex RLong (intersperseNP 4 "-" int) 0 1) "1-2-3-4"
  --   <BLANKLINE>
  --   TrueP  PRegex RLong as="1-2-3-4" b=[1,2,3,4] rs=""
  --   |
  --   `- TrueP  PConst a=([1,2,3,4],"")
  --   <BLANKLINE>
  --
  --   >>> :set -XOverloadedStrings
  --   >>> pe2' (PRegex RLong (intersperseNP 4 "-" int) 0 1) "1-2-3"
  --   <BLANKLINE>
  --   FalseP PRegex RLong no regex match | PConst a=()
  --   <BLANKLINE>
  --
  --   >>> :set -XOverloadedStrings
  --   >>> pe2' (PRegex RLong (intersperseNP 4 "-" int) 0 1) "1-2-3-4-5"
  --   <BLANKLINE>
  --   TrueP  PRegex RLong as="1-2-3-4-5" b=[1,2,3,4] rs="-5"
  --   |
  --   `- TrueP  PConst a=([1,2,3,4],"-5")
  --   <BLANKLINE>
  --
  --   >>> :set -XOverloadedStrings
  --   >>> pe2' (PRegex RLong (widthExact 4 "x") 0 1) "xx"
  --   <BLANKLINE>
  --   FalseP PRegex RLong no regex match | PConst a=()
  --   <BLANKLINE>
  --
  --   >>> :set -XOverloadedStrings
  --   >>> pe2' (PRegex RLong (widthExact 4 "x") 0 1) "xxxx"
  --   <BLANKLINE>
  --   TrueP  PRegex RLong as="xxxx" b=["x","x","x","x"] rs=""
  --   |
  --   `- TrueP  PConst a=(["x","x","x","x"],"")
  --   <BLANKLINE>
  --
  --   >>> :set -XOverloadedStrings
  --   >>> pe2' (PRegex RLong (widthExact 4 "x") 0 1) "xxxxx"
  --   <BLANKLINE>
  --   TrueP  PRegex RLong as="xxxxx" b=["x","x","x","x"] rs="x"
  --   |
  --   `- TrueP  PConst a=(["x","x","x","x"],"x")
  --   <BLANKLINE>
  --
  --   >>> pe2' (PRegex RLong (stringCI "abCD") 0 1) "ABcd"
  --   <BLANKLINE>
  --   TrueP  PRegex RLong as="ABcd" b="ABcd" rs=""
  --   |
  --   `- TrueP  PConst a=("ABcd","")
  --   <BLANKLINE>
  --
  --   >>> pe2' (PRegex RLong (stringCI "abCD") 0 1) "xBcd"
  --   <BLANKLINE>
  --   FalseP PRegex RLong no regex match | PConst a=()
  --   <BLANKLINE>
  --
  PRegex      :: (Foldable t, Show a, Show b) =>
         RType
      -> RE a b
      -> Pred z () -- failure predicate
      -> Pred z (b,[a]) -- success predicate which has the result and the remaining input
      -> Pred z (t a)
  -- infix finds the leftmost match!! so <|> pure will match if lhs doesnt match prefix! cos pure matches against "" at the beginning
  -- few is very powerful: it does adjust to work with greedy combinators

  -- | tries to match the given regex using infix search
  --
  --   >>> pe2' (PRegexI RLong ipaddr 0 $ p_2 $ plift isIPValid) "123.4.4.200"
  --   <BLANKLINE>
  --   TrueP  PRegexI RLong as="123.4.4.200" b=IP:123.4.4.200 used="" remaining=""
  --   |
  --   `- TrueP  PFn _2 | a=("",IP:123.4.4.200,"") | b=IP:123.4.4.200
  --      |
  --      `- TrueP  PLift | a=IP:123.4.4.200
  --   <BLANKLINE>
  --
  --   >>> pe2' (PRegexI RLong ipaddr 0 $ p_2 $ plift isIPValid) "123.4.4.300"
  --   <BLANKLINE>
  --   FalseP PRegexI RLong as="123.4.4.300" b=IP:123.4.4.300 used="" remaining=""
  --   |
  --   `- FalseP PFn _2 | a=("",IP:123.4.4.300,"") | b=IP:123.4.4.300
  --      |
  --      `- FalseP PLift | a=IP:123.4.4.300
  --   <BLANKLINE>
  --
  PRegexI :: (Foldable t, Show a, Show b) =>
         RType
      -> RE a b
      -> Pred z () -- failure predicate
      -> Pred z ([a],b,[a]) -- success predicate which has the unprocessed input before, the result and then remaining input
      -> Pred z (t a)

  -- | matches i,j times: see pregexN1: not sure how useful [Re a b] cos same type
  --   >>> pe2' (PRegexN (These 3 5) (RLong, _d) 0 1) "12x"
  --   <BLANKLINE>
  --   FalseP PRegexN {3,5} | only matched 2 of {3,5} | leftovers="x"
  --   |
  --   +- FalseP PConst a=((2,3),"x")
  --   |
  --   `- only matched 2 of {3,5} | leftovers="x"
  --      |
  --      +- i=0 | b='1' | used="1" | remaining="2x"
  --      |
  --      `- i=1 | b='2' | used="2" | remaining="x"
  --   <BLANKLINE>
  --
  --   >>> pe2' (PRegexN (These 3 5) (RLong, _d) 0 1) "1234x"
  --   <BLANKLINE>
  --   TrueP  PRegexN {3,5} | matched all(4) | leftovers="x"
  --   |
  --   +- TrueP  PConst a=("1234","x")
  --   |
  --   `- matched all(4) | leftovers="x"
  --      |
  --      +- i=0 | b='1' | used="1" | remaining="234x"
  --      |
  --      +- i=1 | b='2' | used="2" | remaining="34x"
  --      |
  --      +- i=2 | b='3' | used="3" | remaining="4x"
  --      |
  --      `- i=3 | b='4' | used="4" | remaining="x"
  --   <BLANKLINE>
  --
  --   >>> pe2' (PRegexN (These 3 5) (RLong, _d) 0 1) "12345"
  --   <BLANKLINE>
  --   TrueP  PRegexN {3,5} | matched all(5) | leftovers=""
  --   |
  --   +- TrueP  PConst a=("12345","")
  --   |
  --   `- matched all(5) | leftovers=""
  --      |
  --      +- i=0 | b='1' | used="1" | remaining="2345"
  --      |
  --      +- i=1 | b='2' | used="2" | remaining="345"
  --      |
  --      +- i=2 | b='3' | used="3" | remaining="45"
  --      |
  --      +- i=3 | b='4' | used="4" | remaining="5"
  --      |
  --      `- i=4 | b='5' | used="5" | remaining=""
  --   <BLANKLINE>
  --
  --   >>> pe2' (PRegexN (These 3 5) (RLong, _d) 0 1) "123456"
  --   <BLANKLINE>
  --   TrueP  PRegexN {3,5} | matched all(5) | leftovers="6"
  --   |
  --   +- TrueP  PConst a=("12345","6")
  --   |
  --   `- matched all(5) | leftovers="6"
  --      |
  --      +- i=0 | b='1' | used="1" | remaining="23456"
  --      |
  --      +- i=1 | b='2' | used="2" | remaining="3456"
  --      |
  --      +- i=2 | b='3' | used="3" | remaining="456"
  --      |
  --      +- i=3 | b='4' | used="4" | remaining="56"
  --      |
  --      `- i=4 | b='5' | used="5" | remaining="6"
  --   <BLANKLINE>
  --
  --   >>> pe2' (PRegexN (These 3 5) (RLong, spaces *> _d) 0 1) "123456"
  --   <BLANKLINE>
  --   TrueP  PRegexN {3,5} | matched all(5) | leftovers="6"
  --   |
  --   +- TrueP  PConst a=("12345","6")
  --   |
  --   `- matched all(5) | leftovers="6"
  --      |
  --      +- i=0 | b='1' | used="1" | remaining="23456"
  --      |
  --      +- i=1 | b='2' | used="2" | remaining="3456"
  --      |
  --      +- i=2 | b='3' | used="3" | remaining="456"
  --      |
  --      +- i=3 | b='4' | used="4" | remaining="56"
  --      |
  --      `- i=4 | b='5' | used="5" | remaining="6"
  --   <BLANKLINE>
  --
  --   >>> pe2' (PRegexN (These 3 5) (RLong, spaces *> _d) 0 1) "12  34   56"
  --   <BLANKLINE>
  --   TrueP  PRegexN {3,5} | matched all(5) | leftovers="6"
  --   |
  --   +- TrueP  PConst a=("12345","6")
  --   |
  --   `- matched all(5) | leftovers="6"
  --      |
  --      +- i=0 | b='1' | used="1" | remaining="2  34   56"
  --      |
  --      +- i=1 | b='2' | used="2" | remaining="  34   56"
  --      |
  --      +- i=2 | b='3' | used="  3" | remaining="4   56"
  --      |
  --      +- i=3 | b='4' | used="4" | remaining="   56"
  --      |
  --      `- i=4 | b='5' | used="   5" | remaining="6"
  --   <BLANKLINE>
  --
  PRegexN  :: (Foldable t, Eq a, Show a, Show b) =>
         These Int Int
      -> (RType, RE a b)
      -> Pred z ((Int, Int), [a]) -- failure predicate
      -> Pred z ([b], [a]) -- success predicate which has the result and the remaining input
      -> Pred z (t a)

  -- | matches i,j times with intersperse
  --
  --   >>> pe2' (PRegexIP (These 4 4) RLong "." int 3 1) "444.123.3.4xxx"
  --   <BLANKLINE>
  --   TrueP  PRegexIP{4} | matched all(4) | leftovers="xxx"
  --   |
  --   +- TrueP  PConst a=([444,123,3,4],"xxx")
  --   |
  --   `- matched all(4) | leftovers="xxx"
  --      |
  --      +- i=0 | b=444 | used="444" | remaining=".123.3.4xxx"
  --      |
  --      +- i=1 | b=123 | used=".123" | remaining=".3.4xxx"
  --      |
  --      +- i=2 | b=3 | used=".3" | remaining=".4xxx"
  --      |
  --      `- i=3 | b=4 | used=".4" | remaining="xxx"
  --   <BLANKLINE>
  --
  --   >>> pe2' (PRegexIP (These 4 4) RLong "." int 3 1) "444.123.3.4xxx"
  --   <BLANKLINE>
  --   TrueP  PRegexIP{4} | matched all(4) | leftovers="xxx"
  --   |
  --   +- TrueP  PConst a=([444,123,3,4],"xxx")
  --   |
  --   `- matched all(4) | leftovers="xxx"
  --      |
  --      +- i=0 | b=444 | used="444" | remaining=".123.3.4xxx"
  --      |
  --      +- i=1 | b=123 | used=".123" | remaining=".3.4xxx"
  --      |
  --      +- i=2 | b=3 | used=".3" | remaining=".4xxx"
  --      |
  --      `- i=3 | b=4 | used=".4" | remaining="xxx"
  --   <BLANKLINE>
  --
  --   >>> pe2' (PRegexIP (These 4 4) RLong "." int 3 1) "444.123.3.4.789xxx"
  --   <BLANKLINE>
  --   TrueP  PRegexIP{4} | matched all(4) | leftovers=".789xxx"
  --   |
  --   +- TrueP  PConst a=([444,123,3,4],".789xxx")
  --   |
  --   `- matched all(4) | leftovers=".789xxx"
  --      |
  --      +- i=0 | b=444 | used="444" | remaining=".123.3.4.789xxx"
  --      |
  --      +- i=1 | b=123 | used=".123" | remaining=".3.4.789xxx"
  --      |
  --      +- i=2 | b=3 | used=".3" | remaining=".4.789xxx"
  --      |
  --      `- i=3 | b=4 | used=".4" | remaining=".789xxx"
  --   <BLANKLINE>
  --
  --   >>> pe2' (PRegexIP (These 4 4) RLong "." int 3 1) "444.123.3.xxx"
  --   <BLANKLINE>
  --   [Error fromInteger: n=3: use 0 or 1] PRegexIP{4} | only matched 3 of {4} | leftovers=".xxx"
  --   |
  --   +- [Error fromInteger: n=3: use 0 or 1] PConst a=((2,4),".xxx")
  --   |
  --   `- only matched 3 of {4} | leftovers=".xxx"
  --      |
  --      +- i=0 | b=444 | used="444" | remaining=".123.3.xxx"
  --      |
  --      +- i=1 | b=123 | used=".123" | remaining=".3.xxx"
  --      |
  --      `- i=2 | b=3 | used=".3" | remaining=".xxx"
  --   <BLANKLINE>
  --
  --   >>> pe2' (PRegexIP (These 4 5) RLong "." int 3 1) "444.123.3.xxx"
  --   <BLANKLINE>
  --   [Error fromInteger: n=3: use 0 or 1] PRegexIP{4,5} | only matched 3 of {4,5} | leftovers=".xxx"
  --   |
  --   +- [Error fromInteger: n=3: use 0 or 1] PConst a=((2,4),".xxx")
  --   |
  --   `- only matched 3 of {4,5} | leftovers=".xxx"
  --      |
  --      +- i=0 | b=444 | used="444" | remaining=".123.3.xxx"
  --      |
  --      +- i=1 | b=123 | used=".123" | remaining=".3.xxx"
  --      |
  --      `- i=2 | b=3 | used=".3" | remaining=".xxx"
  --   <BLANKLINE>
  --
  --   >>> pe2' (PRegexIP (These 4 5) RLong "." int 3 1) "444.123.3.5.6.xxx"
  --   <BLANKLINE>
  --   TrueP  PRegexIP{4,5} | matched all(5) | leftovers=".xxx"
  --   |
  --   +- TrueP  PConst a=([444,123,3,5,6],".xxx")
  --   |
  --   `- matched all(5) | leftovers=".xxx"
  --      |
  --      +- i=0 | b=444 | used="444" | remaining=".123.3.5.6.xxx"
  --      |
  --      +- i=1 | b=123 | used=".123" | remaining=".3.5.6.xxx"
  --      |
  --      +- i=2 | b=3 | used=".3" | remaining=".5.6.xxx"
  --      |
  --      +- i=3 | b=5 | used=".5" | remaining=".6.xxx"
  --      |
  --      `- i=4 | b=6 | used=".6" | remaining=".xxx"
  --   <BLANKLINE>
  --
  PRegexIP  :: (Foldable t, Eq a, Show a, Show b) =>
         These Int Int
      -> RType
      -> RE a x
      -> RE a b
      -> Pred z ((Int, Int), [a]) -- failure predicate
      -> Pred z ([b], [a]) -- success predicate which has the result and the remaining input
      -> Pred z (t a)

  -- | matches on a range of values
  --
  --   first value is the lower bound and second is the upper bound
  --
  --   has nicer output than 'PElem'
  --
  --
  --   >>> pe2' (PRange 4 7) 5
  --   <BLANKLINE>
  --   TrueP  5 == [4..7]
  --   <BLANKLINE>
  --
  --   >>> pe2' (PRange 4 7) 3
  --   <BLANKLINE>
  --   FalseP 3 < 4 (Under)
  --   <BLANKLINE>
  --
  --   >>> pe2' (PRange 4 7) 8
  --   <BLANKLINE>
  --   FalseP 8 > 7 (Over)
  --   <BLANKLINE>
  --
  PRange      :: Ord a => a -> a -> Pred z a
  -- | like 'Data.List.elem'
  PElem       :: (Eq a, Foldable t) => t a -> Pred z a

  -- | like 'Data.Foldable.length'
  --
  --   >>> pe1' (PLen (pgt 1)) "abcd"
  --   <BLANKLINE>
  --   TrueP  PLen 4 as="abcd"
  --   |
  --   `- TrueP  4 > 1
  --   <BLANKLINE>
  --
  PLen        :: Foldable t => Pred z Int -> Pred z (t a)
  -- works for monomorphic stuff as well as lists and maybes etc  ([],[]) is empty but not null!
  -- | empty predicate which is sometimes different from 'PNull' eg ([],[]) is empty but not null
  --
  --   >>> pe2' PEmpty [(),()]
  --   <BLANKLINE>
  --   FalseP PEmpty s=[(),()]
  --   <BLANKLINE>
  --
  --   >>> pe2' PEmpty ((),())
  --   <BLANKLINE>
  --   TrueP  PEmpty s=((),())
  --   <BLANKLINE>
  --
  --   >>> pe2' PEmpty [1..4]
  --   <BLANKLINE>
  --   FalseP PEmpty s=[1,2,3,4]
  --   <BLANKLINE>
  --
  --   >>> pe2' PEmpty []
  --   <BLANKLINE>
  --   TrueP  PEmpty s=[]
  --   <BLANKLINE>
  --
  PEmpty      :: AsEmpty s => Pred z s
  -- not as general cos doesnt work with monomorphic stuff
  -- | like 'Data.Foldable.null'
  --
  --   >>> pe2' PNull ((),())
  --   <BLANKLINE>
  --   FalseP PNull length=1 as=((),())
  --   <BLANKLINE>
  --
  --   >>> pe2' PNull [1..4]
  --   <BLANKLINE>
  --   FalseP PNull length=4 as=[1,2,3,4]
  --   <BLANKLINE>
  --
  --   >>> pe2' PNull []
  --   <BLANKLINE>
  --   TrueP  PNull length=0 as=[]
  --   <BLANKLINE>
  --
  PNull       :: Foldable t => Pred z (t a)
  -- does PFst and PSnd: use 1 to emulate
  -- | applies a different predicate to each side of a tuple. same as 'PFst' p * 'PSnd' q but has nicer output
  --
  --   >>> :set -XOverloadedStrings
  --   >>> pe2' (PBoth "abc" (pgt 'x')) ("AbC",'y')
  --   <BLANKLINE>
  --   TrueP  PBoth
  --   |
  --   +- TrueP  PStringCI "AbC" == "abc"
  --   |
  --   `- TrueP  'y' > 'x'
  --   <BLANKLINE>
  --
  PBoth       :: (Show a, Show b) => Pred z a -> Pred z b -> Pred z (a, b)
  -- | applies a predicate to left hand side of a tuple and ignores the right
  --
  --   >>> pe' (PFst (PRange 4 8)) (9,'x')
  --   <BLANKLINE>
  --   FalseP PFst
  --   |
  --   `- FalseP 9 > 8 (Over)
  --   <BLANKLINE>
  --
  PFst        :: (Show a, Show b) => Pred z a -> Pred z (a, b)
  -- | applies a predicate to right hand side of a tuple and ignores the left
  --
  --   >>> pe' (PSnd (PRange 'm' 'y')) (9,'x')
  --   <BLANKLINE>
  --   TrueP  PSnd
  --   |
  --   `- TrueP  'x' == ['m'..'y']
  --   <BLANKLINE>
  --
  PSnd        :: (Show a, Show b) => Pred z b -> Pred z (a, b)

  -- | swap arguments in a tuple. useful when push everything good to the right
  --
  --   >>> pe2' (PSwap $ PBoth (peq 4) pid) (True,4)
  --   <BLANKLINE>
  --   TrueP  PSwap a,b=(True,4)
  --   |
  --   `- TrueP  PBoth
  --      |
  --      +- TrueP  4 == 4
  --      |
  --      `- TrueP  PLift id | a=True
  --   <BLANKLINE>
  --
  PSwap       :: (Swapped p, Show (p d c)) => Pred z (p d c) -> Pred z (p c d)
  -- | reverse predicate
  --
  --   >>> :set -XOverloadedStrings
  --   >>> pe' (PReverse $ sinfix "zyx") ("pqrstuvwxyz" :: Text)
  --   <BLANKLINE>
  --   TrueP  PReverse
  --   |
  --   `- TrueP  PStringCI "zyx" `isInfixOf` "zyxwvutsrqp"
  --   <BLANKLINE>
  --
  PReverse    :: (Reversing t, Show t) => Pred z t -> Pred z t
  -- | like 'Data.List.splitAt', splits a foldable into two
  --
  --   >>> :set -XTypeApplications
  --   >>> pe2' (PSplitAt @[] 3 1) "abcdefg"
  --   <BLANKLINE>
  --   TrueP  PSplitAt 3 | lhs="abc" rhs="defg"
  --   |
  --   `- TrueP  PConst a=("abc","defg")
  --   <BLANKLINE>
  --
  PSplitAt    :: (Foldable t, Show a) => Int -> Pred z ([a],[a]) -> Pred z (t a)
--  PTake       :: (Foldable t, Show a) => Int -> Pred z [a] -> Pred z (t a)
--  PDrop       :: (Foldable t, Show a) => Int -> Pred z [a] -> Pred z (t a)

  -- boolean operators
  -- | conjunction of two predicates
  --
  --   >>> pe' (PAnd (pgt 4) (plt 10)) 7
  --   <BLANKLINE>
  --   TrueP  PAnd
  --   |
  --   +- TrueP  7 > 4
  --   |
  --   `- TrueP  7 < 10
  --   <BLANKLINE>
  --
  PAnd        :: Pred z a -> Pred z a -> Pred z a
  POr         :: Pred z a -> Pred z a -> Pred z a
  PXor        :: Pred z a -> Pred z a -> Pred z a
  PEquiv      :: Pred z a -> Pred z a -> Pred z a
  -- | implication predicate
  --
  --   >>> pe' (PImpl (pgt 4) (plt 10)) 3
  --   <BLANKLINE>
  --   TrueP  PImpl
  --   |
  --   +- FalseP 3 > 4
  --   |
  --   `- TrueP  3 < 10
  --   <BLANKLINE>
  --
  PImpl       :: Pred z a -> Pred z a -> Pred z a
  -- | negation predicate
  --
  --   >>> pe' (PNot (PMatch SInfix "xyz")) "abcxyzdef"
  --   <BLANKLINE>
  --   FalseP PNot
  --   |
  --   `- TrueP  PMatch "xyz" `isInfixOf` "abcxyzdef"
  --   <BLANKLINE>
  --
  PNot        :: Pred z a -> Pred z a

  -- generalises PAnds and POrs + more
  -- cheating a bit by blending tacking the results of [Pred z a] onto the end of the nodes of Pred z [Bool]
  -- | applies a list of predicates to a single value and then calls Pred z [Bool] with the results
  --
  --   >>> pe2' (POps [peq 2, peq 4, pgt 3,peven] $ plift and) 4
  --   <BLANKLINE>
  --   FalseP POps | (1,3)
  --   |
  --   `- FalseP PLift | a=[False,True,True,True]
  --      |
  --      +- FalseP i=0: 4 == 2
  --      |
  --      +- TrueP  i=1: 4 == 4
  --      |
  --      +- TrueP  i=2: 4 > 3
  --      |
  --      `- TrueP  i=3: PLift even | a=4
  --   <BLANKLINE>
  --
  POps        :: [Pred z a] -> Pred z [Bool] -> Pred z a
--  PAnds       :: [Pred z a] -> Pred z a
--  POrs        :: [Pred z a] -> Pred z a

  -- deals with adjacent elements -- porder using pgroupBy (groupBy') is better
  -- but this does give nicer tracing so good for demoing
  -- | a predicate for checking that the list is the given order by checking adjacent elements
  --
  --   >>> pe2' (POrder Le) [1,2,3,3,4]
  --   <BLANKLINE>
  --   TrueP  POrder (<=)
  --   |
  --   +- TrueP  i=0: 1
  --   |
  --   +- TrueP  i=1: 2
  --   |
  --   +- TrueP  i=2: 3
  --   |
  --   +- TrueP  i=3: 3
  --   |
  --   `- TrueP  i=4: 4
  --   <BLANKLINE>
  --
  --   >>> pe2' (POrder Le) [1,2,3,3,4,7,1]
  --   <BLANKLINE>
  --   FalseP POrder (<=) errs=1 (6,1)
  --   |
  --   +- TrueP  i=0: 1
  --   |
  --   +- TrueP  i=1: 2
  --   |
  --   +- TrueP  i=2: 3
  --   |
  --   +- TrueP  i=3: 3
  --   |
  --   +- TrueP  i=4: 4
  --   |
  --   +- TrueP  i=5: 7
  --   |
  --   `- FalseP i=6: 1
  --   <BLANKLINE>
  --
  POrder      :: (Foldable t, Ord a, Show a) => CmpOperator -> Pred z (t a)
  -- | subset of 'POrder' but works only for (==)
  --
  -- Eq so makes sure all the elements are the same (or not if False)
  --
  -- Value has an Eq constraint but not an Ord so is necessary
  --
  -- ie all the same and (/=) where no adjacent elements are the same.
  --
  -- Useful if you only have the 'Eq' constraint
  POrderEq    :: (Foldable t, Eq a, Show a) => Bool -> Pred z (t a)

-- debugging stuff
  -- | modify the options see 'POpts'
  PChangeOpts :: (POpts -> POpts) -> Pred z a -> Pred z a
  -- | passthrough predicate for debugging a single value
  PShow1      :: Show a => Pred z a -> Pred z a
  -- | passthrough predicate for debugging a foldable of values as a list
  --
  --   >>> :set -XTypeApplications
  --   >>> pe' (PShow @[] 1) "abcdef"
  --   <BLANKLINE>
  --   TrueP  PShow
  --   |
  --   +- TrueP
  --   |
  --   `- ===== PShow =====
  --      |
  --      +- i=0 a='a'
  --      |
  --      +- i=1 a='b'
  --      |
  --      +- i=2 a='c'
  --      |
  --      +- i=3 a='d'
  --      |
  --      +- i=4 a='e'
  --      |
  --      `- i=5 a='f'
  --   <BLANKLINE>
  --
  --   >>> pe' (PShow 1) ["hello","wor\nld","end"]
  --   <BLANKLINE>
  --   TrueP  PShow
  --   |
  --   +- TrueP
  --   |
  --   `- ===== PShow =====
  --      |
  --      +- i=0 a="hello"
  --      |
  --      +- i=1 a="wor\nld"
  --      |
  --      `- i=2 a="end"
  --   <BLANKLINE>
  --
  PShow       :: (Foldable t, Show a) => Pred z [a] -> Pred z (t a)
-- for String/Text where we dont want double quotes escaped
  -- | passthrough predicate for debugging a single value as a Showable. Nicer output than 'PShow1'
  PShowS1     :: SConv a => Pred z a -> Pred z a
  -- | passthrough predicate for debugging a foldable of values as a Showable. Nicer output than 'PShow'
  --
  --   >>> pe' (PShowS 1) ["hello","wor\nld","end"]
  --   <BLANKLINE>
  --   TrueP  PShowS
  --   |
  --   +- TrueP
  --   |
  --   `- ===== PShowS =====
  --      |
  --      +- i=0 a=hello
  --      |
  --      +- i=1 a=wor
  --      |  ld
  --      |
  --      `- i=2 a=end
  --   <BLANKLINE>
  --
  PShowS      :: (Foldable t, SConv a) => Pred z [a] -> Pred z (t a)
  -- | if given predicate is false then fail with the given message string else let it continue
  --
  --   >>> pe' (POrDie "oops" (pgt 4)) 5
  --   <BLANKLINE>
  --   TrueP  POrDie oops:ok
  --   |
  --   `- TrueP  5 > 4
  --   <BLANKLINE>
  --
  --   >>> pe' (POrDie "oops" (pgt 4)) 3
  --   <BLANKLINE>
  --   [Error oops] POrDie oops: found False
  --   |
  --   `- FalseP 3 > 4
  --   <BLANKLINE>
  --
  POrDie      :: String -> Pred z a -> Pred z a
  -- | catch a failed predicate
  --
  --   >>> pe' (PCatch 1 (POrDie "xxx" (peq 4))) 5
  --   <BLANKLINE>
  --   TrueP  PCatch:Exception caught | xxx
  --   |
  --   +- TrueP
  --   |
  --   `- [Error xxx] POrDie xxx: found False
  --      |
  --      `- FalseP 5 == 4
  --   <BLANKLINE>
  --
  PCatch      :: Pred z a -- failure predicate to run if predicate fails
              -> Pred z a -- run this predicate and if it fails run the error predicate above
              -> Pred z a
  -- | prepend an informational message either inline or nested
  --
  --   >>> pe' (PMsg Nested "extra info" $ pgt 4) 5
  --   <BLANKLINE>
  --   TrueP  PMsg:extra info
  --   |
  --   `- TrueP  5 > 4
  --   <BLANKLINE>
  --
  --   >>> pe' (PMsg Nested "extra info" $ pgt 4) 4
  --   <BLANKLINE>
  --   FalseP PMsg:extra info
  --   |
  --   `- FalseP 4 > 4
  --   <BLANKLINE>
  --
  --   >>> pe' (PMsg Inline "extra info" $ pgt 4) 5
  --   <BLANKLINE>
  --   TrueP  extra info | 5 > 4
  --   <BLANKLINE>
  --
  PMsg        :: Inline -> String -> Pred z a -> Pred z a
  -- | depending on the result of Pred a calls the predicates matching 'BoolPE'.
  --
  --   Nothing means passthru else override: pexc pbad then pgood
  --
  --   >>> pe' (PIf Nothing Nothing (Just $ pgt 45) 1) 44
  --   <BLANKLINE>
  --   FalseP PIf <True Branch>
  --   |
  --   +- FalseP 44 > 45
  --   |
  --   `- TrueP  <override with False>
  --   <BLANKLINE>
  --
  --   >>> pe' (PIf Nothing Nothing (Just $ pgt 45) 1) 44
  --   <BLANKLINE>
  --   FalseP PIf <True Branch>
  --   |
  --   +- FalseP 44 > 45
  --   |
  --   `- TrueP  <override with False>
  --   <BLANKLINE>
  --
  PIf         :: Maybe (Pred z a) -- on failure ie 'FailP'
              -> Maybe (Pred z a) -- on false ie 'FalseP'
              -> Maybe (Pred z a) -- on true ie 'TrueP'
              -> Pred z a         -- the predicate to run
              -> Pred z a
-- days from current time  -- need lambda application
-- days from a given time?
--  PDays       :: Pred z Int -> LocalTime -> Pred z LocalTime

-- need to be able to join 2 predicates back together
  -- | function application
  --
  --   >>> import Text.Show.Functions
  --   >>> pe2' (PFn "xx" (*) (PApp 7 1)) 1012
  --   <BLANKLINE>
  --   TrueP  PFn xx | a=1012 | b=<function>
  --   |
  --   `- TrueP  PApp a=7 b=7084
  --      |
  --      `- TrueP  PConst a=7084
  --   <BLANKLINE>
  --
  --   >>> pe2' (PApp 5 1) (*)
  --   <BLANKLINE>
  --   TrueP  PApp a=5 b=<function>
  --   |
  --   `- TrueP  PConst a=<function>
  --   <BLANKLINE>
  --
  --   >>> pe2' (PApp 5 (PApp 3 1)) (*)
  --   <BLANKLINE>
  --   TrueP  PApp a=5 b=<function>
  --   |
  --   `- TrueP  PApp a=3 b=15
  --      |
  --      `- TrueP  PConst a=15
  --   <BLANKLINE>
  --
  --   >>> pe2' (PApp 4 1) (*5)
  --   <BLANKLINE>
  --   TrueP  PApp a=4 b=20
  --   |
  --   `- TrueP  PConst a=20
  --   <BLANKLINE>
  --
  PApp        :: (Show a, Show b) => a -> Pred z b -> Pred z (a -> b)
--  PApp1       :: (Show a, Show b) => Pred z (a -> Pred b ) -> (a -> Pred z b ) -> Pred z a

-- PDivide id = PBoth -- once you divide then you have lost ability to compare between 2 values!
--  PDivide     :: (Show a, Show b, Show c) => (a -> (b, c)) -> Pred z b -> Pred z c -> Pred z a    -- see pdivide: PFn + PBoth
--  PChoose     :: (Show a, Show b, Show c) => (a -> Either b c) -> Pred z b -> Pred z c -> Pred z a  -- see pchoose: PFn + PEither

  -- not sure what use this is! our values are from a structure but it is intriguing
  -- | join
  PJoin       :: Show a => a -> Pred z (Pred z a)
  -- if you want to just run a lens
  -- | lift a 'Control.Lens.Type.Lens' or 'Control.Lens.Type.Prism' or 'Control.Lens.Type.Iso' etc into Pred
  --
  --   >>> pe1' (PView (_1 . _2) $ PLen $ pgt 3) (('x',"abcd"),True)
  --   <BLANKLINE>
  --   TrueP  PView s=(('x',"abcd"),True) a="abcd"
  --   |
  --   `- TrueP  PLen 4 as="abcd"
  --      |
  --      `- TrueP  4 > 3
  --   <BLANKLINE>
  --
  PView       :: Show a => Getting a s a -> Pred z a -> Pred z s

-- can change the tree [internal: used for change return code or adding message info] lpred rpred work on that
  -- | internal: decorate the output
  PTree       :: (TT -> TT) -> Pred z a -> Pred z a
  -- | coerce a predicate on one value to another using 'Coercible'
  PCoerce     :: (Coercible a b, Show a, Show b) => Pred z b -> Pred z a

  -- | monomorphic head predicate - 'PUncons' or 'phead' are more general
  --
  --   >>> pe' (PHead 0 (peq 'x')) "xbc"
  --   <BLANKLINE>
  --   TrueP  PHead 'x'
  --   |
  --   `- TrueP  'x' == 'x'
  --   <BLANKLINE>
  --
  --   >>> pe' (PHead 0 (peq 'x')) "abc"
  --   <BLANKLINE>
  --   FalseP PHead 'a'
  --   |
  --   `- FalseP 'a' == 'x'
  --   <BLANKLINE>
  --
  PHead       :: Show a => Pred z () -- failure predicate ie list is empty
                        -> Pred z a  -- success predicate ie list has at least one element
                        -> Pred z [a]
  -- | monomorphic last predicate - 'PUnsnoc' or 'plast' are more general
  PLast       :: Show a => Pred z () -- failure predicate ie list is empty
                        -> Pred z a  -- success predicate ie list has at least one element
                        -> Pred z [a]

  -- | runs a predicate on exactly one element
  --
  --   >>> pe' (POne 0 (PBoth (peq 'x') (PLen $ plt 3)) $ peq 'x') "xyzw"
  --   <BLANKLINE>
  --   FalseP POne extra values! a='x' s'="yzw"
  --   |
  --   `- FalseP PBoth
  --      |
  --      +- TrueP  'x' == 'x'
  --      |
  --      `- FalseP PLen 3
  --         |
  --         `- FalseP 3 < 3
  --   <BLANKLINE>
  --
  --   >>> pe' (POne 0 (PBoth (peq 'x') (PLen $ plt 3)) $ peq 'x') "x"
  --   <BLANKLINE>
  --   TrueP  POne 'x'
  --   |
  --   `- TrueP  'x' == 'x'
  --   <BLANKLINE>
  --
  --   >>> pe' (POne 0 (PBoth (peq 'x') (PLen $ plt 3)) $ peq 'x') ""
  --   <BLANKLINE>
  --   FalseP POne empty!
  --   <BLANKLINE>
  --
  POne       :: (AsEmpty s, Cons s s a a, Show a, Show s) =>
            Pred z () -- failure predicate (empty list)
         -> Pred z (a,s) -- failure predicate (more than one element)
         -> Pred z a -- success predicate ie list has exactly one element
         -> Pred z s
-- foldable wont work for monomorpic types
  POneT        :: (Foldable t, Show a) => Pred z () -> Pred z (a, [a]) -> Pred z a -> Pred z (t a)

  PUnconsT     :: (Foldable t, Show a) => Pred z () -> Pred z (a, [a]) -> Pred z (t a)
  PUnsnocT     :: (Foldable t, Show a) => Pred z () -> Pred z ([a], a) -> Pred z (t a)

  -- | uncons
  --
  --   >>> :set -XOverloadedStrings
  --   >>> :set -XTypeApplications
  --   >>> pe' (PUncons @String (pfalse' "dude") 1) ""
  --   <BLANKLINE>
  --   FalseP PUncons empty | dude
  --   <BLANKLINE>
  --
  --   >>> :set -XOverloadedStrings
  --   >>> :set -XTypeApplications
  --   >>> pe1' (PUncons @[_] (pfalse' "dude") 1) ""
  --   <BLANKLINE>
  --   FalseP PUncons empty | PConst a=() | dude
  --   <BLANKLINE>
  --
  --   >>> :set -XOverloadedStrings
  --   >>> :set -XTypeApplications
  --   >>> pe1' (PUncons @Text (pfalse' "dude") 1) "abc"
  --   <BLANKLINE>
  --   TrueP  PUncons a='a' s="bc"
  --   |
  --   `- TrueP  PConst a=('a',"bc")
  --   <BLANKLINE>
  --
  --   >>> :set -XOverloadedStrings
  --   >>> :set -XTypeApplications
  --   >>> pe1' (PUncons @Text (pfalse' "dude") 1) ""
  --   <BLANKLINE>
  --   FalseP PUncons empty | PConst a=() | dude
  --   <BLANKLINE>
  --
  PUncons    :: (Show s, Cons s s a a, Show a) =>
       Pred z () -- failure predicate ie empty
    -> Pred z (a, s) -- success predicate with a tuple of the head and tail
    -> Pred z s
  -- | unsnoc
  --
  --   >>> pe1' (PUnsnoc 0 (PSnd (peq 'x'))) "xyz"
  --   <BLANKLINE>
  --   FalseP PUnsnoc a='z' s="xy"
  --   |
  --   `- FalseP PSnd a='z' fst="xy"
  --      |
  --      `- FalseP 'z' == 'x'
  --   <BLANKLINE>
  --
  PUnsnoc    :: (Snoc s s a a, Show a, Show s) =>
       Pred z () -- failure predicate ie empty
    -> Pred z (s, a) -- success predicate with a tuple of init and last
    -> Pred z s

-- works with monomorphic stuff too!! eg pe (PIx 1 0 1) ("ab"::Text)
  -- | index into a structure
  --
  {-   >>> :{
        :set -XOverloadedStrings
        :set -XFlexibleContexts
        let zzz = PIx "glossary" 0
                . PIx "GlossDiv" 0
                . PIx "GlossList" 0
                . PIx "GlossEntry" 0
                . PIx "GlossSee" 0
        pe' (zzz $ scs "mARkup") json1
        :}
  -}
  --   <BLANKLINE>
  --   FalseP PIx "glossary" Object (fromList [("GlossDiv",Object (fromLi...
  --   |
  --   `- FalseP PIx "GlossDiv" Object (fromList [("title",String "S"),("...
  --      |
  --      `- FalseP PIx "GlossList" Object (fromList [("GlossEntry",Objec...
  --         |
  --         `- FalseP PIx "GlossEntry" Object (fromList [("GlossSee",Str...
  --            |
  --            `- FalseP PIx "GlossSee" String "markup"
  --               |
  --               `- FalseP PStringCS String "markup" == String "mARkup"
  --   <BLANKLINE>
  --
  PIx         :: (Eq (Index s), Show s, Show (IxValue s), Show (Index s), Ixed s) =>
                    Index s -- index into the structure
                 -> Pred z () -- failure predicate
                 -> Pred z (IxValue s) -- success predicate
                 -> Pred z s

  -- | intersection of two lists:
  --
  --   calls a predicate with lists for left only, both and right only
  --
  --   >>> pe1' (PISect 1) ("abc","daaef":: String)
  --   <BLANKLINE>
  --   TrueP  PISect left="bc" isect="a" right="adef"
  --   |
  --   `- TrueP  PConst a=("bc","a","adef")
  --   <BLANKLINE>
  --
  --   >>> pe1' (PISect 1) ("abc","daaaef":: String)
  --   <BLANKLINE>
  --   TrueP  PISect left="bc" isect="a" right="aadef"
  --   |
  --   `- TrueP  PConst a=("bc","a","aadef")
  --   <BLANKLINE>
  --
  PISect :: (Foldable t, Ord a, Show a) => Pred z ([a], [a], [a]) -> Pred z (t a, t a)

  -- | intersection of a list. use 'PISect' if only using two values
  --
  --   'PISect' will give you stuff in left both and right
  --
  --   >>> :set -XTypeApplications
  --   >>> pe1' (PISectList @[] 1) $ reverse ["abdbc","defbba","bbbbd"]
  --   <BLANKLINE>
  --   TrueP  PISectList unmatched="bbaefc" matched="bbd"
  --   |
  --   `- TrueP  PConst a=("bbaefc","bbd")
  --   <BLANKLINE>
  --
  --   >>> :set -XTypeApplications
  --   >>> pe1' (PISectList @[] 1) $ reverse ["abdc","defba","bd"]
  --   <BLANKLINE>
  --   TrueP  PISectList unmatched="aefc" matched="bd"
  --   |
  --   `- TrueP  PConst a=("aefc","bd")
  --   <BLANKLINE>
  --
  --   >>> :set -XTypeApplications
  --   >>> pe1' (PISectList @[] 1) ["abdc","defba","bd"]
  --   <BLANKLINE>
  --   TrueP  PISectList unmatched="acaef" matched="bd"
  --   |
  --   `- TrueP  PConst a=("acaef","bd")
  --   <BLANKLINE>
  --
  --   >>> :set -XTypeApplications
  --   >>> pe1' (PISectList @[] 1) ["abdc","defa","bd"]
  --   <BLANKLINE>
  --   TrueP  PISectList unmatched="abcaefb" matched="d"
  --   |
  --   `- TrueP  PConst a=("abcaefb","d")
  --   <BLANKLINE>
  --
  PISectList :: (Foldable t, Foldable u, Ord a, Show a) => Pred z ([a], [a]) -> Pred z (u (t a))

  -- | divides a list into two with not matching on the left and transformed on the right
  --
  --   >>> pe1' (PMorph (^? _Left . to show) 1) [Left 1,Left 10,Left 12]
  --   <BLANKLINE>
  --   TrueP  PMorph bad=[] good=["1","10","12"]
  --   |
  --   `- TrueP  PConst a=([],["1","10","12"])
  --   <BLANKLINE>
  --
  --   >>> pe1' (PMorph (^? _Left . to show) 1) [Left 1,Left 10,Left 12,Right 'a']
  --   <BLANKLINE>
  --   TrueP  PMorph bad=[Right 'a'] good=["1","10","12"]
  --   |
  --   `- TrueP  PConst a=([Right 'a'],["1","10","12"])
  --   <BLANKLINE>
  --
  PMorph      :: (Foldable t, Show a, Show b) => (a -> Maybe b) -> Pred z ([a],[b]) -> Pred z (t a)

-- PEither and PMaybe can replace a lot if not all of the PFnPartial stuff: can use PFn to bust it down into PEither
  -- | deconstructs 'Maybe'
  --
  --   >>> pe' (PMaybe 0 (peq 'x')) Nothing
  --   <BLANKLINE>
  --   FalseP PMaybe (Nothing)
  --   <BLANKLINE>
  --
  --   >>> pe' (PMaybe 0 (peq 'x')) (Just 'y')
  --   <BLANKLINE>
  --   FalseP PMaybe (Just) 'y'
  --   |
  --   `- FalseP 'y' == 'x'
  --   <BLANKLINE>
  --
  --   >>> pe' (PMaybe 0 (peq 'x')) (Just 'x')
  --   <BLANKLINE>
  --   TrueP  PMaybe (Just) 'x'
  --   |
  --   `- TrueP  'x' == 'x'
  --   <BLANKLINE>
  --
  PMaybe      :: Show a =>
       Pred z () -- Nothing case
    -> Pred z a -- Just case
    -> Pred z (Maybe a)
  -- prism1 == pfalse prism2 == pfail msg
  -- | deconstructs 'Either'
  --
  --   >>> pe' (PEither (peq 'x') (-pid)) (Left 'x')
  --   <BLANKLINE>
  --   TrueP  PEither (Left) 'x'
  --   |
  --   `- TrueP  'x' == 'x'
  --   <BLANKLINE>
  --
  --   >>> pe' (PEither (peq 'x') (-pid)) (Right False)
  --   <BLANKLINE>
  --   TrueP  PEither (Right) False
  --   |
  --   `- TrueP  PNot
  --      |
  --      `- FalseP PLift id
  --   <BLANKLINE>
  --
  PEither     :: (Show a, Show b) => Pred z a -> Pred z b -> Pred z (Either a b)
  -- | deconstructs 'Data.These.These'
  --
  --   >>> pe' (PThese (peq 'x') (pgt 4) $ pfn (first $ \a -> ord 'z' - ord a) pgt2) (These 'x' 4)
  --   <BLANKLINE>
  --   FalseP PThese (These) a='x' b=4
  --   |
  --   `- FalseP PFn | a=('x',4) | b=(2,4)
  --      |
  --      `- FalseP PCmp2 2 > 4
  --   <BLANKLINE>
  --
  PThese      :: (Show a, Show b) =>
       Pred z a -- This predicate
    -> Pred z b -- That predicate
    -> Pred z (a, b) -- These predicate
    -> Pred z (These a b)

  -- | lift a maybe function to 'Pred'
  PPrism      :: (Show a, Show b) => String
                                  -> (a -> Maybe b)
                                  -> Pred z () -- failure predicate
                                  -> Pred z b -- success predicate
                                  -> Pred z a

  -- | lift a maybe over a tuple on lhs
  --
  --   >>> pe1' (PPrismL "dude" (^? _Left) 0 (PFn "zz" (first (succ.succ)) 1)) (Left 'x',True)
  --   <BLANKLINE>
  --   TrueP  PPrismL (Just) [dude] 'x'
  --   |
  --   `- TrueP  PFn zz | a=('x',True) | b=('z',True)
  --      |
  --      `- TrueP  PConst a=('z',True)
  --   <BLANKLINE>
  --
  PPrismL     :: (Show x, Show a, Show b) => String -> (a -> Maybe b) -> Pred z x -> Pred z (b, x) -> Pred z (a, x)
  PPrismR     :: (Show x, Show a, Show b) => String -> (a -> Maybe b) -> Pred z x -> Pred z (x, b) -> Pred z (x, a)

  PPrismLE    :: (Show c, Show x, Show a, Show b) => String -> (a -> Either b c) -> Pred z (b, x) -> Pred z (c, x) -> Pred z (a, x)
  PPrismRE    :: (Show c, Show x, Show a, Show b) => String -> (a -> Either b c) -> Pred z (x, b) -> Pred z (x, c) -> Pred z (x, a)
--  PFirst      :: (Show a, Show x, Show b) => Pred z a -> Pred z (a, x) -> Pred z (a, x)
--  PFirst      :: (Show a, Show x, Show b) => (a -> b) -> Pred z (b, x) -> Pred z (a, x)  -- PFn "PFirst" (first f)

  -- | matches predicates to values (order is not important)
  --
  --   a value is not allowed to be matched by more than one predicate
  --
  --   see 'preq' 'popt' etc
  --
  --   >>> pe1' (PLinear Rigid [preq (peq 'x'), preq (peq 'y'),preq (peq 'w')]) "yxxxxo"
  --   <BLANKLINE>
  --   FalseP PLinear Failed Pred [Int] | errors(1): NoMatch 5
  --   |
  --   +- FalseP Predicates | PZipAnd | PZipExact | (bad,good)=(2,1)
  --   |  |
  --   |  `- FalseP PLift and | a=[False,True,False]
  --   |     |
  --   |     +- FalseP i=0
  --   |     |  |
  --   |     |  +- FalseP 4 > 1 (Over)
  --   |     |  |
  --   |     |  `- a == 'x'
  --   |     |
  --   |     +- TrueP  i=1
  --   |     |  |
  --   |     |  +- TrueP  1 == 1
  --   |     |  |
  --   |     |  `- a == 'y'
  --   |     |
  --   |     `- FalseP i=2
  --   |        |
  --   |        +- FalseP 0 < 1 (Under)
  --   |        |
  --   |        `- a == 'w'
  --   |
  --   +- TrueP  PLinear | OneMatch 0 a='y' cnt=1 (i=1, a='y')
  --   |  |
  --   |  +- FalseP i=0: 'y' == 'x'
  --   |  |
  --   |  +- TrueP  i=1: 'y' == 'y'
  --   |  |
  --   |  `- FalseP i=2: 'y' == 'w'
  --   |
  --   +- TrueP  PLinear | OneMatch 1 a='x' cnt=1 (i=0, a='x')
  --   |  |
  --   |  +- TrueP  i=0: 'x' == 'x'
  --   |  |
  --   |  +- FalseP i=1: 'x' == 'y'
  --   |  |
  --   |  `- FalseP i=2: 'x' == 'w'
  --   |
  --   +- TrueP  PLinear | OneMatch 2 a='x' cnt=1 (i=0, a='x')
  --   |  |
  --   |  +- TrueP  i=0: 'x' == 'x'
  --   |  |
  --   |  +- FalseP i=1: 'x' == 'y'
  --   |  |
  --   |  `- FalseP i=2: 'x' == 'w'
  --   |
  --   +- TrueP  PLinear | OneMatch 3 a='x' cnt=1 (i=0, a='x')
  --   |  |
  --   |  +- TrueP  i=0: 'x' == 'x'
  --   |  |
  --   |  +- FalseP i=1: 'x' == 'y'
  --   |  |
  --   |  `- FalseP i=2: 'x' == 'w'
  --   |
  --   +- TrueP  PLinear | OneMatch 4 a='x' cnt=1 (i=0, a='x')
  --   |  |
  --   |  +- TrueP  i=0: 'x' == 'x'
  --   |  |
  --   |  +- FalseP i=1: 'x' == 'y'
  --   |  |
  --   |  `- FalseP i=2: 'x' == 'w'
  --   |
  --   `- FalseP PLinear NoMatch 5 a='o'
  --      |
  --      +- FalseP i=0: 'o' == 'x'
  --      |
  --      +- FalseP i=1: 'o' == 'y'
  --      |
  --      `- FalseP i=2: 'o' == 'w'
  --   <BLANKLINE>
  --
  --   >>> let m = M.fromList $ zip ['a'..] [12..15]
  --   >>> pe1' (pilist $ PLinear Rigid [preq (PFst (peq 'a')),preq (PFst (peq 'b'))]) m
  --   <BLANKLINE>
  --   FalseP PLinear | errors(2): NoMatch 2 | NoMatch 3
  --   |
  --   +- TrueP  Predicates | PZipAnd | PZipExact | (bad,good)=(0,2)
  --   |  |
  --   |  `- TrueP  PLift and | a=[True,True]
  --   |     |
  --   |     +- TrueP  i=0
  --   |     |  |
  --   |     |  +- TrueP  1 == 1
  --   |     |  |
  --   |     |  `- PFst
  --   |     |     |
  --   |     |     `- a == 'a'
  --   |     |
  --   |     `- TrueP  i=1
  --   |        |
  --   |        +- TrueP  1 == 1
  --   |        |
  --   |        `- PFst
  --   |           |
  --   |           `- a == 'b'
  --   |
  --   +- TrueP  PLinear | OneMatch 0 a=('a',12) cnt=1 (i=0, a=('a',12))
  --   |  |
  --   |  +- TrueP  i=0: PFst a='a' snd=12
  --   |  |  |
  --   |  |  `- TrueP  'a' == 'a'
  --   |  |
  --   |  `- FalseP i=1: PFst a='a' snd=12
  --   |     |
  --   |     `- FalseP 'a' == 'b'
  --   |
  --   +- TrueP  PLinear | OneMatch 1 a=('b',13) cnt=1 (i=1, a=('b',13))
  --   |  |
  --   |  +- FalseP i=0: PFst a='b' snd=13
  --   |  |  |
  --   |  |  `- FalseP 'b' == 'a'
  --   |  |
  --   |  `- TrueP  i=1: PFst a='b' snd=13
  --   |     |
  --   |     `- TrueP  'b' == 'b'
  --   |
  --   +- FalseP PLinear NoMatch 2 a=('c',14)
  --   |  |
  --   |  +- FalseP i=0: PFst a='c' snd=14
  --   |  |  |
  --   |  |  `- FalseP 'c' == 'a'
  --   |  |
  --   |  `- FalseP i=1: PFst a='c' snd=14
  --   |     |
  --   |     `- FalseP 'c' == 'b'
  --   |
  --   `- FalseP PLinear NoMatch 3 a=('d',15)
  --      |
  --      +- FalseP i=0: PFst a='d' snd=15
  --      |  |
  --      |  `- FalseP 'd' == 'a'
  --      |
  --      `- FalseP i=1: PFst a='d' snd=15
  --         |
  --         `- FalseP 'd' == 'b'
  --   <BLANKLINE>
  --
  PLinear     :: (Foldable t, Show a) =>
       Rigid -- if 'Rigid' then each value have to match a predicate
    -> [(Pred z Int, Pred z a)] -- lhs is a predicate on number of times the rhs predicate needs to succeed
    -> Pred z (t a)

  -- | runs the predicate against all the values and expects all to succeed. see 'pquantifier' and 'PPartition'
  --
  --   >>> pe1' (PForAll (PLen (peq 3) * PHead 0 (peq 'f'))) ["foo","ab","fghi","fxx",""]
  --   <BLANKLINE>
  --   FalseP PForAll | cnt=3 (i=1, a="ab")
  --   |
  --   +- TrueP  i=0: PAnd
  --   |  |
  --   |  +- TrueP  PLen 3 as="foo"
  --   |  |  |
  --   |  |  `- TrueP  3 == 3
  --   |  |
  --   |  `- TrueP  PHead 'f'
  --   |     |
  --   |     `- TrueP  'f' == 'f'
  --   |
  --   +- FalseP i=1: PAnd
  --   |  |
  --   |  +- FalseP PLen 2 as="ab"
  --   |  |  |
  --   |  |  `- FalseP 2 == 3
  --   |  |
  --   |  `- FalseP PHead 'a'
  --   |     |
  --   |     `- FalseP 'a' == 'f'
  --   |
  --   +- FalseP i=2: PAnd
  --   |  |
  --   |  +- FalseP PLen 4 as="fghi"
  --   |  |  |
  --   |  |  `- FalseP 4 == 3
  --   |  |
  --   |  `- TrueP  PHead 'f'
  --   |     |
  --   |     `- TrueP  'f' == 'f'
  --   |
  --   +- TrueP  i=3: PAnd
  --   |  |
  --   |  +- TrueP  PLen 3 as="fxx"
  --   |  |  |
  --   |  |  `- TrueP  3 == 3
  --   |  |
  --   |  `- TrueP  PHead 'f'
  --   |     |
  --   |     `- TrueP  'f' == 'f'
  --   |
  --   `- FalseP i=4: PAnd
  --      |
  --      +- FalseP PLen 0 as=""
  --      |  |
  --      |  `- FalseP 0 == 3
  --      |
  --      `- FalseP PHead empty | PConst a=()
  --   <BLANKLINE>
  --
  PForAll     :: (Foldable t, Show a) => Pred z a -> Pred z (t a)
  -- | runs the predicate against all the values and expects at least one to succeed. see 'pquantifier' and 'PPartition'
  --
  --   >>> pe' (PExists (peq 4)) [1..7]
  --   <BLANKLINE>
  --   TrueP  PExists | cnt=1 (i=3, a=4)
  --   |
  --   +- FalseP i=0: 1 == 4
  --   |
  --   +- FalseP i=1: 2 == 4
  --   |
  --   +- FalseP i=2: 3 == 4
  --   |
  --   +- TrueP  i=3: 4 == 4
  --   |
  --   +- FalseP i=4: 5 == 4
  --   |
  --   +- FalseP i=5: 6 == 4
  --   |
  --   `- FalseP i=6: 7 == 4
  --   <BLANKLINE>
  --
  PExists     :: (Foldable t, Show a) => Pred z a -> Pred z (t a)

-- get rid of this and use PSeq: too hard to write pzipand in terms of pseq
-- pzipops probably should always be strict! make error configurable: it doesnt even try if not exact
-- strict so if not exact length preds with length as then calls error predicate with those lengths
  -- | matches exact number of predicates with values. see 'PSeq'
  --
  --   >>> pe2' (PZipExact [plift isDigit,plift isAlpha,plift isDigit] 0 1) "9b8"
  --   <BLANKLINE>
  --   TrueP  PZipExact | as="9b8" | (bad,good)=(0,3)
  --   |
  --   `- TrueP  PConst a=[True,True,True]
  --      |
  --      +- TrueP  i=0: PLift | a='9'
  --      |
  --      +- TrueP  i=1: PLift | a='b'
  --      |
  --      `- TrueP  i=2: PLift | a='8'
  --   <BLANKLINE>
  --
  --   >>> pe2' (PZipExact [plift isDigit,plift isAlpha,plift isDigit] 0 1) "9bb"
  --   <BLANKLINE>
  --   TrueP  PZipExact | as="9bb" | (bad,good)=(1,2)
  --   |
  --   `- TrueP  PConst a=[True,True,False]
  --      |
  --      +- TrueP  i=0: PLift | a='9'
  --      |
  --      +- TrueP  i=1: PLift | a='b'
  --      |
  --      `- FalseP i=2: PLift | a='b'
  --   <BLANKLINE>
  --
  --   >>> pe2' (PZipExact [plift isDigit,plift isAlpha,plift isDigit] 0 1) "9b"
  --   <BLANKLINE>
  --   FalseP PZipExact |  length ps 3 /= length as 2
  --   |
  --   `- FalseP PConst a=(3,2)
  --   <BLANKLINE>
  --
  --   >>> :set -XOverloadedStrings
  --   >>> pe2' (PZipExact ["abc",sinfix "xyz"] 0 1) ["AbC", "aaaaxyzbbb"]
  --   <BLANKLINE>
  --   TrueP  PZipExact | as=["AbC","aaaaxyzbbb"] | (bad,good)=(0,2)
  --   |
  --   `- TrueP  PConst a=[True,True]
  --      |
  --      +- TrueP  i=0: PStringCI "AbC" == "abc"
  --      |
  --      `- TrueP  i=1: PStringCI "xyz" `isInfixOf` "aaaaxyzbbb"
  --   <BLANKLINE>
  --
  PZipExact   ::  (Foldable t, Show a) =>
         [Pred z a] -- has to match the number of values in the foldable list
      -> Pred z (Int,Int) -- failure predicate has number of predicates and number of values
      -> Pred z [Bool] -- list of results from zipping predicates and values
      -> Pred z (t a)
  -- similar to the above but gives you the leftovers so doesnt have to be exact
  -- does an element at a time
  -- if you want to grab blocks of stuff at a time then use PRegexs cos then we know how much is consumed
  -- each go: with PSeq it is more limited to a token at a time like PZipExact
  -- | run all the predicates against the values and retain the leftovers
  -- | for a stricter version see 'PZipExact'
  --
  --   >>> :set -XOverloadedStrings
  --   >>> pe2' (PSeq [pregex _d 1] $ PSnd $ PSeq ["DudE","xx"] 1) ["9","dude"]
  --   <BLANKLINE>
  --   TrueP  PSeq | length ps 1 /= length as 2  | as=["9","dude"] | (0,1)
  --   |
  --   `- TrueP  PSnd a=["dude"] fst=[True]
  --      |
  --      +- TrueP  i=0: PRegex RLong as="9" b='9' rs=""
  --      |  |
  --      |  `- TrueP  PConst a=('9',"")
  --      |
  --      `- TrueP  PSeq | length ps 2 /= length as 1  | as=["dude"] | (0,1)
  --         |
  --         `- TrueP  PConst a=([True],[])
  --            |
  --            `- TrueP  i=0: PStringCI "dude" == "DudE"
  --   <BLANKLINE>
  --
  {-   >>> :{
        pe2' (PSeq [peq 1,peq 4] $ PBoth (plift or)
            $ PSeq [peq 111,peq 2] $ PBoth (plift or)
            $ PSeq [peq 11] 1) [2,4,21,111]
           :}
  -}
  --   <BLANKLINE>
  --   FalseP PSeq | length ps 2 /= length as 4  | as=[2,4,21,111] | (1,1)
  --   |
  --   `- FalseP PBoth
  --      |
  --      +- FalseP i=0: 2 == 1
  --      |
  --      +- TrueP  i=1: 4 == 4
  --      |
  --      +- TrueP  PLift | a=[False,True]
  --      |
  --      `- FalseP PSeq | as=[21,111] | (2,0)
  --         |
  --         `- FalseP PBoth
  --            |
  --            +- FalseP i=0: 21 == 111
  --            |
  --            +- FalseP i=1: 111 == 2
  --            |
  --            +- FalseP PLift | a=[False,False]
  --            |
  --            `- TrueP  PSeq | length ps 1 /= length as 0  | as=[] | (0,0)
  --               |
  --               `- TrueP  PConst a=([],[])
  --   <BLANKLINE>
  --
  PSeq        ::  (Foldable t, Show a) =>
          [Pred z a] -- extra predicates are just ignored
        -> Pred z ([Bool],[a]) -- list of results from running the predicates and the leftovers
        -> Pred z (t a)

  -- | 'Data.List.partition' except failures are on the left and successes on the right
  --
  --   >>> pe2' (PPartition peven $ (PFn "***" (sum *** sum)) pgt2) [1..10]
  --   <BLANKLINE>
  --   FalseP PPartition | lefts=5 (0,1) | rights=5 (1,2)
  --   |
  --   +- FalseP PPartition Predicate
  --   |  |
  --   |  `- FalseP PFn *** | a=([1,3,5,7,9],[2,4,6,8,10]) | b=(25,30)
  --   |     |
  --   |     `- FalseP PCmp2 25 > 30
  --   |
  --   `- PPartition debugging info
  --      |
  --      +- FalseP i=0: PLift even | a=1
  --      |
  --      +- TrueP  i=1: PLift even | a=2
  --      |
  --      +- FalseP i=2: PLift even | a=3
  --      |
  --      +- TrueP  i=3: PLift even | a=4
  --      |
  --      +- FalseP i=4: PLift even | a=5
  --      |
  --      +- TrueP  i=5: PLift even | a=6
  --      |
  --      +- FalseP i=6: PLift even | a=7
  --      |
  --      +- TrueP  i=7: PLift even | a=8
  --      |
  --      +- FalseP i=8: PLift even | a=9
  --      |
  --      `- TrueP  i=9: PLift even | a=10
  --   <BLANKLINE>
  --
  --   >>> let xs = [10,3,4,8,7,1,2,3,4,5,6,7,100,220,22]
  --   >>> pe1' (PPartition (pgt 7) $ PBoth (PLen (pgt 3)) (PShow 1 * PIx 4 0 (peq 999))) xs
  --   <BLANKLINE>
  --   FalseP PPartition | lefts=10 (1,3) | rights=5 (0,10)
  --   |
  --   `- FalseP PPartition Predicate
  --      |
  --      `- FalseP PBoth
  --         |
  --         +- TrueP  PLen 10 as=[3,4,7,1,2,3,4,5,6,7]
  --         |  |
  --         |  `- TrueP  10 > 3
  --         |
  --         `- FalseP PAnd
  --            |
  --            +- TrueP  PShow
  --            |  |
  --            |  +- TrueP  PConst a=[10,8,100,220,22]
  --            |  |
  --            |  `- ===== PShow =====
  --            |     |
  --            |     +- i=0 a=10
  --            |     |
  --            |     +- i=1 a=8
  --            |     |
  --            |     +- i=2 a=100
  --            |     |
  --            |     +- i=3 a=220
  --            |     |
  --            |     `- i=4 a=22
  --            |
  --            `- FalseP PIx 4 22
  --               |
  --               `- FalseP 22 == 999
  --   <BLANKLINE>
  --
  --   >>> pe1' (PPartition (pgt 7) 1) [10,3,4,8,7,1,2,3,4,5,6,7,100,220,22]
  --   <BLANKLINE>
  --   TrueP  PPartition | lefts=10 (1,3) | rights=5 (0,10)
  --   |
  --   `- TrueP  PPartition Predicate
  --      |
  --      `- TrueP  PConst a=([3,4,7,1,2,3,4,5,6,7],[10,8,100,220,22])
  --   <BLANKLINE>
  --
  PPartition  :: (Foldable t, Show a) =>
        Pred z a -- run a predicate on each value
     -> Pred z ([a],[a]) -- lhs has list of values that failed the predicate
     -> Pred z (t a)
  -- | see 'Data.List.break'
  --
  --   >>> pe1' (pilist $ PBreak (PSnd (peq 'e')) 1) ['c'..'h']
  --   <BLANKLINE>
  --   TrueP  PBreak | lefts=2 | rights=4 pivot=(2,(2,'e'))
  --   |
  --   `- TrueP  PBreak Predicate
  --      |
  --      `- TrueP  PConst a=([(0,'c'),(1,'d')],[(2,'e'),(3,'f'),(4,'g'),(5,'h')])
  --   <BLANKLINE>
  --
  --   >>> pe2' (PBreak (pgt 4) (PFn "x" (join (***) length) pgt2)) [-1..8]
  --   <BLANKLINE>
  --   TrueP  PBreak | lefts=6 | rights=4 pivot=(6,5)
  --   |
  --   +- TrueP  PBreak Predicate
  --   |  |
  --   |  `- TrueP  PFn x | a=([-1,0,1,2,3,4],[5,6,7,8]) | b=(6,4)
  --   |     |
  --   |     `- TrueP  PCmp2 6 > 4
  --   |
  --   `- PBreak debugging info
  --      |
  --      +- FalseP i=0: -1 > 4
  --      |
  --      +- FalseP i=1: 0 > 4
  --      |
  --      +- FalseP i=2: 1 > 4
  --      |
  --      +- FalseP i=3: 2 > 4
  --      |
  --      +- FalseP i=4: 3 > 4
  --      |
  --      +- FalseP i=5: 4 > 4
  --      |
  --      `- TrueP  i=6: 5 > 4
  --   <BLANKLINE>
  --
  PBreak      :: (Foldable t, Show a) =>
        Pred z a -- run a predicate on each value until predicate succeeds
     -> Pred z ([a],[a])
     -> Pred z (t a)
  -- | see 'Data.List.span'
  PSpan       :: (Foldable t, Show a) =>
        Pred z a -- run a predicate on each value while the predicate succeeds
     -> Pred z ([a],[a])
     -> Pred z (t a)

  -- | json visitor where you determine the targets
  --
  --   see 'matchArrays' 'matchIndex' 'matchNumber' etc
  --
  --   or 'PJsonKey' if matching on key
  --
  --   >>> pe1' (PJson (matchStringP (sinfix "a")) $ psnds $ PShow 1) json1
  --   <BLANKLINE>
  --   TrueP  PJson
  --   |
  --   +- TrueP  PShow
  --   |  |
  --   |  +- TrueP  PConst a=["markup","Standard Generalized Markup Language",...
  --   |  |
  --   |  `- ===== PShow =====
  --   |     |
  --   |     +- i=0 a="markup"
  --   |     |
  --   |     +- i=1 a="Standard Generalized Markup Language"
  --   |     |
  --   |     +- i=2 a="A meta-markup language, used to create markup languages ...
  --   |     |
  --   |     `- i=3 a="example glossary"
  --   |
  --   `- Debugging jpaths
  --      |
  --      +- i=0 | [JPKey "glossary",JPKey "GlossDiv",JPKey "GlossList",JPKey "...
  --      |
  --      +- i=1 | [JPKey "glossary",JPKey "GlossDiv",JPKey "GlossList",JPKey "...
  --      |
  --      +- i=2 | [JPKey "glossary",JPKey "GlossDiv",JPKey "GlossList",JPKey "...
  --      |
  --      `- i=3 | [JPKey "glossary",JPKey "title",JPValue (String "example glo...
  --   <BLANKLINE>
  --
  PJson       :: Show a =>
       ((NonEmpty JPath, Value) -> Maybe a)
    -> Pred z [(NonEmpty JPath, a)] -- list of successful matches
    -> Pred z Value

  -- | matches on the key using the string predicate
  --
  --   >>> :set -XOverloadedStrings
  --   >>> pe1' (PJsonKey "abbrev" (-PNull)) json1
  --   <BLANKLINE>
  --   TrueP  PJsonKey
  --   |
  --   +- TrueP  PNot
  --   |  |
  --   |  `- FalseP PNull length=1 as=[(JPKey "Abbrev" :| [JPKey "GlossEntry",JPKey "Gloss...
  --   |
  --   `- Debugging jpaths
  --      |
  --      `- i=0 | key=Abbrev | [JPKey "glossary",JPKey "GlossDiv",JPKey "GlossList",JPKey...
  --   <BLANKLINE>
  --
  --   >>> let fn = PSnd $ jarray 0 $ PLinear Rigid [preq "c#",preq "haskell", preq "rust"]
  --   >>> pe1' (PJsonKey "langs" (PLen (peq 1) * PHead 0 fn * (psnds $ pone $ jarray 3 $ PShow 1))) json0
  --   <BLANKLINE>
  --   FalseP PJsonKey
  --   |
  --   +- FalseP PAnd
  --   |  |
  --   |  +- FalseP PAnd
  --   |  |  |
  --   |  |  +- TrueP  PLen 1 as=[(JPKey "langs" :| [],Array [String "c#",String "rusxt",String "haskell"])]
  --   |  |  |  |
  --   |  |  |  `- TrueP  1 == 1
  --   |  |  |
  --   |  |  `- FalseP PHead (JPKey "langs" :| [],Array [String "c#",String "rusxt",String "haskell"])
  --   |  |     |
  --   |  |     `- FalseP PSnd a=Array [String "c#",String "rusxt",String "haskell"] fst=JPKey "langs" :| []
  --   |  |        |
  --   |  |        `- FalseP PPrism (Just) [jarray] [String "c#",String "rusxt",String "haskell"]
  --   |  |           |
  --   |  |           `- FalseP PLinear Failed Pred [Int] | errors(1): NoMatch 1
  --   |  |              |
  --   |  |              +- FalseP Predicates | PZipAnd | PZipExact | (bad,good)=(1,2)
  --   |  |              |  |
  --   |  |              |  `- FalseP PLift and | a=[True,True,False]
  --   |  |              |     |
  --   |  |              |     +- TrueP  i=0
  --   |  |              |     |  |
  --   |  |              |     |  +- TrueP  1 == 1
  --   |  |              |     |  |
  --   |  |              |     |  `- PStringCI a == String "c#"
  --   |  |              |     |
  --   |  |              |     +- TrueP  i=1
  --   |  |              |     |  |
  --   |  |              |     |  +- TrueP  1 == 1
  --   |  |              |     |  |
  --   |  |              |     |  `- PStringCI a == String "haskell"
  --   |  |              |     |
  --   |  |              |     `- FalseP i=2
  --   |  |              |        |
  --   |  |              |        +- FalseP 0 < 1 (Under)
  --   |  |              |        |
  --   |  |              |        `- PStringCI a == String "rust"
  --   |  |              |
  --   |  |              +- TrueP  PLinear | OneMatch 0 a=String "c#" cnt=1 (i=0, a=String "c#")
  --   |  |              |  |
  --   |  |              |  +- TrueP  i=0: PStringCI String "c#" == String "c#"
  --   |  |              |  |
  --   |  |              |  +- FalseP i=1: PStringCI String "c#" == String "haskell"
  --   |  |              |  |
  --   |  |              |  `- FalseP i=2: PStringCI String "c#" == String "rust"
  --   |  |              |
  --   |  |              +- FalseP PLinear NoMatch 1 a=String "rusxt"
  --   |  |              |  |
  --   |  |              |  +- FalseP i=0: PStringCI String "rusxt" == String "c#"
  --   |  |              |  |
  --   |  |              |  +- FalseP i=1: PStringCI String "rusxt" == String "haskell"
  --   |  |              |  |
  --   |  |              |  `- FalseP i=2: PStringCI String "rusxt" == String "rust"
  --   |  |              |
  --   |  |              `- TrueP  PLinear | OneMatch 2 a=String "haskell" cnt=1 (i=1, a=String "haskell")
  --   |  |                 |
  --   |  |                 +- FalseP i=0: PStringCI String "haskell" == String "c#"
  --   |  |                 |
  --   |  |                 +- TrueP  i=1: PStringCI String "haskell" == String "haskell"
  --   |  |                 |
  --   |  |                 `- FalseP i=2: PStringCI String "haskell" == String "rust"
  --   |  |
  --   |  `- TrueP  POne Array [String "c#",String "rusxt",String "haskell"]
  --   |     |
  --   |     `- TrueP  PPrism (Just) [jarray] [String "c#",String "rusxt",String "haskell"]
  --   |        |
  --   |        `- TrueP  PShow
  --   |           |
  --   |           +- TrueP  PConst a=[String "c#",String "rusxt",String "haskell"]
  --   |           |
  --   |           `- ===== PShow =====
  --   |              |
  --   |              +- i=0 a=String "c#"
  --   |              |
  --   |              +- i=1 a=String "rusxt"
  --   |              |
  --   |              `- i=2 a=String "haskell"
  --   |
  --   `- Debugging jpaths
  --      |
  --      `- i=0 | key=langs | [JPKey "langs"]
  --   <BLANKLINE>
  --
  --   >>> :set -XOverloadedStrings
  --   >>> let xx = jarray 0 $ PLinear Rigid [preq "xml",preq "gml",preq "abc"]
  --   >>> pe1' (PJsonKey (sinfix "seealso") $ psnds $ PHead 0 xx) json1
  --   <BLANKLINE>
  --   FalseP PJsonKey
  --   |
  --   +- FalseP PHead Array [String "GML",String "XML"]
  --   |  |
  --   |  `- FalseP PPrism (Just) [jarray] [String "GML",String "XML"]
  --   |     |
  --   |     `- FalseP PLinear Failed Pred [Int]
  --   |        |
  --   |        +- FalseP Predicates | PZipAnd | PZipExact | (bad,good)=(1,2)
  --   |        |  |
  --   |        |  `- FalseP PLift and | a=[True,True,False]
  --   |        |     |
  --   |        |     +- TrueP  i=0
  --   |        |     |  |
  --   |        |     |  +- TrueP  1 == 1
  --   |        |     |  |
  --   |        |     |  `- PStringCI a == String "xml"
  --   |        |     |
  --   |        |     +- TrueP  i=1
  --   |        |     |  |
  --   |        |     |  +- TrueP  1 == 1
  --   |        |     |  |
  --   |        |     |  `- PStringCI a == String "gml"
  --   |        |     |
  --   |        |     `- FalseP i=2
  --   |        |        |
  --   |        |        +- FalseP 0 < 1 (Under)
  --   |        |        |
  --   |        |        `- PStringCI a == String "abc"
  --   |        |
  --   |        +- TrueP  PLinear | OneMatch 0 a=String "GML" cnt=1 (i=1, a=String "GML")
  --   |        |  |
  --   |        |  +- FalseP i=0: PStringCI String "GML" == String "xml"
  --   |        |  |
  --   |        |  +- TrueP  i=1: PStringCI String "GML" == String "gml"
  --   |        |  |
  --   |        |  `- FalseP i=2: PStringCI String "GML" == String "abc"
  --   |        |
  --   |        `- TrueP  PLinear | OneMatch 1 a=String "XML" cnt=1 (i=0, a=String "XML")
  --   |           |
  --   |           +- TrueP  i=0: PStringCI String "XML" == String "xml"
  --   |           |
  --   |           +- FalseP i=1: PStringCI String "XML" == String "gml"
  --   |           |
  --   |           `- FalseP i=2: PStringCI String "XML" == String "abc"
  --   |
  --   `- Debugging jpaths
  --      |
  --      `- i=0 | key=GlossSeeAlso | [JPKey "glossary",JPKey "GlossDiv",JPKey "GlossList"...
  --   <BLANKLINE>
  --
  PJsonKey    ::
       Pred z String
    -> Pred z [(NonEmpty JPath, Value)] -- list of successful matches
    -> Pred z Value


  -- PJsonP creates a nested tree until it stops or is successful with 'Value' at then end
  -- | given a json path will get the json value at that path
  --
  --   >>> :set -XOverloadedStrings
  --   >>> pe1' (PJsonP [JPIndex 2,JPKey "age",JPValue (Number 33),JPValue ""] 0 1) json2
  --   <BLANKLINE>
  --   FalseP PJsonP path=nth 2.key "age"._Number._String
  --   |
  --   +- FalseP Number 33.0 /= Number 45.0 | matched up to=nth 2.key "age" | PConst a=()
  --   |
  --   `- nth 2 | value=Object (fromList [("lastName",String "Doe"),("age",Number 45.0),("firstName",...
  --      |
  --      `- key "age" | value=Number 45.0
  --         |
  --         `- match failed on _Number | Number 33.0 /= Number 45.0 | partial match=nth 2.key "age"
  --   <BLANKLINE>
  --
  --   >>> let zzz = [JPKey "glossary",JPKey "GlossDiv",JPKey "GlossList",JPKey "GlossEntry",JPKey "GlossDef",JPKey "para"]
  --   >>> pe' (PJsonP zzz 0 $ PString CI SInfix "docbook") json1
  --   <BLANKLINE>
  --   TrueP  PJsonP
  --   |
  --   +- TrueP  matched | PStringCI String "docbook" `isInfixOf` String "A meta-markup...
  --   |
  --   `- key "glossary"
  --      |
  --      `- key "GlossDiv"
  --         |
  --         `- key "GlossList"
  --            |
  --            `- key "GlossEntry"
  --               |
  --               `- key "GlossDef"
  --                  |
  --                  `- key "para"
  --                     |
  --                     `- TrueP  matched complete path
  --   <BLANKLINE>
  --
  --   >>> let zzz = map JPKey ["glossary","GlossDiv","GlossList","GlossEntry","GlossTerm"]
  --   >>> pe' (PJsonP zzz 0 $ PShow1 $ sinfix "marku" * ssuffix "uaxge") json1
  --   <BLANKLINE>
  --   FalseP PJsonP
  --   |
  --   +- FalseP matched | PShow1
  --   |  |
  --   |  +- FalseP PAnd
  --   |  |  |
  --   |  |  +- TrueP  PStringCI String "marku" `isInfixOf` String "Standard Generalized Markup Language"
  --   |  |  |
  --   |  |  `- FalseP PStringCI String "uaxge" `isSuffixOf` String "Standard Generalized Markup Language"
  --   |  |
  --   |  `- a=String "Standard Generalized Markup Language"
  --   |
  --   `- key "glossary"
  --      |
  --      `- key "GlossDiv"
  --         |
  --         `- key "GlossList"
  --            |
  --            `- key "GlossEntry"
  --               |
  --               `- key "GlossTerm"
  --                  |
  --                  `- TrueP  matched complete path
  --   <BLANKLINE>
  --
  --   >>> pe' (PJsonP [JPIndex 2] 0 $ jobjectList 0 $ PShow 1) json2
  --   <BLANKLINE>
  --   TrueP  PJsonP
  --   |
  --   +- TrueP  matched | PPrism (Just) [jobjectList]
  --   |  |
  --   |  `- TrueP  PShow
  --   |     |
  --   |     +- TrueP
  --   |     |
  --   |     `- ===== PShow =====
  --   |        |
  --   |        +- i=0 a=("lastName",String "Doe")
  --   |        |
  --   |        +- i=1 a=("age",Number 45.0)
  --   |        |
  --   |        +- i=2 a=("firstName",String "John")
  --   |        |
  --   |        `- i=3 a=("likesPizza",Bool False)
  --   |
  --   `- nth 2
  --      |
  --      `- TrueP  matched complete path
  --   <BLANKLINE>
  --
  PJsonP      :: [JPath] -- list of jpaths to get you to the json 'Value'
              -> Pred z () -- failure predicate ie no match
              -> Pred z Value  -- success predicate
              -> Pred z Value

-- only used by PredState -- else wrapped with plog/pstate not implemented
  -- | passthrough predicate which allows you to log using current value and state
  --
  --   >>> :set -XTypeApplications
  --   >>> import Data.Semigroup (Sum(..))
  --   >>> pe2' (PLog (These show show) $ PForAll (PState @(Sum _) (That (<>)) 1)) [1,5,3,7]
  --   <BLANKLINE>
  --   TrueP  PLog-+ a=[Sum {getSum = 1},Sum {getSum = 5},Sum {getSum = 3},Sum {getSum = 7}]
  --   |
  --   +- PLog- ([Sum {getSum = 1},Sum {getSum = 5},Sum {getSum = 3},Sum {getSum = 7}],Sum {getSum = 0}) state=Sum {getSum = 0}
  --   |
  --   +- TrueP  PForAll
  --   |  |
  --   |  +- TrueP  i=0: PState+ a=Sum {getSum = 1}
  --   |  |  |
  --   |  |  +- TrueP  PConst a=Sum {getSum = 1}
  --   |  |  |
  --   |  |  `- PState+ old state=Sum {getSum = 0} new state=Sum {getSum = 1}
  --   |  |
  --   |  +- TrueP  i=1: PState+ a=Sum {getSum = 5}
  --   |  |  |
  --   |  |  +- TrueP  PConst a=Sum {getSum = 5}
  --   |  |  |
  --   |  |  `- PState+ old state=Sum {getSum = 1} new state=Sum {getSum = 6}
  --   |  |
  --   |  +- TrueP  i=2: PState+ a=Sum {getSum = 3}
  --   |  |  |
  --   |  |  +- TrueP  PConst a=Sum {getSum = 3}
  --   |  |  |
  --   |  |  `- PState+ old state=Sum {getSum = 6} new state=Sum {getSum = 9}
  --   |  |
  --   |  `- TrueP  i=3: PState+ a=Sum {getSum = 7}
  --   |     |
  --   |     +- TrueP  PConst a=Sum {getSum = 7}
  --   |     |
  --   |     `- PState+ old state=Sum {getSum = 9} new state=Sum {getSum = 16}
  --   |
  --   `- PLog+ ([Sum {getSum = 1},Sum {getSum = 5},Sum {getSum = 3},Sum {getSum = 7}],Sum {getSum = 16}) state=Sum {getSum = 16}
  --   <BLANKLINE>
  --
  --   >>> pe2' (PLog (These (("LHS:"++) . show) (("RHS:"++).show)) 1) ()
  --   <BLANKLINE>
  --   TrueP  PLog-+ a=()
  --   |
  --   +- PLog- LHS:((),()) state=()
  --   |
  --   +- TrueP  PConst a=()
  --   |
  --   `- PLog+ RHS:((),()) state=()
  --   <BLANKLINE>
  --
  --   >>> pe2' (PLog (This (("LHS:"++) . show)) 1) ()
  --   <BLANKLINE>
  --   TrueP  PLog- a=()
  --   |
  --   +- PLog- LHS:((),()) state=()
  --   |
  --   `- TrueP  PConst a=()
  --   <BLANKLINE>
  --
  --   >>> pe2' (PLog (That (("RHS:"++) . show)) 1) ()
  --   <BLANKLINE>
  --   TrueP  PLog+ a=()
  --   |
  --   +- TrueP  PConst a=()
  --   |
  --   `- PLog+ RHS:((),()) state=()
  --   <BLANKLINE>
  --
  PLog :: (Show a, Show z) => These ((a, z) -> String) ((a, z) -> String) -> Pred z a -> Pred z a
  -- does logging before running the predicate
  -- | passthrough predicate which allows you to modify state using the current value and state
  --
  --   >>> import Data.Semigroup (Sum(..))
  --   >>> pe1' (PState (These (<>) (<>)) 1) (Sum 4)
  --   <BLANKLINE>
  --   TrueP  PState-+ a=Sum {getSum = 4}
  --   |
  --   +- PState- old state=Sum {getSum = 0} new state=Sum {getSum = 4}
  --   |
  --   +- TrueP  PConst a=Sum {getSum = 4}
  --   |
  --   `- PState+ old state=Sum {getSum = 4} new state=Sum {getSum = 8}
  --   <BLANKLINE>
  --
  --   >>> import Data.Semigroup (Sum(..))
  --   >>> pe1' (pput (Sum 14) $ PState (These (<>) (<>)) 1) 4
  --   <BLANKLINE>
  --   TrueP  PState- a=Sum {getSum = 4}
  --   |
  --   +- PState- old state=Sum {getSum = 0} new state=Sum {getSum = 14}
  --   |
  --   `- TrueP  PState-+ a=Sum {getSum = 4}
  --      |
  --      +- PState- old state=Sum {getSum = 14} new state=Sum {getSum = 18}
  --      |
  --      +- TrueP  PConst a=Sum {getSum = 4}
  --      |
  --      `- PState+ old state=Sum {getSum = 18} new state=Sum {getSum = 22}
  --   <BLANKLINE>
  --
  --   >>> import Data.Semigroup (Sum(..))
  --   >>> pe1' (PState (These (const2 (Sum 19)) (<>)) $ PLog (These show show) 1) 14
  --   <BLANKLINE>
  --   TrueP  PState-+ a=Sum {getSum = 14}
  --   |
  --   +- PState- old state=Sum {getSum = 0} new state=Sum {getSum = 19}
  --   |
  --   +- TrueP  PLog-+ a=Sum {getSum = 14}
  --   |  |
  --   |  +- PLog- (Sum {getSum = 14},Sum {getSum = 19}) state=Sum {getSum = 19}
  --   |  |
  --   |  +- TrueP  PConst a=Sum {getSum = 14}
  --   |  |
  --   |  `- PLog+ (Sum {getSum = 14},Sum {getSum = 19}) state=Sum {getSum = 19}
  --   |
  --   `- PState+ old state=Sum {getSum = 19} new state=Sum {getSum = 33}
  --   <BLANKLINE>
  --
  PState :: (Show a, Show z) => These (a -> z -> z) (a -> z -> z) -> Pred z a -> Pred z a
  -- | decorate predicate with current state
  PGet   :: (Show a, Show z) => Pred z (z,a) -> Pred z a
{-
  -- | set the state
  --
  --   >>> import Data.Semigroup (Sum(..))
  --   >>> pe1' (PPut (Sum 4) * PGet (PFst (pgt 4))) ()
  --   <BLANKLINE>
  --   FalseP PAnd
  --   |
  --   +- TrueP  PPut a=() oldstate=Sum {getSum = 0}
  --   |
  --   `- FalseP PGet a=() state=Sum {getSum = 4}
  --      |
  --      `- FalseP PFst a=Sum {getSum = 4} snd=()
  --         |
  --         `- FalseP Sum {getSum = 4} > Sum {getSum = 4}
  --   <BLANKLINE>
  --
  --   >>> import Data.Semigroup (Sum(..))
  --   >>> pe1' (PPut (Sum 4) * PGet (PFst (pgt 3))) ()
  --   <BLANKLINE>
  --   TrueP  PAnd
  --   |
  --   +- TrueP  PPut a=() oldstate=Sum {getSum = 0}
  --   |
  --   `- TrueP  PGet a=() state=Sum {getSum = 4}
  --      |
  --      `- TrueP  PFst a=Sum {getSum = 4} snd=()
  --         |
  --         `- TrueP  Sum {getSum = 4} > Sum {getSum = 3}
  --   <BLANKLINE>
  --
  PPut   :: (Eq z, Show a, Show z) => z -> Pred z a
-}
-- | equivalent to take using 'PSplitAt' but using one side of the tuple
ptake, pdrop :: (Foldable t, Show a) => Int -> Pred z [a] -> Pred z (t a)
ptake i = PMsg Inline "PTake" . PSplitAt i . phide . PFst
pdrop i = PMsg Inline "PDrop" . PSplitAt i . phide . PSnd

-- not sure how useful this is? can use PIx to get at particular keyvalues or can just pilist to get it as a big list of tuples
-- | convert a predicate on a foldable to predicate on a map grouped by key
--
--   >>> pe2' (pgroup (between 3 7) $ PIx GT 0 1) [11,5,2,4,12]
--   <BLANKLINE>
--   TrueP  PFn pgroup | a=[11,5,2,4,12] | b=fromList [(LT,[2]),(EQ,[5,4]),(GT,[11,12])]
--   |
--   `- TrueP  PIx GT [11,12]
--      |
--      `- TrueP  PConst a=[11,12]
--   <BLANKLINE>
--
--   >>> pe2' (pgroup (between 3 7) $ PIx EQ 0 $ PLen (peq 2)) [11,5,2,4,12,14,11,11,12]
--   <BLANKLINE>
--   TrueP  PFn pgroup | a=[11,5,2,4,12,14,11,11,12] | b=fromList [(LT,[2]),(EQ,[5,4]),(GT,[11,12,14,11,11,12])]
--   |
--   `- TrueP  PIx EQ [5,4]
--      |
--      `- TrueP  PLen 2 as=[5,4]
--         |
--         `- TrueP  2 == 2
--   <BLANKLINE>
--
--   >>> pe2' (pgroup (between 3 7) $ PIx GT 0 $ PLen (peq 2)) [11,5,2,4,12,14,11,11,12]
--   <BLANKLINE>
--   FalseP PFn pgroup | a=[11,5,2,4,12,14,11,11,12] | b=fromList [(LT,[2]),(EQ,[5,4])...
--   |
--   `- FalseP PIx GT [11,12,14,11,11,12]
--      |
--      `- FalseP PLen 6 as=[11,12,14,11,11,12]
--         |
--         `- FalseP 6 == 2
--   <BLANKLINE>
--
--   >>> pe2' (pgroup (compare 'd') (PIx GT 0 (PLen (peq 4)))) ("adcxdza"::String)
--   <BLANKLINE>
--   FalseP PFn pgroup | a="adcxdza" | b=fromList [(LT,"xz"),(EQ,"dd"),(GT,"aca")]
--   |
--   `- FalseP PIx GT "aca"
--      |
--      `- FalseP PLen 3 as="aca"
--         |
--         `- FalseP 3 == 4
--   <BLANKLINE>
--
--   >>> pe2' (pgroup (compare 'd') (PIx EQ 0 (PLen (peq 4)))) ("adcxdza"::String)
--   <BLANKLINE>
--   FalseP PFn pgroup | a="adcxdza" | b=fromList [(LT,"xz"),(EQ,"dd"),(GT,"aca")]
--   |
--   `- FalseP PIx EQ "dd"
--      |
--      `- FalseP PLen 2 as="dd"
--         |
--         `- FalseP 2 == 4
--   <BLANKLINE>
--
--   >>> pe2' (pgroup (compare 'd') (PIx EQ 0 (PLen (peq 2)))) ("adcxdza"::String)
--   <BLANKLINE>
--   TrueP  PFn pgroup | a="adcxdza" | b=fromList [(LT,"xz"),(EQ,"dd"),(GT,"aca")]
--   |
--   `- TrueP  PIx EQ "dd"
--      |
--      `- TrueP  PLen 2 as="dd"
--         |
--         `- TrueP  2 == 2
--   <BLANKLINE>
--
pgroup :: (Foldable t, Show k, Ord k, Show a) => (a -> k) -> Pred z (Map k [a]) -> Pred z (t a)
pgroup ak = PFn "pgroup" (M.fromListWith (flip (<>)) . map (ak &&& (:[])) . toList)

pgroupBetween :: (Foldable t, Show a, Ord a) => a -> a -> Pred z (Map Ordering [a]) -> Pred z (t a)
pgroupBetween a b = pgroup (between a b)

pgroupEq :: (Foldable t, Show k, Eq k, Hashable k, Show a) => (a -> k) -> Pred z (HashMap k [a]) -> Pred z (t a)
pgroupEq ak = PFn "pgroupEq" (H.fromListWith (flip (<>)) . map (ak &&& (:[])) . toList)

-- uses my groupBy' which behaves more consistently than Data.List
-- Data.List.groupBy grabs first value and compares that with a span of stuff
-- instead of comparing each consecutive pair
-- eg groupBy (>=)
{-
>groupBy' (<=) [1,3,5,2,4]
[[1,3,5],[2,4]]
>groupBy (<=) [1,3,5,2,4]
[[1,3,5,2,4]]
-}

-- this is useful can emulate POrder and more eg pgroupBy ((==) . succ) off by exactly one or pgroupBy (on (==) even odd) xor on evenness
-- | a better 'groupBy' that checks adjacent elements. good replacement and more powerful version of 'POrder'
--
--   >>> pe2' (pgroupBy (<=) $ PLen $ plt 3) [1,4,5,7,11,3,4]
--   <BLANKLINE>
--   TrueP  PFn pgroupBy | a=[1,4,5,7,11,3,4] | b=[[1,4,5,7,11],[3,4]]
--   |
--   `- TrueP  PLen 2 as=[[1,4,5,7,11],[3,4]]
--      |
--      `- TrueP  2 < 3
--   <BLANKLINE>
--
--   >>> pe2' (pgroupBy (on (/=) even) 1) [1,4,5,10,11,9]
--   <BLANKLINE>
--   TrueP  PFn pgroupBy | a=[1,4,5,10,11,9] | b=[[1,4,5,10,11],[9]]
--   |
--   `- TrueP  PConst a=[[1,4,5,10,11],[9]]
--   <BLANKLINE>
--
--   >>> pe2' (pgroupBy ((((<=2) . abs) .) . subtract) 1) [1,4,5,7,11,9]
--   <BLANKLINE>
--   TrueP  PFn pgroupBy | a=[1,4,5,7,11,9] | b=[[1],[4,5,7],[11,9]]
--   |
--   `- TrueP  PConst a=[[1],[4,5,7],[11,9]]
--   <BLANKLINE>
--
--   >>> pe2' (pgroupBy (<) $ PLen (pgt 2) * PHead 0 (PLen $ pgt 6)) [1,3,4,6,6,9,3,4]
--   <BLANKLINE>
--   FalseP PFn pgroupBy | a=[1,3,4,6,6,9,3,4] | b=[[1,3,4,6],[6,9],[3,4]]
--   |
--   `- FalseP PAnd
--      |
--      +- TrueP  PLen 3 as=[[1,3,4,6],[6,9],[3,4]]
--      |  |
--      |  `- TrueP  3 > 2
--      |
--      `- FalseP PHead [1,3,4,6]
--         |
--         `- FalseP PLen 4 as=[1,3,4,6]
--            |
--            `- FalseP 4 > 6
--   <BLANKLINE>
--
--   >>> pe1' (pgroupBy (<=) 1) ([1..10] ++ [1..4] ++ [1..6])
--   <BLANKLINE>
--   TrueP  PFn pgroupBy | a=[1,2,3,4,5,6,7,8,9,10,1,2,3,4,1,2,3,4,5,6] | b=[[1,2,3,4,5,6,7,8,9,10],[1,2,3,4],[1,2,3,4,5,6]]
--   |
--   `- TrueP  PConst a=[[1,2,3,4,5,6,7,8,9,10],[1,2,3,4],[1,2,3,4,5,6]]
--   <BLANKLINE>
--
pgroupBy :: (Foldable t, Show a) => (a -> a -> Bool) -> Pred z [[a]] -> Pred z (t a)
pgroupBy f = PFn "pgroupBy" (groupBy' f . toList)

--pthese :: (Foldable t, Show a, Show b) => Pred z ([a],[b]) -> Pred z (t (Either a b))
--pthese = PFn "pthese" (mconcat . map (either (\a -> ([a],[])) (\b -> ([],[b]))) . toList)

-- with pilist we can do any PI* stuff pilist $ PBreak becomes PIBreak and same with PLinear/PPartition/PForAll/PExists
-- this is very useful: adds an index to any normal list too! ie zip [0..]
-- | lifts 'itoList' into a predicate
pilist :: (FoldableWithIndex i f, Show a, Show i) => Pred z [(i, a)] -> Pred z (f a)
pilist = phide . PFn "itoList" itoList


-- | logging
--
--   >>> import Data.Semigroup (Sum(..))
--   >>> pe1' (plog show $ PState (That ((+) . Sum . sum)) $ PPartition peven 1) [1..10]
--   <BLANKLINE>
--   TrueP  PLog-+ a=[1,2,3,4,5,6,7,8,9,10]
--   |
--   +- PLog- ([1,2,3,4,5,6,7,8,9,10],Sum {getSum = 0}) state=Sum {getSum = 0}
--   |
--   +- TrueP  PState+ a=[1,2,3,4,5,6,7,8,9,10]
--   |  |
--   |  +- TrueP  PPartition | lefts=5 (0,1) | rights=5 (1,2)
--   |  |  |
--   |  |  `- TrueP  PPartition Predicate
--   |  |     |
--   |  |     `- TrueP  PConst a=([1,3,5,7,9],[2,4,6,8,10])
--   |  |
--   |  `- PState+ old state=Sum {getSum = 0} new state=Sum {getSum = 55}
--   |
--   `- PLog+ ([1,2,3,4,5,6,7,8,9,10],Sum {getSum = 55}) state=Sum {getSum = 55}
--   <BLANKLINE>
--
--   >>> import Data.Semigroup (Sum(..))
--   >>> pe3' (plog show $ PState (That ((+) . Sum . sum)) $ PPartition peven 1) [1..10]
--   <BLANKLINE>
--   TrueP  PLog-+ a=[1,2,3,4,5,6,7,8,9,10]
--   |
--   +- PLog- ([1,2,3,4,5,6,7,8,9,10],Sum {getSum = 0}) state=Sum {getSum = 0}
--   |
--   +- TrueP  PState+ a=[1,2,3,4,5,6,7,8,9,10]
--   |  |
--   |  +- TrueP  PPartition | lefts=5 (0,1) | rights=5 (1,2)
--   |  |  |
--   |  |  +- TrueP  PPartition Predicate
--   |  |  |  |
--   |  |  |  `- TrueP  PConst a=([1,3,5,7,9],[2,4,6,8,10])
--   |  |  |
--   |  |  `- PPartition debugging info
--   |  |     |
--   |  |     +- FalseP i=0: PLift even | a=1
--   |  |     |
--   |  |     +- TrueP  i=1: PLift even | a=2
--   |  |     |
--   |  |     +- FalseP i=2: PLift even | a=3
--   |  |     |
--   |  |     +- TrueP  i=3: PLift even | a=4
--   |  |     |
--   |  |     +- FalseP i=4: PLift even | a=5
--   |  |     |
--   |  |     +- TrueP  i=5: PLift even | a=6
--   |  |     |
--   |  |     +- FalseP i=6: PLift even | a=7
--   |  |     |
--   |  |     +- TrueP  i=7: PLift even | a=8
--   |  |     |
--   |  |     +- FalseP i=8: PLift even | a=9
--   |  |     |
--   |  |     `- TrueP  i=9: PLift even | a=10
--   |  |
--   |  `- PState+ old state=Sum {getSum = 0} new state=Sum {getSum = 55}
--   |
--   `- PLog+ ([1,2,3,4,5,6,7,8,9,10],Sum {getSum = 55}) state=Sum {getSum = 55}
--   <BLANKLINE>
--   Config {_cLog = fromList ["-([1,2,3,4,5,6,7,8,9,10],Sum {getSum = 0})","+([1,2,3,4,5,6,7,8,9,10],Sum {getSum = 55})"], _cZ = Sum {getSum = 55}, _cCnt = fromList [("PConst",1),("PLift even",10),("PLog-+",1),("PPartition",1),("PState+",1)]}
--
plog, plogA, plogB :: (Show z, Show a) => ((a, z) -> String) -> Pred z a -> Pred z a
plog f = PLog (These f f)
plogB = PLog . This
plogA = PLog . That

pstateB, pstateA :: (Show z, Show a) => (a -> z -> z) -> Pred z a -> Pred z a
pstateB = PState . This
pstateA = PState . That
pstateBA :: (Show z, Show a) => (a -> z -> z) -> (a -> z -> z) -> Pred z a -> Pred z a
pstateBA = (PState .) . These

-- | set the state
--
--   >>> import Data.Semigroup (Sum(..))
--   >>> pe1' (pput (Sum 19) $ PState (That (<>)) $ PLog (These show show) 1) 14
--   <BLANKLINE>
--   TrueP  PState- a=Sum {getSum = 14}
--   |
--   +- PState- old state=Sum {getSum = 0} new state=Sum {getSum = 19}
--   |
--   `- TrueP  PState+ a=Sum {getSum = 14}
--      |
--      +- TrueP  PLog-+ a=Sum {getSum = 14}
--      |  |
--      |  +- PLog- (Sum {getSum = 14},Sum {getSum = 19}) state=Sum {getSum = 19}
--      |  |
--      |  +- TrueP  PConst a=Sum {getSum = 14}
--      |  |
--      |  `- PLog+ (Sum {getSum = 14},Sum {getSum = 19}) state=Sum {getSum = 19}
--      |
--      `- PState+ old state=Sum {getSum = 19} new state=Sum {getSum = 33}
--   <BLANKLINE>
--
--   >>> pe1' (pput (Sum 19) $ PForAll (PState (That (<>)) $ PLog (These show show) 1)) (map Sum [7,24,3,1,-8])
--   <BLANKLINE>
--   TrueP  PState- a=[Sum {getSum = 7},Sum {getSum = 24},Sum {getSum = 3},Sum {getSum = 1},Sum {getSum = -8}]
--   |
--   +- PState- old state=Sum {getSum = 0} new state=Sum {getSum = 19}
--   |
--   `- TrueP  PForAll
--      |
--      +- TrueP  i=0: PState+ a=Sum {getSum = 7}
--      |  |
--      |  +- TrueP  PLog-+ a=Sum {getSum = 7}
--      |  |  |
--      |  |  +- PLog- (Sum {getSum = 7},Sum {getSum = 19}) state=Sum {getSum = 19}
--      |  |  |
--      |  |  +- TrueP  PConst a=Sum {getSum = 7}
--      |  |  |
--      |  |  `- PLog+ (Sum {getSum = 7},Sum {getSum = 19}) state=Sum {getSum = 19}
--      |  |
--      |  `- PState+ old state=Sum {getSum = 19} new state=Sum {getSum = 26}
--      |
--      +- TrueP  i=1: PState+ a=Sum {getSum = 24}
--      |  |
--      |  +- TrueP  PLog-+ a=Sum {getSum = 24}
--      |  |  |
--      |  |  +- PLog- (Sum {getSum = 24},Sum {getSum = 26}) state=Sum {getSum = 26}
--      |  |  |
--      |  |  +- TrueP  PConst a=Sum {getSum = 24}
--      |  |  |
--      |  |  `- PLog+ (Sum {getSum = 24},Sum {getSum = 26}) state=Sum {getSum = 26}
--      |  |
--      |  `- PState+ old state=Sum {getSum = 26} new state=Sum {getSum = 50}
--      |
--      +- TrueP  i=2: PState+ a=Sum {getSum = 3}
--      |  |
--      |  +- TrueP  PLog-+ a=Sum {getSum = 3}
--      |  |  |
--      |  |  +- PLog- (Sum {getSum = 3},Sum {getSum = 50}) state=Sum {getSum = 50}
--      |  |  |
--      |  |  +- TrueP  PConst a=Sum {getSum = 3}
--      |  |  |
--      |  |  `- PLog+ (Sum {getSum = 3},Sum {getSum = 50}) state=Sum {getSum = 50}
--      |  |
--      |  `- PState+ old state=Sum {getSum = 50} new state=Sum {getSum = 53}
--      |
--      +- TrueP  i=3: PState+ a=Sum {getSum = 1}
--      |  |
--      |  +- TrueP  PLog-+ a=Sum {getSum = 1}
--      |  |  |
--      |  |  +- PLog- (Sum {getSum = 1},Sum {getSum = 53}) state=Sum {getSum = 53}
--      |  |  |
--      |  |  +- TrueP  PConst a=Sum {getSum = 1}
--      |  |  |
--      |  |  `- PLog+ (Sum {getSum = 1},Sum {getSum = 53}) state=Sum {getSum = 53}
--      |  |
--      |  `- PState+ old state=Sum {getSum = 53} new state=Sum {getSum = 54}
--      |
--      `- TrueP  i=4: PState+ a=Sum {getSum = -8}
--         |
--         +- TrueP  PLog-+ a=Sum {getSum = -8}
--         |  |
--         |  +- PLog- (Sum {getSum = -8},Sum {getSum = 54}) state=Sum {getSum = 54}
--         |  |
--         |  +- TrueP  PConst a=Sum {getSum = -8}
--         |  |
--         |  `- PLog+ (Sum {getSum = -8},Sum {getSum = 54}) state=Sum {getSum = 54}
--         |
--         `- PState+ old state=Sum {getSum = 54} new state=Sum {getSum = 46}
--   <BLANKLINE>
--
--   >>> pe1' (pput [999] $ PForAll (PState (That (flip (<>) . (:[]))) $ PLog (These show show) 1)) [7,24,3,1,-8]
--   <BLANKLINE>
--   TrueP  PState- a=[7,24,3,1,-8]
--   |
--   +- PState- old state=[] new state=[999]
--   |
--   `- TrueP  PForAll
--      |
--      +- TrueP  i=0: PState+ a=7
--      |  |
--      |  +- TrueP  PLog-+ a=7
--      |  |  |
--      |  |  +- PLog- (7,[999]) state=[999]
--      |  |  |
--      |  |  +- TrueP  PConst a=7
--      |  |  |
--      |  |  `- PLog+ (7,[999]) state=[999]
--      |  |
--      |  `- PState+ old state=[999] new state=[999,7]
--      |
--      +- TrueP  i=1: PState+ a=24
--      |  |
--      |  +- TrueP  PLog-+ a=24
--      |  |  |
--      |  |  +- PLog- (24,[999,7]) state=[999,7]
--      |  |  |
--      |  |  +- TrueP  PConst a=24
--      |  |  |
--      |  |  `- PLog+ (24,[999,7]) state=[999,7]
--      |  |
--      |  `- PState+ old state=[999,7] new state=[999,7,24]
--      |
--      +- TrueP  i=2: PState+ a=3
--      |  |
--      |  +- TrueP  PLog-+ a=3
--      |  |  |
--      |  |  +- PLog- (3,[999,7,24]) state=[999,7,24]
--      |  |  |
--      |  |  +- TrueP  PConst a=3
--      |  |  |
--      |  |  `- PLog+ (3,[999,7,24]) state=[999,7,24]
--      |  |
--      |  `- PState+ old state=[999,7,24] new state=[999,7,24,3]
--      |
--      +- TrueP  i=3: PState+ a=1
--      |  |
--      |  +- TrueP  PLog-+ a=1
--      |  |  |
--      |  |  +- PLog- (1,[999,7,24,3]) state=[999,7,24,3]
--      |  |  |
--      |  |  +- TrueP  PConst a=1
--      |  |  |
--      |  |  `- PLog+ (1,[999,7,24,3]) state=[999,7,24,3]
--      |  |
--      |  `- PState+ old state=[999,7,24,3] new state=[999,7,24,3,1]
--      |
--      `- TrueP  i=4: PState+ a=-8
--         |
--         +- TrueP  PLog-+ a=-8
--         |  |
--         |  +- PLog- (-8,[999,7,24,3,1]) state=[999,7,24,3,1]
--         |  |
--         |  +- TrueP  PConst a=-8
--         |  |
--         |  `- PLog+ (-8,[999,7,24,3,1]) state=[999,7,24,3,1]
--         |
--         `- PState+ old state=[999,7,24,3,1] new state=[999,7,24,3,1,-8]
--   <BLANKLINE>
--
pput :: (Show z, Show a) => z -> Pred z a -> Pred z a
pput z = PState (This (const2 z))



--  PXml        :: [XPath] => ((NonEmpty JPath, Value) -> Maybe a) -> Pred z [(NonEmpty JPath, a)] -> Pred Value
{-
>import qualified Data.Text.Lay as TL
>:m + Text.Xml.Lens
>doc = "<root><foo><abc>dude</abc></foo><foo>hoo</foo><bar>moo</bar></root>" :: TL.Text
>doc ^.. xml . node "foo" . node "abc"
[Element {elementName = Name {nameLocalName = "abc", nameNamespace = Nothing, namePrefix = Nothing}, elementAttributes = fromList
 [], elementNodes = [NodeContent "dude"]}]
-}

-- | roughly equivalent to 'divide' in 'Divisible'
--
--   >>> pe2' (pdivide id (PLen (pgt 4)) (pgt 10)) (['a'..'h'],9)
--   <BLANKLINE>
--   FalseP PFn divide | a=("abcdefgh",9) | b=("abcdefgh",9)
--   |
--   `- FalseP PBoth
--      |
--      +- TrueP  PLen 8 as="abcdefgh"
--      |  |
--      |  `- TrueP  8 > 4
--      |
--      `- FalseP 9 > 10
--   <BLANKLINE>
--
pdivide :: (Show b, Show c) => (a -> (b, c)) -> Pred z b -> Pred z c -> Pred z a
pdivide abc pb pc = PFn "divide" abc (PBoth pb pc)

-- | roughly equivalent to 'choose' in 'Decidable'
--
--   >>> pe2' (pchoose id (PLen (pgt 4)) (pgt 10)) (Left ['a'..'h'])
--   <BLANKLINE>
--   TrueP  PFn choose | a=Left "abcdefgh" | b=Left "abcdefgh"
--   |
--   `- TrueP  PEither (Left) "abcdefgh"
--      |
--      `- TrueP  PLen 8 as="abcdefgh"
--         |
--         `- TrueP  8 > 4
--   <BLANKLINE>
--
--   >>> pe2' (pchoose id (PLen (pgt 4)) (pgt 10)) (Right 9)
--   <BLANKLINE>
--   FalseP PFn choose | a=Right 9 | b=Right 9
--   |
--   `- FalseP PEither (Right) 9
--      |
--      `- FalseP 9 > 10
--   <BLANKLINE>
--
pchoose :: (Show b, Show c) => (a -> Either b c) -> Pred z b -> Pred z c -> Pred z a
pchoose abc pb pc = PFn "choose" abc (PEither pb pc)

-- | unzip a list
--
--   >>> pe1' (PJsonKey "aGE" $ punzip (pfn (map showJPathsNE) $ PShowS 1) (jnumbers' $ PShow 1)) json2
--   <BLANKLINE>
--   TrueP  PJsonKey
--   |
--   +- TrueP  PFn punzip | a=[(JPKey "age" :| [JPIndex 0],Number 24.0),(JPKey "age" :| [JPIndex 1],Number 39.0),(JPKey "age" :| [JPIndex 2],Number 45 ... | b=([JPKey "age" :| [JPIndex 0],JPKey "age" :| [JPIndex 1],JPKey "age" :| [JPIndex 2],JPKey "age" :| [JPIndex 3]],[Number 2 ...
--   |  |
--   |  `- TrueP  PBoth
--   |     |
--   |     +- TrueP  PFn | a=[JPKey "age" :| [JPIndex 0],JPKey "age" :| [JPIndex 1],JPKey "age" :| [JPIndex 2],JPKey "age" :| [JPIndex 3]] | b=["nth 0.key \"age\"","nth 1.key \"age\"","nth 2.key \"age\"","nth 3.key \"age\""]
--   |     |  |
--   |     |  `- TrueP  PShowS
--   |     |     |
--   |     |     +- TrueP  PConst a=["nth 0.key \"age\"","nth 1.key \"age\"","nth 2.key \"age\"","nth 3.key \"age\""]
--   |     |     |
--   |     |     `- ===== PShowS =====
--   |     |        |
--   |     |        +- i=0 a=nth 0.key "age"
--   |     |        |
--   |     |        +- i=1 a=nth 1.key "age"
--   |     |        |
--   |     |        +- i=2 a=nth 2.key "age"
--   |     |        |
--   |     |        `- i=3 a=nth 3.key "age"
--   |     |
--   |     `- TrueP  PMorph bad=[] good=[24.0,39.0,45.0,27.0]
--   |        |
--   |        `- TrueP  PBoth
--   |           |
--   |           +- TrueP  PNull length=0 as=[]
--   |           |
--   |           `- TrueP  PShow
--   |              |
--   |              +- TrueP  PConst a=[24.0,39.0,45.0,27.0]
--   |              |
--   |              `- ===== PShow =====
--   |                 |
--   |                 +- i=0 a=24.0
--   |                 |
--   |                 +- i=1 a=39.0
--   |                 |
--   |                 +- i=2 a=45.0
--   |                 |
--   |                 `- i=3 a=27.0
--   |
--   `- Debugging jpaths
--      |
--      +- i=0 | key=age | [JPIndex 0,JPKey "age"]
--      |
--      +- i=1 | key=age | [JPIndex 1,JPKey "age"]
--      |
--      +- i=2 | key=age | [JPIndex 2,JPKey "age"]
--      |
--      `- i=3 | key=age | [JPIndex 3,JPKey "age"]
--   <BLANKLINE>
--
punzip :: (Foldable t, Show a, Show b) => Pred z [a] -> Pred z [b] -> Pred z (t (a, b))
punzip = (PFn "punzip" (unzip . toList) .) . PBoth

-- these are contravariant sort of curry uncurry
puncurry :: Show c => (a -> b -> c) -> Pred z c -> Pred z (a, b)
puncurry = PFn "uncurry" . uncurry

-- just locks down the signature is all
pcurry :: (Show a, Show b) => (c -> (a, b)) -> Pred z (a, b) -> Pred z c
pcurry = PFn "curry"

-- pe (pcurry (fst &&& fst . snd) (puncurry (-) (pgt 3))) (7,(12,'x'))
-- pe (pcu (fst &&& fst.snd) (-) (pgt 3)) (7,(12,'x'))

-- curry . uncurry but has tracing
-- | adds tracing to 'curry' . 'uncurry'
--
--   >>> pe' (pcu (fst &&& fst.snd) (-) (pgt 3)) (7,(12,'x'))
--   <BLANKLINE>
--   FalseP PFn uncurry | a=(7,12) | b=-5
--   |
--   `- FalseP -5 > 3
--   <BLANKLINE>
--
pcu :: (Show a, Show b, Show y) => (x -> (a, b)) -> (a -> b -> y) -> Pred z y -> Pred z x
pcu f g = phide . pcurry f . puncurry g

-- pe (pcomp (fst &&& fst.snd) (uncurry (-)) (pgt 3)) (7,(12,'x'))
-- by separating out the functions we get tracing
-- if we just do x->y then we lose the stuff in between but then it is just PFn

-- pcomp is good cos we get all the stuff between traced
-- pep (pquantifier (pgt 3) (pcomp (uncurry (-)) (>0) pid)) [1..10]
-- pep1 (pquantifier (peven * pgt 5) pge2) [1..10]   -- if just simple comparison
-- pep1 (pquantifier (peven * pgt 5) (plift2 id id (>))) [1..10] -- could decide to add subtract one from one of the ids to offset it a bit
-- | adds tracing to composed functions
--
--   >>> pe' (pcomp (first fst) (uncurry (-)) (pgt 3)) ((12,'x'),7)
--   <BLANKLINE>
--   TrueP  PFn PComp a->x | a=((12,'x'),7) | b=(12,7)
--   |
--   `- TrueP  PFn PComp x->b | a=(12,7) | b=5
--      |
--      `- TrueP  5 > 3
--   <BLANKLINE>
--
pcomp :: (Show x, Show b) => (a -> x) -> (x -> b) -> Pred z b -> Pred z a
pcomp ax xb = PFn "PComp a->x" ax . PFn "PComp x->b" xb

--pview :: Show a => Getting a s a -> Pred z a -> Pred z s
--pview f = PFn "view" (^. f)

-- cos you have to have it!
pid :: Pred z Bool
pid = PLift "id" id

-- we lose the in between stuff
-- pe2 (pcu2 (uncurry (-) . (fst &&& fst.snd)) (pgt 3)) (7,(12,'x'))
--pcu2 :: (Show y) => (x -> y) -> Pred z y -> Pred x
--pcu2 = PFn "curryuncurry"

-- | infix match on a list
--
--   >>> pe2' (minfix "abc") "<<<abc>>>"
--   <BLANKLINE>
--   TrueP  PMatch "abc" `isInfixOf` "<<<abc>>>"
--   <BLANKLINE>
--
minfix, mprefix, msuffix :: (Show a, Eq a) => [a] -> Pred z [a]
minfix = PMatch SInfix
mprefix = PMatch SPrefix
msuffix = PMatch SSuffix

sinfix, sprefix, ssuffix, sci, scs :: SConv s => s -> Pred z s
sinfix = PString CI SInfix
sprefix = PString CI SPrefix
ssuffix = PString CI SSuffix
sci = PString CI SNone
scs = PString CS SNone

instance (IsString a, SConv a) => IsString (Pred z a) where
  fromString = PString CI SNone . fromString

-- |||
pfanin :: Show d => String -> (b -> d) -> (c -> d) -> Pred z d -> Pred z (Either b c)
pfanin s f g = PFn ("(|||)" `stringAp` s) (either f g)

(|||!) :: Show d => (b -> d) -> (c -> d) -> Pred z d -> Pred z (Either b c)
(|||!) = pfanin ""

pplus :: (Show b', Show c') => String -> (b -> b') -> (c -> c') -> Pred z (Either b' c') -> Pred z (Either b c)
pplus s f g = PFn ("(+++)" `stringAp` s) (f +++ g)

(+++!) :: (Show b', Show c') => (b -> b') -> (c -> c') -> Pred z (Either b' c') -> Pred z (Either b c)
(+++!) = pplus ""

pfn :: Show b => (a -> b) -> Pred z b -> Pred z a
pfn = PFn ""

p_1 :: (Field1 s s b b, Show b) => Pred z b -> Pred z s
p_1 = PFn "_1" (view _1)

p_2 :: (Field2 s s b b, Show b) => Pred z b -> Pred z s
p_2 = PFn "_2" (view _2)

p_3 :: (Field3 s s b b, Show b) => Pred z b -> Pred z s
p_3 = PFn "_3" (view _3)

p_4 :: (Field4 s s b b, Show b) => Pred z b -> Pred z s
p_4 = PFn "_4" (view _4)

phide :: Pred z a -> Pred z a
phide = PChangeOpts (\o -> o { oHide = max 2 (oHide o + 2) })

plift :: (a -> Bool) -> Pred z a
plift = PLift ""

picmp :: (i -> a -> Bool) -> Pred z (i, a)
picmp = PLift "picmp" . uncurry

peven, podd :: Integral a => Pred z a
peven = PLift "even" even
podd = PLift "odd" odd

pfind :: (Foldable t, Show a) => Pred z a -> Pred z () -> Pred z a -> Pred z (t a)
pfind p e = PPartition p . PSnd . PHead e

pfilter :: (Show a, Foldable t) => Pred z a -> Pred z [a] -> Pred z (t a)
pfilter p = PPartition p . phide . PSnd

pspan :: (Foldable t, Show a) => Pred z a -> Pred z ([a],[a]) -> Pred z (t a)
pspan p = PBreak (-p)

pspan2 :: (Foldable t, Show a) => Pred z a -> Pred z [a] -> Pred z [a] -> Pred z (t a)
pspan2 p p0 p1 = PBreak (-p) (PBoth (PMsg Inline "Left Predicate" p0) (PMsg Inline "Right Predicate" p1))


-- old school way where we split out the predicates for left and right instead of tupling
-- easier to work with but we have to introduce PBoth=AND
-- also not as flexible cos cannot compare results of left and right cos independent
pbreak2 :: (Foldable t, Show a) => Pred z a -> Pred z [a] -> Pred z [a] -> Pred z (t a)
pbreak2 p p0 p1 = PBreak p (PBoth (PMsg Inline "Left Predicate" p0) (PMsg Inline "Right Predicate" p1))

ppartition2 :: (Foldable t, Show a) => Pred z a -> Pred z [a] -> Pred z [a] -> Pred z (t a)
ppartition2 p p0 p1 = PPartition p (PBoth (PMsg Inline "Left Predicate" p0) (PMsg Inline "Right Predicate" p1))

-- these are trivial using pfn/PFn but does give documentation using String instead of a mysterious PFn
-- also cos I use them a lot
pstar :: (Show c', Show c) => String -> (b -> c) -> (b' -> c') -> Pred z (c, c') -> Pred z (b, b')
pstar s f g = PFn ("(***)" `stringAp` s) (f *** g)

(***!) :: (Show c', Show c) => (b -> c) -> (b' -> c') -> Pred z (c, c') -> Pred z (b, b')
(***!) = pstar ""

pfanout, pamp :: (Show c', Show c) => String -> (b -> c) -> (b -> c') -> Pred z (c, c') -> Pred z b
pfanout s f g = PFn ("(&&&)" `stringAp` s) (f &&& g)
pamp = pfanout

(&&&!) :: (Show c', Show c) => (b -> c) -> (b -> c') -> Pred z (c, c') -> Pred z b
(&&&!) = pfanout ""

pstar2 :: Show b => String -> (a -> b) -> Pred z (b, b) -> Pred z (a, a)
pstar2 s  = join (pstar s)

-- too hard to write using PSeq
pzipand :: (Foldable t, Show a) => [Pred z a] -> Pred z (t a)
pzipand ps = PMsg Inline "PZipAnd" $ PZipExact ps 0 (PLift "and" and)

pzipor :: (Foldable t, Show a) => [Pred z a] -> Pred z (t a)
pzipor ps = PMsg Inline "PZipOr" $ PZipExact ps 0 (PLift "or" or)

pands :: [Pred z a] -> Pred z a
pands ps = PMsg Inline "PAnds" $ POps ps (PLift "and" and)

pors :: [Pred z a] -> Pred z a
pors ps = PMsg Inline "POrs" $ POps ps (PLift "or" or)

-- way cool:
-- | generalises PForAll and PExists
--
--   >>> pe2' (pquantifier (PRange 4 7) 1) [1..10]
--   <BLANKLINE>
--   TrueP  PPartition | lefts=6 (0,1) | rights=4 (3,4)
--   |
--   +- TrueP  PPartition Predicate
--   |  |
--   |  `- TrueP  PFn (***) length | a=([1,2,3,8,9,10],[4,5,6,7]) | b=(6,4)
--   |     |
--   |     `- TrueP  PConst a=(6,4)
--   |
--   `- PPartition debugging info
--      |
--      +- FalseP i=0: 1 < 4 (Under)
--      |
--      +- FalseP i=1: 2 < 4 (Under)
--      |
--      +- FalseP i=2: 3 < 4 (Under)
--      |
--      +- TrueP  i=3: 4 == [4..7]
--      |
--      +- TrueP  i=4: 5 == [4..7]
--      |
--      +- TrueP  i=5: 6 == [4..7]
--      |
--      +- TrueP  i=6: 7 == [4..7]
--      |
--      +- FalseP i=7: 8 > 7 (Over)
--      |
--      +- FalseP i=8: 9 > 7 (Over)
--      |
--      `- FalseP i=9: 10 > 7 (Over)
--   <BLANKLINE>
--
--   >>> pe1' (pquantifier (peven * pgt 5) (puncurry (-) (pgt 2))) [1..10]
--   <BLANKLINE>
--   TrueP  PPartition | lefts=7 (0,1) | rights=3 (5,6)
--   |
--   `- TrueP  PPartition Predicate
--      |
--      `- TrueP  PFn (***) length | a=([1,2,3,4,5,7,9],[6,8,10]) | b=(7,3)
--         |
--         `- TrueP  PFn uncurry | a=(7,3) | b=4
--            |
--            `- TrueP  4 > 2
--   <BLANKLINE>
--
pquantifier :: (Show a, Foldable t) => Pred z a -> Pred z (Int, Int) -> Pred z (t a)
pquantifier p p12 = PPartition p (pstar2 "length" length p12)

-- all vs at least one: so we have flexibility to make sure that at least 1/2 are valid
pforall, pforall' :: (Foldable t, Show a) => Pred z a -> Pred z (t a)
pforall = flip pquantifier (PFst (peq 0))
pforall' = flip PPartition (PFst PNull)

pexists, pexists' :: (Foldable t, Show a) => Pred z a -> Pred z (t a)
pexists = flip pquantifier (PSnd (pgt 0))
pexists' = flip PPartition (PSnd (-PNull))

-- | like 'Data.Function.on' for predicates
plift2 :: (Show b', Show a') => (a -> a') -> (b -> b') -> (a' -> b' -> Bool) -> Pred z (a, b)
plift2 f g = pstar "plift2" f g . plift . uncurry

-- | like 'Data.Function.on' for predicates but uses the same function for both sides
pliftBi :: Show a' => (a -> a') -> (a' -> a' -> Bool) -> Pred z (a, a)
pliftBi f = pstar2 "pliftBi" f . plift . uncurry

pfsts :: (Functor f, Show (f a)) => Pred z (f a) -> Pred z (f (a, b))
pfsts = phide . PFn "fsts" (fmap fst)

psnds :: (Functor f, Show (f b)) => Pred z (f b) -> Pred z (f (a, b))
psnds = phide . PFn "snds" (fmap snd)

psnds2 :: (Functor f2, Functor f1, Show (f2 b2), Show (f1 b1)) =>
     Pred z (f1 b1, f2 b2) -> Pred z (f1 (a1, b1), f2 (a2, b2))
psnds2 = phide . PFn "snds2" (fmap snd *** fmap snd)

pcatch :: Pred z a -> Pred z a -> Pred z a
pcatch e = PMsg Inline "PCatch" . PIf (Just e) Nothing Nothing

pordie :: String -> Pred z a -> Pred z a
pordie s = PMsg Inline "POrDie" . PIf Nothing (Just (pfail s)) Nothing

pwhen, punless :: Pred z a -> Pred z a -> Pred z a
pwhen = PIf Nothing Nothing . Just
punless p = PIf Nothing (Just p) Nothing

-- works on a tuple: runs a maybe on each side then one of 4 predicates depending on the Nothing Just combinations
pprismLR, pprismLR' :: (Show b, Show b') =>
     String
  -> (a -> Maybe b)
  -> (a' -> Maybe b')
  -> Pred z () -- when both sides are nothing
  -> Pred z b
  -> Pred z b'
  -> Pred z (b, b') -- both match -- use this for comparing: eg PCmp2 or PEq2 or just plain PFn uncurry
  -> Pred z (a, a')
pprismLR s f g p0 p1 p2 p3 = PFn ("pprismLR " <> s) (\(a, a') -> case (f a, g a') of
                               (Nothing,Nothing) -> Left (Left ())
                               (Just b,Nothing)  -> Left (Right b)
                               (Nothing,Just b') -> Right (Left b')
                               (Just b,Just b')  -> Right (Right (b, b'))) (PEither (PEither p0 p1) (PEither p2 p3))

-- use These cos more natural then is Maybe These as opposed to Either Either Either
pprismLR' s f g p0 p1 p2 p3 = PFn ("pprismLR " <> s) (\(a, a') -> case (f a, g a') of
                               (Nothing,Nothing) -> Nothing
                               (Just b,Nothing)  -> Just $ This b
                               (Nothing,Just b') -> Just $ That b'
                               (Just b,Just b')  -> Just $ These b b') (PMaybe p0 (PThese p1 p2 p3))

pprismLR'' :: (Show b, Show b') =>
     String
  -> (a -> Maybe b)
  -> (a' -> Maybe b')
  -> Pred z () -- when both sides are nothing
  -> Pred z (These b b')
  -> Pred z (a, a')
pprismLR'' s f g p0 p1 = PFn ("pprismLR'' " <> s) (\(a, a') -> case (f a, g a') of
                               (Nothing,Nothing) -> Nothing
                               (Just b,Nothing)  -> Just $ This b
                               (Nothing,Just b') -> Just $ That b'
                               (Just b,Just b')  -> Just $ These b b') (PMaybe p0 p1)

pprismL :: (Show x, Show b) =>
     String
  -> (a -> Maybe b)  -- match lhs of tuple
  -> Pred z x        -- if no match ie Nothing then do this
  -> Pred z (b, x)    -- else result of applying lhs
  -> Pred z (a, x)
pprismL s f p q = PFn ("PPrismL " <> s) (\(a, x) -> maybe (Left x) (Right . (,x)) (f a)) (PEither p q)

pprismR :: (Show x, Show b) => String -> (a -> Maybe b) -> Pred z x -> Pred z (x, b) -> Pred z (x, a)
pprismR s f p q = PFn ("PPrismR " <> s) (\(x, a) -> maybe (Left x) (Right . (x,)) (f a)) (PEither p q)

-- same but for Either instead of Maybe
pprismLEither :: (Show c, Show x, Show b) =>
     (a -> Either b c) -> Pred z (b, x) -> Pred z (c, x) -> Pred z (a, x)
pprismLEither f p q = PFn "pprismle" (\(a, x) -> either (Left . (,x)) (Right . (,x)) (f a)) (PEither p q)

pprismREither :: (Show c, Show x, Show b) =>
     (a -> Either b c) -> Pred z (x, b) -> Pred z (x, c) -> Pred z (x, a)
pprismREither f p q = PFn "pprismre" (\(x, a) -> either (Left . (x,)) (Right . (x,)) (f a)) (PEither p q)

--not so useful: just use PFn directly but shows how to use pfn
--plens :: Show b => Getting b s b -> Pred z b -> Pred z s
--plens f = PFn "lens" (view f)

-- use pmaybe for prisms and stuff that returns Maybe
-- these are useful else too much to remember
-- | most common version of 'PPrism'
--
--   >>> :set -XOverloadedStrings
--   >>> pe1' (pprism0 (^? key "glossary" . key "GlossDiv" . key "title" . _String) "s") json1
--   <BLANKLINE>
--   TrueP  PPrism (Just) [] "S"
--   |
--   `- TrueP  PStringCI "S" == "s"
--   <BLANKLINE>
--
--   >>> let zzz = PLinear Rigid [preq (pprism0 (^? _Bool) 1), preq (pprism0 (^? _Number) 1)]
--   >>> pe2' (pprism0 (^? _Array) zzz) "[1,true]"
--   <BLANKLINE>
--   TrueP  PPrism (Just) [] [Number 1.0,Bool True]
--   |
--   `- TrueP  PLinear | debug=[OneMatch 0,OneMatch 1] match=[(0,[1]),(1,[0])]
--      |
--      +- TrueP  Predicates | PZipAnd | PZipExact | as=[1,1] | (bad,good)=(0,2)
--      |  |
--      |  `- TrueP  PLift and | a=[True,True]
--      |     |
--      |     +- TrueP  i=0
--      |     |  |
--      |     |  +- TrueP  1 == 1
--      |     |  |
--      |     |  `- PPrism
--      |     |     |
--      |     |     +- PConst FalseP
--      |     |     |
--      |     |     `- PConst TrueP
--      |     |
--      |     `- TrueP  i=1
--      |        |
--      |        +- TrueP  1 == 1
--      |        |
--      |        `- PPrism
--      |           |
--      |           +- PConst FalseP
--      |           |
--      |           `- PConst TrueP
--      |
--      +- TrueP  PLinear | OneMatch 0 a=Number 1.0 cnt=1 (i=1, a=Number 1.0)
--      |  |
--      |  +- FalseP i=0: PPrism (Nothing) [] | PConst a=()
--      |  |
--      |  `- TrueP  i=1: PPrism (Just) [] 1.0
--      |     |
--      |     `- TrueP  PConst a=1.0
--      |
--      `- TrueP  PLinear | OneMatch 1 a=Bool True cnt=1 (i=0, a=Bool True)
--         |
--         +- TrueP  i=0: PPrism (Just) [] True
--         |  |
--         |  `- TrueP  PConst a=True
--         |
--         `- FalseP i=1: PPrism (Nothing) [] | PConst a=()
--   <BLANKLINE>
--
pprism0, pprism1 :: (Show a, Show b) => (a -> Maybe b) -> Pred z b -> Pred z a
pprism0 f = PPrism "" f pfalse
pprism1 f = PPrism "" f ptrue

pprism2 :: (Show a, Show b) => String -> (a -> Maybe b) -> Pred z b -> Pred z a
pprism2 e f = PPrism "" f (pfail e)

pprism' :: (Show b, Show c) => String -> (a -> Either b c) -> Pred z b -> Pred z c -> Pred z a
pprism' s g = (PFn s g .) . PEither

-- if pred is false we want to add a message! can use PTree but not great: really need to extend BoolPE
--     from Either (NonEmpty String) Bool to Either (NonEmpty String) (Bool,String) ??
-- most common option: all required fields and no extra 'a's allowed that arent covered by a predicate

preq, popt, pnever :: Pred z a -> (Pred z Int, Pred z a)
preq = (preq',)
popt = (popt',)
pnever = (pnever',)

pij :: Int -> Int -> Pred z a -> (Pred z Int, Pred z a)
pij = ((,) .) . PRange

(..!) :: Ord a => a -> a -> Pred z a
(..!) = PRange

preq', popt', pnever' :: Pred z Int
preq' = PRange 1 1
popt' = PRange 0 1
pnever' = PRange 0 0

pmsgIfNotTrue :: String -> Pred z a -> Pred z a
pmsgIfNotTrue = pmsgIf (isn't _TrueP)

pmsgIfNotTrue' :: String -> Pred z a -> Pred z a
pmsgIfNotTrue' s p =
  let m = Just (PMsg Inline s p)
  in PIf m m Nothing p

pmsgIf :: (BoolP -> Bool) -> String -> Pred z a -> Pred z a
pmsgIf f msg = PTree go
  where go tt | f (tt ^. boolP) = addMessagePre msg tt
              | otherwise = tt

infixr 3 `PAnd`
infixr 2 `POr`
infixr 2 `PXor`
infixr 2 `PEquiv`
infixr 2 `PImpl`

--
--   >>> pe' (5 .! peq 'f') ['a'..'z']
--   <BLANKLINE>
--   TrueP  PIx 5 'f'
--   |
--   `- TrueP  'f' == 'f'
--   <BLANKLINE>
--
--   >>> pe' (5 .! peq 'f' + 1) ['a'..'z']
--   <BLANKLINE>
--   TrueP  POr
--   |
--   +- TrueP  PIx 5 'f'
--   |  |
--   |  `- TrueP  'f' == 'f'
--   |
--   `- TrueP
--   <BLANKLINE>
--
--   >>> pe' (5 .! peq 'f' * 1) ['a'..'z']
--   <BLANKLINE>
--   TrueP  PAnd
--   |
--   +- TrueP  PIx 5 'f'
--   |  |
--   |  `- TrueP  'f' == 'f'
--   |
--   `- TrueP
--   <BLANKLINE>
--
--   >>> pe' (5 .! peq 'f' .&& 1) (['a'..'z'],())
--   <BLANKLINE>
--   TrueP  PBoth
--   |
--   +- TrueP  PIx 5 'f'
--   |  |
--   |  `- TrueP  'f' == 'f'
--   |
--   `- TrueP
--   <BLANKLINE>
--
--   >>> pe' (5 .! peq 'f' .&& PLen (pgt 4)) (['a'..'z'],"af")
--   <BLANKLINE>
--   FalseP PBoth
--   |
--   +- TrueP  PIx 5 'f'
--   |  |
--   |  `- TrueP  'f' == 'f'
--   |
--   `- FalseP PLen 2
--      |
--      `- FalseP 2 > 4
--   <BLANKLINE>
--
(.!) = pix
(.!), pix :: (Eq (Index s), Show s, Show (IxValue s), Show (Index s),
              Ixed s) =>
             Index s -> Pred z (IxValue s) -> Pred z s
pix i = PIx i 0

-- abs and signum?
-- fromInteger: could set >0 is ptrue but then pfail will never happen
-- cos will just call negate then fromInteger
-- pfail is good cos indicates an error in your predicate
-- adding pfail to BoolPE was a really good idea

-- Note: the Num law abs x * signum x == x is satisfied
-- since id x `PAnd` id x == x * x = x

instance Num (Pred z a) where
  (+) = POr
  (*) = PAnd
  negate = PNot
  p - q = p `POr` PNot q
  fromInteger n | n == 0 = pfalse
                | n == 1 = ptrue
                | n == 2 = pfail ""
                | otherwise = pfail ("fromInteger: n=" ++ show n ++ ": use 0 or 1")
  abs = id
  signum = id

instance Eq (Pred z a) where
  PString b sop s == PString b1 sop1 s1 = b == b1 && sop == sop1 && sdisp s == sdisp s1
  PString {} == _ = False

  PDist b s p == PDist b1 t q = b == b1 && sdisp s == sdisp t && p == q
  PDist {} == _ = False

  PCmp a b == PCmp a1 b1 = a == a1 && b == b1
  PCmp {} == _ = False

  PEq a b == PEq a1 b1 = a == a1 && b == b1
  PEq {} == _ = False

  PCmp2 c == PCmp2 c1 = c == c1
  PCmp2 {} == _ = False

  PEq2 b == PEq2 b1 = b == b1
  PEq2 {} == _ = False

  PMatch sop a == PMatch sop1 a1 = sop == sop1 && a == a1
  PMatch {} == _ = False

  PRegex {} == _ = False
  PRegexI {} == _ = False
  PRegexs {} == _ = False
  PRegexV {} == _ = False
  PRegexN {} == _ = False
  PRegexIP {} == _ = False

  PRange a1 a2 == PRange b1 b2 = a1 == b1 && a2 == b2
  PRange {} == _ = False

  PElem as == PElem bs = toList as == toList bs
  PElem {} == _ = False

  PAnd p q == PAnd p1 q1 = p == p1 && q == q1
  PAnd {} == _ = False

  POr p q == POr p1 q1 = p == p1 && q == q1
  POr {} == _ = False

  PXor p q == PXor p1 q1 = p == p1 && q == q1
  PXor {} == _ = False

  PEquiv p q == PEquiv p1 q1 = p == p1 && q == q1
  PEquiv {} == _ = False

  PImpl p q == PImpl p1 q1 = p == p1 && q == q1
  PImpl {} == _ = False

  PNot p == PNot q = p == q
  PNot {} == _ = False

  POps ps p == POps qs q = ps == qs && p == q
  POps {} == _ = False

  PForAll p == PForAll q = p == q
  PForAll {} == _ = False

  PZipExact ps e q == PZipExact ps1 e1 q1 = ps == ps1 && e == e1 && q == q1
  PZipExact {} == _ = False

  PSeq ps q == PSeq ps1 q1 = ps == ps1 && q == q1
  PSeq {} == _ = False

  PExists p == PExists q = p == q
  PExists {} == _ = False

  PConst b == PConst b1 = b == b1
  PConst {} == _ = False

  PLift {} == _ = False -- cant compare functions

  PLen p == PLen q = p == q
  PLen {} == _ = False

  PBoth pa pb == PBoth pa1 pb1 = pa == pa1 && pb == pb1
  PBoth {} == _ = False

  PFst p == PFst q = p == q
  PFst {} == _ = False

  PSnd p == PSnd q = p == q
  PSnd {} == _ = False

  PNull == PNull = True
  PNull {} == _ = False

  PEmpty == PEmpty = True
  PEmpty {} == _ = False

  PIf mpexc mpb mpg p == PIf mpexc1 mpb1 mpg1 p1 = mpexc == mpexc1 && mpb == mpb1 && mpg == mpg1 && p == p1
  PIf {} == _ = False

--  PApp a p == PApp a1 p1 = coerce a == coerce a1 && p == p1 -- todo: might have to use typeable
  PApp {} == _  = False

{-
  PJoin a == PJoin a1 = case cast a of
                          Nothing -> False
                          Just a' -> case cast a1 of
                                        Nothing -> False
                                        Just a1' -> a' == a1' -- cast a1 -- todo: might have to use typeable
  PJoin a == PJoin a1 = case (cast a, cast a1) of
                          (Just a', Just a1') -> a' == a1'
                          _ -> False
-}
  PJoin {} == _  = False -- todo

  PView {} == _  = False

  PHead e p == PHead f q = e == f && p == q
  PHead {} == _ = False

  -- POne p q r == POne p1 q1 r1 = p == p1 && q == q1 && r == r1
  POne {} == _ = False

  POneT e e2 p == POneT f f2 q = e == f && e2== f2 && p == q
  POneT {} == _ = False

  PUnconsT e p == PUnconsT f q = e == f && p == q
  PUnconsT {} == _ = False

  PUnsnocT e p == PUnsnocT f q = e == f && p == q
  PUnsnocT {} == _ = False

--  PUncons e p == PUncons f q = e == f && p == q
  PUncons {} == _ = False

  PLast e p == PLast f q = e == f && p == q
  PLast {} == _ = False

--  PUnsnoc e p == PUnsnoc f q = e == f && p == q
  PUnsnoc {} == _ = False

  PIx i e p == PIx j f q = e == f && i == j && p == q
  PIx {} == _ = False

  PPartition p pbg == PPartition p1 pbg1 = p == p1 && pbg == pbg1
  PPartition {} == _ = False

  PSplitAt i p == PSplitAt j q = i == j && p == q
  PSplitAt {} == _ = False

--  PTake i p == PTake j q = i == j && p == q
--  PTake {} == _ = False

--  PDrop i p == PDrop j q = i == j && p == q
--  PDrop {} == _ = False

  PBreak p p12 == PBreak q q12 = p == q && p12 == q12
  PBreak {} == _ = False

  PSpan p p12 == PSpan q q12 = p == q && p12 == q12
  PSpan {} == _ = False

--  PSpans ips q == PSpans ips1 q1 = ips == ips1 && q == q1
--  PSpans {} == _ = False

  POrder c == POrder d = c == d
  POrder {} == _ = False

  POrderEq b == POrderEq b1 = b == b1
  POrderEq {} == _ = False

  PLinear b qps == PLinear b1 qps1 = b == b1 && qps == qps1
  PLinear {} == _ = False

  PEither p q == PEither p1 q1 = p == p1 && q == q1
  PEither {} == _ = False

  PThese p q pq == PThese p1 q1 pq1 = p == p1 && q == q1 && pq == pq1
  PThese {} == _ = False

  PISect p == PISect q = p == q
  PISect {} == _ = False

  PISectList p == PISectList q = p == q
  PISectList {} == _ = False

  PMorph {} == _ = False
--  PMorph2 {} == _ = False

  PMaybe p q == PMaybe p1 q1 = p == p1 && q == q1
  PMaybe {} == _ = False

  PJson {} == _ = False -- pprism like

  PJsonKey p q == PJsonKey p1 q1 = p == p1 && q == q1
  PJsonKey {} == _ = False

  PJsonP jps p q  == PJsonP jps1 p1 q1 = jps == jps1 && p == p1 && q == q1
  PJsonP {} == _ = False

  PPrism {} == _ = False -- cant compare functions
  PPrismL {} == _ = False
  PPrismR {} == _ = False
  PPrismLE {} == _ = False
  PPrismRE {} == _ = False

  PSwap p == PSwap q = p == q
  PSwap {} == _ = False

  PReverse p == PReverse q = p == q
  PReverse {} == _ = False

  PChangeOpts {} == _ = False -- cant compare functions

  PShow p == PShow q = p == q
  PShow {} == _ = False

  PShowS p == PShowS q = p == q
  PShowS {} == _ = False

  PShow1 p == PShow1 q = p == q
  PShow1 {} == _ = False

  PShowS1 p == PShowS1 q = p == q
  PShowS1 {} == _ = False

  POrDie s p == POrDie t q = s == t && p == q
  POrDie {} == _ = False

  PCatch e p == PCatch f q = e == f && p == q
  PCatch {} == _ = False

  PMsg hide s p == PMsg hide1 s1 p1 = hide == hide1 && s == s1 && p == p1
  PMsg {} == _ = False

  PTree {} == _ = False -- cant compare functions

  -- these cannot compare as have embedded functions
  PFn {} == PFn {} = False -- cant compare of course
  PFn {} == _ = False

  --PCoerce p == PCoerce q = coerce p == coerce q -- todo: cant get these to compare
  PCoerce {} == _ = False
  PLog {} == _ = False
  PState {} == _ = False

  PGet p == PGet q = p == q
  PGet {} == _ = False

--  PPut z == PPut z1 = z == z1
--  PPut {} == _ = False

-- | false and true predicates
pfalse, ptrue :: Pred z a
pfalse = PConst $ mkBool FalseP []
ptrue = PConst $ mkBool TrueP []

-- | false and true predicates with a string message
pfalse', ptrue' :: String -> Pred z a
pfalse' = PConst . mkBool FalseP . (:[])
ptrue' = PConst . mkBool TrueP . (:[])

-- | fail predicate with an exception and a message
pfail :: String -> Pred z a
pfail = PConst . mkfail

-- keeping it consistent and tight [dont hide the fact that you need to cater for Pred z ()
-- partial functions require you to be honest
-- pprism0/1/2 are an exception cos too much work

-- | most common use of 'POne' is to fail if empty or if too many elements
--
--   >>> pe1' (pone $ pgt 4) []
--   <BLANKLINE>
--   FalseP POne empty! | PConst a=()
--   <BLANKLINE>
--
--   >>> pe1' (pone $ pgt 4) [10]
--   <BLANKLINE>
--   TrueP  POne 10
--   |
--   `- TrueP  10 > 4
--   <BLANKLINE>
--
--   >>> pe1' (pone $ pgt 4) [10,11,12]
--   <BLANKLINE>
--   FalseP POne extra values! a=10 s'=[11,12]
--   |
--   `- FalseP PConst a=(10,[11,12])
--   <BLANKLINE>
--
pone :: (AsEmpty s, Cons s s a a, Show a, Show s) => Pred z a -> Pred z s
pone = POne 0 0

-- | most common use of 'POneT' is to fail if empty or if too many elements
poneT :: (Foldable t, Show a) => Pred z a -> Pred z (t a)
poneT = POneT 0 0

-- | POneT in terms of POne but POneT has equality
poneT' :: (Foldable t, Show a) => Pred z () -> Pred z (a, [a]) -> Pred z a -> Pred z (t a)
poneT' p q = phide . pfn toList . POne p q

-- | 'POne' in terms of 'PUncons'
pone' :: (AsEmpty s, Cons s s a a, Show a, Show s) => Pred z () -> Pred z (a,s) -> Pred z a -> Pred z s
pone' e e1 p = PUncons e $ PIf Nothing (Just e1) (Just (PFst p)) (PSnd PEmpty)

-- remember it is bool false true pred but the types tell us nothing!
-- pbool 0 1 peven == peven
-- pbool 1 0 peven == -peven
-- pbool 0 0 peven = 0
-- pbool 1 1 peven = 1
-- might make sense if you want to provide a dedicated message?
-- dont see any use for this at all! if anything it is misleading
--pbool :: Pred z a -> Pred z a -> Pred z a -> Pred z a
--pbool pf = PIf Nothing (Just pf) . Just

-- splits into 2 as PMorph2 but in terms of PMorph so adds nothing
--pmorph2 :: (Show a, Foldable t, Show b) => (a -> Maybe b) -> Pred z [a] -> Pred z [b] -> Pred z (t a)
--pmorph2 f e = PMorph f . PBoth e

-- | lifts 'maybeToEither' over a functor see 'PMorph' for Foldable but you lose ordering
pmaybeF :: (Show (f (Either a b)), Functor f) => (a -> Maybe b) -> Pred z (f (Either a b)) -> Pred z (f a)
pmaybeF = PFn "pmaybeF" . fmap . maybeToEither

--pmaybeF' :: (Show (f b), Functor f) => (a -> b) -> Pred z (f b) -> Pred z (f a)
--pmaybeF' = PFn "pmaybeF'" . fmap

-- | lifts 'maybeToEither' over a foldable see 'PMorph' but does not retain ordering
pmaybeT :: (Show a, Show b, Foldable t) => (a -> Maybe b) -> Pred z [Either a b] -> Pred z (t a)
pmaybeT f = PFn "pmaybeT" (map (maybeToEither f) . toList)

--pmorph :: (Foldable t, Show a, Show b) =>
--     (a -> Maybe b) -> Pred z ([a], [b]) -> Pred z (t a)
--pmorph f = pmaybeT f . PFn "partitionEithers" partitionEithers

-- | lifts 'maybeToEither' over a []. emulates 'PMorph' but not as good messages
--   Examples:
--
--   >>> pe1' (pmorph (^? ix 3 . to show) 1) [[1,2,3,4],[10..11],[],[19..30],[]]
--   <BLANKLINE>
--   TrueP  PFn pmorph | a=[[1,2,3,4],[10,11],[],[19,20,21,22,23,24,25,26,27,28,29,30],[]] | b=([[10,11],[],[]],["4","22"])
--   |
--   `- TrueP  PConst a=([[10,11],[],[]],["4","22"])
--   <BLANKLINE>
--
pmorph :: (Foldable t, Show a, Show b) =>
     (a -> Maybe b) -> Pred z ([a], [b]) -> Pred z (t a)
pmorph f = PFn "pmorph" (partitionEithers . map (maybeToEither f) . toList)

--pone e p = PUncons e (PSnd (PIf Nothing (Just $ pfalse' "extracrap") (Just $ ptrue' "awesome") PEmpty) * PFst p)

-- | generic version of 'PHead' using 'PUncons' and 'Cons' class instead of []
phead :: (Cons s s a a, Show a, Show s) => Pred z () -> Pred z a -> Pred z s
phead e = PMsg Inline "phead" . PUncons e . phide . PFst

--plast :: (Snoc s s a a, Show a, Show s) => Pred z () -> Pred z a -> Pred z s
--plast e = PPrism "plast" (^? _last) (pmsgIfNotTrue "empty" e)

-- | generic version of 'PLast' using 'PUnsnoc' and 'Snoc' class
plast :: (Snoc s s a a, Show a, Show s) => Pred z () -> Pred z a -> Pred z s
plast e = PMsg Inline "plast" . PUnsnoc e . phide . PSnd

lpredE :: String -> Pred z a -> Pred z a
lpredE = PTree . flip addError

rpred :: String -> Pred z a -> Pred z a
rpred = PTree . addMessagePre

rpred1 :: (BoolP -> BoolP) -> Pred z a -> Pred z a
--rpred1 f = PTree (\t -> t & boolP %~ f)
rpred1 = PTree . over boolP

plt, ple, pge, pgt :: Ord a => a -> Pred z a
plt = PCmp Lt
ple = PCmp Le
pge = PCmp Ge
pgt = PCmp Gt

peq, pne :: Eq a => a -> Pred z a
peq = PEq True
pne = PEq False

-- | predicates for comparing values in a tuple
--
--   >>> pe' peq2 (14,4)
--   <BLANKLINE>
--   FalseP PEq2 14 == 4
--   <BLANKLINE>
--
--   >>> pe' plt2 (14,4)
--   <BLANKLINE>
--   FalseP PCmp2 14 < 4
--   <BLANKLINE>
--
--   >>> pe' pge2 (14,4)
--   <BLANKLINE>
--   TrueP  PCmp2 14 >= 4
--   <BLANKLINE>
--
plt2, ple2, pge2, pgt2 :: (Show a, Ord a) => Pred z (a, a)
plt2 = PCmp2 Lt
ple2 = PCmp2 Le
pge2 = PCmp2 Ge
pgt2 = PCmp2 Gt

peq2, pne2 :: (Show a, Eq a) => Pred z (a, a)
peq2 = PEq2 True
pne2 = PEq2 False

showPred :: Show a => POpts -> Pred z a -> Tree String
showPred o (PConst b)             = Node ("PConst " <> toNodeString o b) []
showPred _ (PLift s _)            = Node ("PLift " <> s)  []
showPred _ (PString ci sop s)     = Node ("PString" <> show ci <> " " <> showStringOperator sop "a" (sdisp s)) []
showPred o (PDist ci s p)         = Node ("PDist" <> show ci <> " " <> sdisp s) [showPred o p]
showPred _ (PCmp c a)             = Node ("a " <> show c <> " " <> show a) []
showPred _ (PEq b a)              = Node ("a " <> equalShow b <> " " <> show a) []
showPred _ (PCmp2 c)              = Node ("a " <> show c <> " a'") []
showPred _ (PEq2 b)               = Node ("a " <> equalShow b <> " a'") []
showPred _ (PMatch sop a)         = Node (showStringOperator sop "a" (show a)) []
showPred o (PRegex t _ e p)       = Node ("PRegex " <> show t) [showPred o e, showPred o p]
showPred o (PRegexI t _ e p)      = Node ("PRegexI " <> show t) [showPred o e, showPred o p]
showPred o (PRegexs rs p)         = Node ("PRegexs (" <> show (length rs) <> ")") [showPred o p]
showPred o (PRegexV rs e p)       = Node ("PRegexV (" <> show (recLen rs) <> ")") [showPred o e, showPred o p]
showPred o (PRegexN th _rx e p)   = Node ("PRegexN " <> show (dispIJ th)) [showPred o e, showPred o p]
showPred o (PRegexIP th _t _rx _rb e p) = Node ("PRegexIP" <> show (dispIJ th)) [showPred o e, showPred o p]
showPred o (PAnd p q)             = Node "PAnd" [showPred o p, showPred o q]
showPred o (POr p q)              = Node "POr" [showPred o p, showPred o q]
showPred o (PXor p q)             = Node "PXor" [showPred o p, showPred o q]
showPred o (PEquiv p q)           = Node "PEquiv" [showPred o p, showPred o q]
showPred o (PImpl p q)            = Node "PImpl" [showPred o p, showPred o q]
showPred o (PNot p)               = Node "PNot" [showPred o p]
showPred o (POps ps q)            = Node "POps" (map (showPred o) ps <> [showPred o q])
showPred o (PForAll p)            = Node "PForAll" [showPred o p]
showPred o (PZipExact ps e q)       = Node "PZipExact" (map (showPred o) ps <> [showPred o e, showPred o q])
showPred o (PSeq ps q)            = Node "PSeq" (map (showPred o) ps <> [showPred o q])
showPred o (PExists p)            = Node "PExists" [showPred o p]
showPred o (PFn s _ p)            = Node ("PFn " <> s) [showPred o p]
showPred o (PElem as)             = Node ("a `elem` " <> showElem o as) []
showPred _ (PRange a1 a2)         = Node ("a " <> showRange a1 a2) []
showPred o (PLen p)               = Node "PLen" [showPred o p]
showPred o (PBoth pa pb)          = Node "PBoth" [showPred o pa, showPred o pb]
showPred o (PFst p)               = Node "PFst" [showPred o p]
showPred o (PSnd p)               = Node "PSnd" [showPred o p]
showPred _ PNull                  = Node "PNull" []
showPred _ PEmpty                 = Node "PEmpty" []
showPred o (PIf mpexc mpb mpg p)  =
      let (xs, ys) = partitionEithers
                    [maybe (Left "exception") Right mpexc
                    ,maybe (Left "bad") Right mpb
                    ,maybe (Left "good") Right mpg
                    ]
          x1 = " skipping " <> intercalate " / " xs
      in Node ("PIf" <> (if null xs then "" else x1)) (map (showPred o) ys <> [showPred o p])

showPred o (PApp a p)             = Node ("PApp " <> show a) [showPred o p]
showPred _ (PJoin a)              = Node ("PJoin " <> show a) []
showPred o (PView _g p)           = Node "PView" [showPred o p]
showPred o (PHead e p)            = Node "PHead" [showPred o e, showPred o p]
showPred o (POne e e2 p)          = Node "POne" [showPred o e, showPred o e2, showPred o p]
showPred o (POneT e e2 p)         = Node "POneT" [showPred o e, showPred o e2, showPred o p]
showPred o (PUnconsT e p)         = Node "PUnconsT" [showPred o e, showPred o p]
showPred o (PUncons e p)          = Node "PUncons" [showPred o e, showPred o p]
showPred o (PLast e p)            = Node "PLast" [showPred o e, showPred o p]
showPred o (PUnsnocT e p)         = Node "PUnsnocT" [showPred o e, showPred o p]
showPred o (PUnsnoc e p)          = Node "PUnsnoc" [showPred o e, showPred o p]
showPred o (PIx i e p)            = Node ("PIx " <> show i) [showPred o e, showPred o p]
showPred o (PCoerce p)            = Node "PCoerce" [showPred o p]
showPred o (PPartition p pbg)     = Node "PPartition" [showPred o p, showPred o pbg]
showPred _ (POrder c)             = Node ("POrder (" <> show c <> ")") []
showPred _ (POrderEq b)           = Node ("POrderEq (" <> show b <> ")") []
showPred o (PLinear b qps)        = Node ("PLinear(" <> show (length qps) <> ") " <> show b) (imap (\i (x,y) -> Node ("Predicate i=" <> show i) [showPred o x,showPred o y]) qps)
showPred o (PSplitAt i p)         = Node ("PSplitAt " <> show i) [showPred o p]
showPred o (PBreak p p12)         = Node "PBreak" [showPred o p, showPred o p12]
showPred o (PSpan p p12)          = Node "PSpan" [showPred o p, showPred o p12]
showPred o (PEither p q)          = Node "PEither" [showPred o p, showPred o q]
showPred o (PThese p q pq)        = Node "PThese" [showPred o p, showPred o q, showPred o pq]
showPred o (PISect p)             = Node "PISect" [showPred o p]
showPred o (PISectList p)         = Node "PISectList" [showPred o p]
showPred o (PMorph _f p)          = Node "PMorph" [showPred o p]
showPred o (PMaybe p q)           = Node "PMaybe" [showPred o p, showPred o q]
showPred o (PPrism s _ p q)       = Node ("PPrism " <> s) [showPred o p, showPred o q]
showPred o (PPrismL s _ p q)      = Node ("PPrismL " <> s) [showPred o p, showPred o q]
showPred o (PPrismR s _ p q)      = Node ("PPrismR " <> s) [showPred o p, showPred o q]
showPred o (PPrismLE s _ p q)     = Node ("PPrismLE " <> s) [showPred o p, showPred o q]
showPred o (PPrismRE s _ p q)     = Node ("PPrismRE " <> s) [showPred o p, showPred o q]
showPred o (PSwap p)              = Node "PSwap" [showPred o p]
showPred o (PReverse p)           = Node "PReverse" [showPred o p]
showPred o (PChangeOpts _ p)      = Node "PChangeOpts" [showPred o p]
showPred o (PShow p)              = Node "PShow" [showPred o p]
showPred o (PShowS p)             = Node "PShowS" [showPred o p]
showPred o (PShow1 p)             = Node "PShow1" [showPred o p]
showPred o (PShowS1 p)            = Node "PShowS1" [showPred o p]
showPred o (POrDie s p)           = Node ("POrDie [" <> s <> "]") [showPred o p]
showPred o (PCatch p q)           = Node "PCatch" [showPred o p, showPred o q]
showPred o (PMsg hide s p)        = Node ("PHide " <> show hide <> " " <> s) [showPred o p]
showPred o (PTree _ p)            = Node "PTree" [showPred o p]
showPred o (PJson _ p)            = Node "PJson" [showPred o p]
showPred o (PJsonKey p q)         = Node "PJsonKey" [showPred o p, showPred o q]
showPred o (PJsonP jps p q)       = Node ("PJsonP " <> showJPaths jps) [showPred o p, showPred o q]
showPred o (PLog f p)             = Node ("PLog" <> beforeafter f) [showPred o p]
showPred o (PState f p)           = Node ("PState " <> beforeafter f) [showPred o p]
showPred o (PGet p)               = Node "PGet" [showPred o p]

instance Show a => Show (Pred z a) where
  show = drawTree . showPred o1

-- | show predicate using the default style
pp, ppu, ppv :: Show a => Pred z a -> IO ()
pp = ppWith (horizontal defOpts)

-- | show predicate using unicode
ppu = ppWith (unicode defOpts)

-- | show predicate vertically
ppv = ppWith (vertical defOpts)

-- | show predicate vertically but change the gap
ppv' :: Show a => Width -> Pred z a -> IO ()
ppv' w = ppWith (vertical' w defOpts)

-- specify options to show predicate
ppWith :: Show a => POpts -> Pred z a -> IO ()
ppWith o = prtImpl o . showPred o

----------------------------------- START JSON STUFF ----------------------------------------
-- | 'PJsonP' but converts the 'NonEmpty' 'JPath' to '[JPath]'
pjsonpNE :: NonEmpty JPath -> Pred z () -> Pred z Value -> Pred z Value
pjsonpNE = PJsonP . reverse . N.toList

-- | match on json 'Array' and pull out the value at the given index or indices
pjsonIndex :: (Int -> Bool) -> Pred z [(NonEmpty JPath, (Int, Value))] -> Pred z Value
pjsonIndex = PJson . matchIndex

-- | match on json 'Number' and pull out any numbers that satisfy the function predicate
--
--   >>> pe1' ((pjsonNumber (const True)) (psnds $ PLinear Rigid $ map (preq . peq) [24,39])) json2
--   <BLANKLINE>
--   FalseP PJson
--   |
--   +- FalseP PLinear | errors(2): NoMatch 2 | NoMatch 3
--   |  |
--   |  +- TrueP  Predicates | PZipAnd | PZipExact | (bad,good)=(0,2)
--   |  |  |
--   |  |  `- TrueP  PLift and | a=[True,True]
--   |  |     |
--   |  |     +- TrueP  i=0
--   |  |     |  |
--   |  |     |  +- TrueP  1 == 1
--   |  |     |  |
--   |  |     |  `- a == 24.0
--   |  |     |
--   |  |     `- TrueP  i=1
--   |  |        |
--   |  |        +- TrueP  1 == 1
--   |  |        |
--   |  |        `- a == 39.0
--   |  |
--   |  +- TrueP  PLinear | OneMatch 0 a=24.0 cnt=1 (i=0, a=24.0)
--   |  |  |
--   |  |  +- TrueP  i=0: 24.0 == 24.0
--   |  |  |
--   |  |  `- FalseP i=1: 24.0 == 39.0
--   |  |
--   |  +- TrueP  PLinear | OneMatch 1 a=39.0 cnt=1 (i=1, a=39.0)
--   |  |  |
--   |  |  +- FalseP i=0: 39.0 == 24.0
--   |  |  |
--   |  |  `- TrueP  i=1: 39.0 == 39.0
--   |  |
--   |  +- FalseP PLinear NoMatch 2 a=45.0
--   |  |  |
--   |  |  +- FalseP i=0: 45.0 == 24.0
--   |  |  |
--   |  |  `- FalseP i=1: 45.0 == 39.0
--   |  |
--   |  `- FalseP PLinear NoMatch 3 a=27.0
--   |     |
--   |     +- FalseP i=0: 27.0 == 24.0
--   |     |
--   |     `- FalseP i=1: 27.0 == 39.0
--   |
--   `- Debugging jpaths
--      |
--      +- i=0 | [JPIndex 0,JPKey "age",JPValue (Number 24.0)]
--      |
--      +- i=1 | [JPIndex 1,JPKey "age",JPValue (Number 39.0)]
--      |
--      +- i=2 | [JPIndex 2,JPKey "age",JPValue (Number 45.0)]
--      |
--      `- i=3 | [JPIndex 3,JPKey "age",JPValue (Number 27.0)]
--   <BLANKLINE>
--
pjsonNumber :: (Scientific -> Bool) -> Pred z [(NonEmpty JPath, Scientific)] -> Pred z Value
pjsonNumber = PJson . matchNumber

-- | match on all json 'Bool'
pjsonBool :: Pred z [(NonEmpty JPath, Bool)] -> Pred z Value
pjsonBool = PJson matchBool

-- | match on all json 'Array'
pjsonArrays :: Pred z [(NonEmpty JPath, [Value])] -> Pred z Value
pjsonArrays = PJson matchArrays

-- | match on all json 'Object'
pjsonObjects :: Pred z [(NonEmpty JPath, HashMap Text Value)] -> Pred z Value
pjsonObjects = PJson matchObjects

lnum :: (Show a, AsValue a) =>
     Int -> Int -> Pred z Scientific -> (Pred z Int, Pred z a)
lnum i j = pij i j . jnumber pfalse

-- todo: can Pred z0 Int, Pred z a work: ie z z0?
lstring :: (Show a, AsValue a) =>
     Int -> Int -> Pred z String -> (Pred z Int, Pred z a)
lstring i j = pij i j . jstring pfalse

-- dont often need this cos can use "xx" cos defined for Aeson String!
jstring :: (AsValue s, Show s) => Pred z () -> Pred z String -> Pred z s
jstring = PPrism "jstring" (^? _String . to T.unpack)

-- | converts a predicate on a json 'Value' to a predicate on Scientific. if not match then call () predicate
jnumber :: (AsValue s, Show s) => Pred z () -> Pred z Scientific -> Pred z s
jnumber = PPrism "jnumber" (^? _Number)

jnumbers :: (Foldable t, AsValue s, Show s) => Pred z ([s], [Scientific]) -> Pred z (t s)
jnumbers = PMorph (^? _Number)

-- | pull out all the numbers but fail if not all pulled
--
--   >>> pe2' (PJsonKey "AgE" $ psnds $ jnumbers' $ PShow 1) json2
--   <BLANKLINE>
--   TrueP  PJsonKey
--   |
--   +- TrueP  PMorph [Number 24.0,Number 39.0,Number 45.0,Number 27.0] bad=[] good=[24.0,39.0,45.0,27.0]
--   |  |
--   |  `- TrueP  PBoth
--   |     |
--   |     +- TrueP  PNull length=0 as=[]
--   |     |
--   |     `- TrueP  PShow
--   |        |
--   |        +- TrueP  PConst a=[24.0,39.0,45.0,27.0]
--   |        |
--   |        `- ===== PShow =====
--   |           |
--   |           +- i=0 a=24.0
--   |           |
--   |           +- i=1 a=39.0
--   |           |
--   |           +- i=2 a=45.0
--   |           |
--   |           `- i=3 a=27.0
--   |
--   `- Debugging jpaths
--      |
--      +- i=0 | key=age | [JPIndex 0,JPKey "age"] | value=Number 24.0
--      |
--      +- i=1 | key=age | [JPIndex 1,JPKey "age"] | value=Number 39.0
--      |
--      +- i=2 | key=age | [JPIndex 2,JPKey "age"] | value=Number 45.0
--      |
--      `- i=3 | key=age | [JPIndex 3,JPKey "age"] | value=Number 27.0
--   <BLANKLINE>
--
jnumbers' :: (Foldable t, AsValue s, Show s) => Pred z [Scientific] -> Pred z (t s)
jnumbers' = PMorph (^? _Number) . PBoth PNull

jstrings :: (Foldable t, AsValue s, Show s) => Pred z ([s], [String]) -> Pred z (t s)
jstrings = PMorph (^? _String . to T.unpack)

-- | pull out all the strings but fail if not all pulled
--
--   >>> pe' (PJsonKey "title" $ psnds $ jstrings' $ PShow 1) json1
--   <BLANKLINE>
--   TrueP  PJsonKey
--   |
--   +- TrueP  PMorph
--   |  |
--   |  `- TrueP  PBoth
--   |     |
--   |     +- TrueP  PNull length=0
--   |     |
--   |     `- TrueP  PShow
--   |        |
--   |        +- TrueP
--   |        |
--   |        `- ===== PShow =====
--   |           |
--   |           +- i=0 a="S"
--   |           |
--   |           `- i=1 a="example glossary"
--   |
--   `- Debugging jpaths
--      |
--      +- i=0 | key=title
--      |
--      `- i=1 | key=title
--   <BLANKLINE>
--
jstrings' :: (Foldable t, AsValue s, Show s) => Pred z [String] -> Pred z (t s)
jstrings' = PMorph (^? _String . to T.unpack) . PBoth PNull

jbools :: (Foldable t, AsValue s, Show s) => Pred z ([s], [Bool]) -> Pred z (t s)
jbools = PMorph (^? _Bool)

jbools' :: (Foldable t, AsValue s, Show s) => Pred z [Bool] -> Pred z (t s)
jbools' = PMorph (^? _Bool) . PBoth PNull

jintegral :: (AsValue s, Show s, Show a, Integral a) => Pred z () -> Pred z a -> Pred z s
jintegral = PPrism "jintegral" (^? _Integral)

jinteger :: (AsValue s, Show s) => Pred z () -> Pred z Integer -> Pred z s
jinteger = jintegral

-- | extract a Double from json 'Value'
jdouble :: (AsValue s, Show s) => Pred z () -> Pred z Double -> Pred z s
jdouble = PPrism "jdouble" (^? _Double)

-- | extract a Bool from json 'Value'
jbool :: (AsValue s, Show s) => Pred z () -> Pred z Bool -> Pred z s
jbool = PPrism "jbool" (^? _Bool)

-- | predicate for json 'Null'
jnull :: (AsValue s, Show s) => Pred z s
jnull = jnull' 0 1

jnull' :: (AsValue s, Show s) => Pred z () -> Pred z () -> Pred z s
jnull' = PPrism "jnull" (^? _Null)

jnotnull :: (AsValue s, Show s) => Pred z s
jnotnull = -jnull

jvalue :: (AsValue s, Show s) => Pred z () -> Pred z Value -> Pred z s
jvalue = PPrism "jvalue" (^? _Value)

-- | change a predicate on 'Value' to a predicate 'Array' but if fails call the () predicate
--
--   >>> :set -XOverloadedStrings
--   >>> pe' (jarray 0 $ PIx 2 0 $ PIx "firstName" 0 $ "johan") json2
--   <BLANKLINE>
--   FalseP PPrism (Just) [jarray]
--   |
--   `- FalseP PIx 2 Object (fromList [("lastName",String "Doe"),("age",Number 45.0),("firstName",String "John"),("likesPizza",Bool ...
--      |
--      `- FalseP PIx "firstName" String "John"
--         |
--         `- FalseP PStringCI String "John" == String "johan"
--   <BLANKLINE>
--
jarray :: (AsValue s, Show s) => Pred z () -> Pred z (Vector Value) -> Pred z s
jarray = PPrism "jarray" (^? _Array)

jobject :: (AsValue s, Show s) => Pred z () -> Pred z (HashMap Text Value) -> Pred z s
jobject = PPrism "jobject" (^? _Object)

-- useful cos now we can use this in PLinearOLD / PForAll / PExists
jobjectList :: (AsValue s, Show s) => Pred z () -> Pred z [(Text, Value)] -> Pred z s
jobjectList = PPrism "jobjectList" (^? _Object . to H.toList)

pjpaths :: Pred z [[JPath]] -> Pred z [(NonEmpty JPath, a)]
pjpaths = phide . PFn "pjpaths" (fmap (reverse . toList . fst))

-- psnds $ psnds -- exactly the same result
pjvalues :: Show c => Pred z [c] -> Pred z [(a, (b, c))]
pjvalues = phide . PFn "pjvalues" (fmap (snd . snd))

----------------------------------- END JSON STUFF ----------------------------------------
----------------------------------- START DATETIME STUFF ----------------------------------------

-- | finds difference between two dates in days. uses 'pcu'
--
--   >>> let dt = UTCTime (read "2018-04-19") 360
--   >>> pe' (pdays id (pgt 10)) (dt, dt & date %~ addDays 15)
--   <BLANKLINE>
--   TrueP  PFn uncurry | a=(2018-04-19 00:06:00 UTC,2018-05-04 00:06:00 UTC) | b=15
--   |
--   `- TrueP  15 > 10
--   <BLANKLINE>
--
--   >>> let dt = UTCTime (read "2018-04-19") 360
--   >>> let dt1 = UTCTime (read "2018-04-25") 380
--   >>> pe2' (pdays id (PRange 4 6)) (dt,dt1)
--   <BLANKLINE>
--   TrueP  PFn uncurry | a=(2018-04-19 00:06:00 UTC,2018-04-25 00:06:20 UTC) | b=6
--   |
--   `- TrueP  6 == [4..6]
--   <BLANKLINE>
--
pdays :: (Show a, Dateable a) => (x -> (a, a)) -> Pred z Integer -> Pred z x
pdays f = pcu f (on (flip diffDays) (^. date))

-- | finds difference between two dates in hours. uses 'pcu'
phours :: (Show a, Dateable a, Timeable a) => (x -> (a, a)) -> Pred z Integer -> Pred z x
phours f = pcu f (on (\(d, t) (d1, t1) -> 24 * diffDays d1 d  + fromIntegral (t1-t)) ((^. date) &&& (^. hours)))

-- | finds difference between two dates in minutes. uses 'pcu'
pminutes :: (Show a, Dateable a, Timeable a) => (x -> (a, a)) -> Pred z Integer -> Pred z x
pminutes f = pcu f (on (\(d, t) (d1, t1) -> 24 * 60 * diffDays d1 d  + truncate ((t1-t)/60)) ((^. date) &&& (^. timeAsDiff)))

-- | finds difference between two dates in seconds. uses 'pcu'
--
--   >>> let dt = UTCTime (read "2018-04-19") 360
--   >>> let dt1 = UTCTime (read "2018-04-19") 380
--   >>> pe2' (pseconds id (PRange 19 22)) (dt,dt1)
--   <BLANKLINE>
--   TrueP  PFn uncurry | a=(2018-04-19 00:06:00 UTC,2018-04-19 00:06:20 UTC) | b=20
--   |
--   `- TrueP  20 == [19..22]
--   <BLANKLINE>
--
pseconds :: (Show a, Dateable a, Timeable a) => (x -> (a, a)) -> Pred z Integer -> Pred z x
pseconds f = pcu f (on (\(d, t) (d1, t1) -> 24 * 60 * 60 * diffDays d1 d  + truncate (t1-t)) ((^. date) &&& (^. timeAsDiff)))

----------------------------------- END DATETIME STUFF ----------------------------------------

-- this doesnt work for Int unless we cast the predicate to @
prx :: (Show b, RecElemFCtx record V.Identity, RecElem record b b rs rs (RIndex b rs)) => Pred z b -> Pred z (record V.Identity rs)
prx = PFn "prx" recGet

-- requires AllowAmbiguousTypes also is a predicate on f a so use pri cos works for Identity
pri' :: forall n f a xs z . (Show (f a), G.KnownNat n, IndexType (Lit n) xs a) => Pred z (f a) -> Pred z (Rec f xs)
pri' =
  let i = G.natVal (Proxy @n)
  in PFn ("@" <> show i <> ".") (fromIndex (Proxy @(Lit n)))

pri :: forall n a xs z . (Show a, G.KnownNat n, IndexType (Lit n) xs a) => Pred z a -> Pred z (Rec V.Identity xs)
pri =
  let i = G.natVal (Proxy @n)
  in PFn ("@" <> show i) (V.getIdentity . fromIndex (Proxy @(Lit n)))


pnum, palpha, palphaNum :: Pred z Char
pnum = PRange '0' '9'
palpha = PLift "palpha" isAlpha
palphaNum = PLift "palphaNum" isAlphaNum

-- | match against the string but allow no match if levenshtein distance is between 1 and mx
-- also if case sensitive need to detect where the string matches but case insensitive
-- ie invalid is where CS string but matches on CI :cant use levenshtein distance cos is 0

-- so if CS then both CS and CI have to match the string or
-- both CS and CI dont match the string. if the CI matches and CS doesnt then we have an error

-- also if CS then we check that there are no values that are CI with a levenshtein distance of 1 .. mx
-- if mx < 1 then dont use it!
pdist :: SConv s => Int -> Dist z s -> [(Pred z Int, Pred z s)]
pdist mx (Dist p cs s) =
     [(p, PString cs SNone s)]
  <> [(PRange 0 0, PDist CI s (PRange 1 mx)) | mx >= 1] -- dont use if with <> cos will grab the next value in the else!
  <> case cs of
       CI -> []
       CS -> [(PRange 0 0, sci s * (-scs s))] -- tricky: if matches ci but isnt the same as cs

-- | use this with 'plinearDist' to detect simple fat fingering
--
pdists :: SConv s => Int -> [Dist z s] -> [(Pred z Int, Pred z s)]
pdists mx ps = concat $ ps <&> pdist mx

-- n is the max levenshtein distance so value cannot have a distance between 1 and n
-- eg "production" "Producxion" has a distance of 2
-- pe1 (plinearDist 2 [dreq "haskell",dopt "scala", dreq "rust", dreq "idris"]) ["idirs","haskell"]
-- pe1 (plinearDist 2 [dopt "idris"]) ["idirs","haskell"]
-- most useful if you have an optional parameter but you want to make sure it is not misspelled
--  also good with preq or pij if there are multiple values ie one correct and another misspelled

-- | only Loose makes sense with Dist cos Rigid will find all errors just using plain PLinear!
--
--   >>> pe1' (plinearDist 2 [dopt "idris"]) ["idirs","haskell"]
--   <BLANKLINE>
--   FalseP PLinear Failed Pred [Int]
--   |
--   +- FalseP Predicates | PZipAnd | PZipExact | (bad,good)=(1,2)
--   |  |
--   |  `- FalseP PLift and | a=[True,False,True]
--   |     |
--   |     +- TrueP  i=0
--   |     |  |
--   |     |  +- TrueP  0 == [0..1]
--   |     |  |
--   |     |  `- PStringCS a == "idris"
--   |     |
--   |     +- FalseP i=1
--   |     |  |
--   |     |  +- FalseP 1 > 0 (Over)
--   |     |  |
--   |     |  `- PDistCI "idris"
--   |     |     |
--   |     |     `- a `elem` [1..2]
--   |     |
--   |     `- TrueP  i=2
--   |        |
--   |        +- TrueP  0 == 0
--   |        |
--   |        `- PAnd
--   |           |
--   |           +- PStringCI a == "idris"
--   |           |
--   |           `- PNot
--   |              |
--   |              `- PStringCS a == "idris"
--   |
--   +- TrueP  PLinear | OneMatch 0 a="idirs" cnt=1 (i=1, a="idirs")
--   |  |
--   |  +- FalseP i=0: PStringCS "idirs" == "idris"
--   |  |
--   |  +- TrueP  i=1: PDistCI | dist=2 | s=idris | t=idirs
--   |  |  |
--   |  |  `- TrueP  2 == [1..2]
--   |  |
--   |  `- FalseP i=2: PAnd
--   |     |
--   |     +- FalseP PStringCI "idirs" == "idris"
--   |     |
--   |     `- TrueP  PNot
--   |        |
--   |        `- FalseP PStringCS "idirs" == "idris"
--   |
--   `- TrueP  PLinear NoMatch 1 a="haskell"
--      |
--      +- FalseP i=0: PStringCS "haskell" == "idris"
--      |
--      +- FalseP i=1: PDistCI | dist=7 | s=idris | t=haskell
--      |  |
--      |  `- FalseP 7 > 2 (Over)
--      |
--      `- FalseP i=2: PAnd
--         |
--         +- FalseP PStringCI "haskell" == "idris"
--         |
--         `- TrueP  PNot
--            |
--            `- FalseP PStringCS "haskell" == "idris"
--   <BLANKLINE>
--
plinearDist :: (Foldable t, SConv s) => Int -> [Dist z s] -> Pred z (t s)
plinearDist n ds = PLinear Loose (pdists n ds)

-- | used by 'plinearDist' to look for a match on s and not allowed to match on values that are at least 1 unit distance from it
-- ie looks for fat fingering
data Dist z s = Dist (Pred z Int) Case s deriving (Show,Eq)

-- | required
dreq :: s -> Dist z s
dreq = Dist preq' CS

dopt :: s -> Dist z s
dopt = Dist popt' CS

dij :: Int -> Int -> s -> Dist z s
dij i j = Dist (PRange i j) CS

dnever :: s -> Dist z s
dnever = Dist (PRange 0 0) CS

dreqCI :: s -> Dist z s
dreqCI = Dist preq' CI

doptCI :: s -> Dist z s
doptCI = Dist popt' CI

dijCI :: Int -> Int -> s -> Dist z s
dijCI i j = Dist (PRange i j) CI

dneverCI :: s -> Dist z s
dneverCI = Dist (PRange 0 0) CI

-- | prefix match: most common version is fail if no match and use Longest match
--
--   >>> pe2' (pregex (((,,) . read @Int) <$> some (psym isDigit) <*> few (sym 'x') <*> some (psym isDigit)) $ 1) "123x1"
--   <BLANKLINE>
--   TrueP  PRegex RLong as="123x1" b=(123,"x","1") rs=""
--   |
--   `- TrueP  PConst a=((123,"x","1"),"")
--   <BLANKLINE>
--
--   >>> pe2' (pregex (((,,) . read @Int) <$> some (psym isDigit) <*> few (psym isDigit) <*> some (psym isDigit)) $ 1) "123x1"
--   <BLANKLINE>
--   TrueP  PRegex RLong as="123x1" b=(12,"","3") rs="x1"
--   |
--   `- TrueP  PConst a=((12,"","3"),"x1")
--   <BLANKLINE>
--
--   >>> pe2' (pregex (((,,) . read @Int) <$> some (psym isDigit) <*> few (psym isDigit) <*> some (psym isDigit)) $ 1) "1231"
--   <BLANKLINE>
--   TrueP  PRegex RLong as="1231" b=(123,"","1") rs=""
--   |
--   `- TrueP  PConst a=((123,"","1"),"")
--   <BLANKLINE>
--
--   >>> pe2' (pregex ((,,) <$> ratio <* sym 'x' <*> few (psym isDigit) <*> int) 1) "123x987"
--   <BLANKLINE>
--   TrueP  PRegex RLong as="123x987" b=(123 % 1,"",987) rs=""
--   |
--   `- TrueP  PConst a=((123 % 1,"",987),"")
--   <BLANKLINE>
--
pregex  :: (Foldable t, Show a, Show b) => RE a b -> Pred z (b,[a]) -> Pred z (t a)
pregex r = PRegex RLong r 0

-- | infix match: most common version is fail if no match and use Longest match
--
--   >>> pe2' (pregexi (read @Int <$> some (psym isDigit)) 1) "abc123def"
--   <BLANKLINE>
--   TrueP  PRegexI RLong as="abc123def" b=123 used="abc" remaining="def"
--   |
--   `- TrueP  PConst a=("abc",123,"def")
--   <BLANKLINE>
--
--   >>> pe2' (pregexi (read @Int <$> some (psym isDigit)) $ p_2 (pgt 122)) "abc123def"
--   <BLANKLINE>
--   TrueP  PRegexI RLong as="abc123def" b=123 used="abc" remaining="def"
--   |
--   `- TrueP  PFn _2 | a=("abc",123,"def") | b=123
--      |
--      `- TrueP  123 > 122
--   <BLANKLINE>
--
--   >>> pe2' (pregex ((read @Integer <$> some (psym isDigit)) <|> pure 999) $ p_1 (pgt 122)) "123def"
--   <BLANKLINE>
--   TrueP  PRegex RLong as="123def" b=123 rs="def"
--   |
--   `- TrueP  PFn _1 | a=(123,"def") | b=123
--      |
--      `- TrueP  123 > 122
--   <BLANKLINE>
--
--   >>> pe2' (pregexi ((read @Int <$> some (psym isDigit)) <|> pure 999) $ p_2 (pgt 122)) "abc123def"
--   <BLANKLINE>
--   TrueP  PRegexI RLong as="abc123def" b=999 used="" remaining="abc123def"
--   |
--   `- TrueP  PFn _2 | a=("",999,"abc123def") | b=999
--      |
--      `- TrueP  999 > 122
--   <BLANKLINE>
--
--   >>> pe2' (pregexi (intersperseNP 4 (sym '.') int) $ p_1 PNull * p_2 (PForAll (ple 255)) * p_2 (PLen (peq 4))) "start123.223.1.256end"
--   <BLANKLINE>
--   FalseP PRegexI RLong as="start123.223.1.256end" b=[123,223,1,256] used="start" remaining="end"
--   |
--   `- FalseP PAnd
--      |
--      +- FalseP PAnd
--      |  |
--      |  +- FalseP PFn _1 | a=("start",[123,223,1,256],"end") | b="start"
--      |  |  |
--      |  |  `- FalseP PNull length=5 as="start"
--      |  |
--      |  `- FalseP PFn _2 | a=("start",[123,223,1,256],"end") | b=[123,223,1,256]
--      |     |
--      |     `- FalseP PForAll | cnt=1 (i=3, a=256)
--      |        |
--      |        +- TrueP  i=0: 123 <= 255
--      |        |
--      |        +- TrueP  i=1: 223 <= 255
--      |        |
--      |        +- TrueP  i=2: 1 <= 255
--      |        |
--      |        `- FalseP i=3: 256 <= 255
--      |
--      `- TrueP  PFn _2 | a=("start",[123,223,1,256],"end") | b=[123,223,1,256]
--         |
--         `- TrueP  PLen 4 as=[123,223,1,256]
--            |
--            `- TrueP  4 == 4
--   <BLANKLINE>
--
pregexi :: (Foldable t, Show a, Show b) => RE a b -> Pred z ([a],b,[a]) -> Pred z (t a)
pregexi r = PRegexI RLong r 0

-- | most common usecase. match all 'peq2' and use 'RLong' ie longest match
--
--   >>> :set -XOverloadedStrings
--   >>> pe2' (pregexs [int, "." *> int, "." *> int, "." *> int] $ PBoth (PLen (peq 4) * PForAll (PRange 0 255)) PNull) "123.33.281.2abcdef"
--   <BLANKLINE>
--   FalseP PRegexs (4) | matched all(4) | leftovers="abcdef" | as="123.33.281.2abcdef"
--   |
--   +- FalseP PBoth
--   |  |
--   |  +- TrueP  PEq2 4 == 4
--   |  |
--   |  `- FalseP PBoth
--   |     |
--   |     +- FalseP PAnd
--   |     |  |
--   |     |  +- TrueP  PLen 4 as=[123,33,281,2]
--   |     |  |  |
--   |     |  |  `- TrueP  4 == 4
--   |     |  |
--   |     |  `- FalseP PForAll | cnt=1 (i=2, a=281)
--   |     |     |
--   |     |     +- TrueP  i=0: 123 == [0..255]
--   |     |     |
--   |     |     +- TrueP  i=1: 33 == [0..255]
--   |     |     |
--   |     |     +- FalseP i=2: 281 > 255 (Over)
--   |     |     |
--   |     |     `- TrueP  i=3: 2 == [0..255]
--   |     |
--   |     `- FalseP PNull length=6 as="abcdef"
--   |
--   `- matched all(4) | leftovers="abcdef"
--      |
--      +- i=0 | b=123 | used="123" | remaining=".33.281.2abcdef"
--      |
--      +- i=1 | b=33 | used=".33" | remaining=".281.2abcdef"
--      |
--      +- i=2 | b=281 | used=".281" | remaining=".2abcdef"
--      |
--      `- i=3 | b=2 | used=".2" | remaining="abcdef"
--   <BLANKLINE>
--
--
--   >>> pe2' (pregexs (int : replicate 3 ("." *> int)) 1) "123.33.1.2"
--   <BLANKLINE>
--   TrueP  PRegexs (4) | matched all(4) | leftovers="" | as="123.33.1.2"
--   |
--   +- TrueP  PBoth
--   |  |
--   |  +- TrueP  PEq2 4 == 4
--   |  |
--   |  `- TrueP  PConst a=([123,33,1,2],"")
--   |
--   `- matched all(4) | leftovers=""
--      |
--      +- i=0 | b=123 | used="123" | remaining=".33.1.2"
--      |
--      +- i=1 | b=33 | used=".33" | remaining=".1.2"
--      |
--      +- i=2 | b=1 | used=".1" | remaining=".2"
--      |
--      `- i=3 | b=2 | used=".2" | remaining=""
--   <BLANKLINE>
--
--   >>> :set -XOverloadedStrings
--   >>> pe2' (pregexs [int, "." *> int, "." *> int, "." *> int] $ PBoth (PLen (peq 4) * PForAll (PRange 0 255)) PNull) "123.33x.281.2abcdef"
--   <BLANKLINE>
--   FalseP PRegexs (4) | only matched 2 of {4} | leftovers="x.281.2abcdef" | as="123.33x.281.2abcdef"
--   |
--   +- FalseP PBoth
--   |  |
--   |  +- FalseP not all matched | PEq2 4 == 2
--   |  |
--   |  `- FalseP PBoth
--   |     |
--   |     +- FalseP PAnd
--   |     |  |
--   |     |  +- FalseP PLen 2 as=[123,33]
--   |     |  |  |
--   |     |  |  `- FalseP 2 == 4
--   |     |  |
--   |     |  `- TrueP  PForAll
--   |     |     |
--   |     |     +- TrueP  i=0: 123 == [0..255]
--   |     |     |
--   |     |     `- TrueP  i=1: 33 == [0..255]
--   |     |
--   |     `- FalseP PNull length=13 as="x.281.2abcdef"
--   |
--   `- only matched 2 of {4} | leftovers="x.281.2abcdef"
--      |
--      +- i=0 | b=123 | used="123" | remaining=".33x.281.2abcdef"
--      |
--      `- i=1 | b=33 | used=".33" | remaining="x.281.2abcdef"
--   <BLANKLINE>
--
--   >>> :set -XOverloadedStrings
--   >>> pe2' (pregexs (replicate 6 (double <* spaces)) $ PFst $ PForAll (PRange 54 304)) "213   1223 23    55 99 1111    8x"
--   <BLANKLINE>
--   FalseP PRegexs (6) | matched all(6) | leftovers="8x" | as="213   1223 23    55 99 1111    8x"
--   |
--   +- FalseP PBoth
--   |  |
--   |  +- TrueP  PEq2 6 == 6
--   |  |
--   |  `- FalseP PFst a=[213.0,1223.0,23.0,55.0,99.0,1111.0] snd="8x"
--   |     |
--   |     `- FalseP PForAll | cnt=3 (i=1, a=1223.0)
--   |        |
--   |        +- TrueP  i=0: 213.0 == [54.0..304.0]
--   |        |
--   |        +- FalseP i=1: 1223.0 > 304.0 (Over)
--   |        |
--   |        +- FalseP i=2: 23.0 < 54.0 (Under)
--   |        |
--   |        +- TrueP  i=3: 55.0 == [54.0..304.0]
--   |        |
--   |        +- TrueP  i=4: 99.0 == [54.0..304.0]
--   |        |
--   |        `- FalseP i=5: 1111.0 > 304.0 (Over)
--   |
--   `- matched all(6) | leftovers="8x"
--      |
--      +- i=0 | b=213.0 | used="213   " | remaining="1223 23    55 99 1111    8x"
--      |
--      +- i=1 | b=1223.0 | used="1223 " | remaining="23    55 99 1111    8x"
--      |
--      +- i=2 | b=23.0 | used="23    " | remaining="55 99 1111    8x"
--      |
--      +- i=3 | b=55.0 | used="55 " | remaining="99 1111    8x"
--      |
--      +- i=4 | b=99.0 | used="99 " | remaining="1111    8x"
--      |
--      `- i=5 | b=1111.0 | used="1111    " | remaining="8x"
--   <BLANKLINE>
--
--   >>> :set -XOverloadedStrings
--   >>> pe2' (pregexs (replicate 6 (int <* spaces)) $ PFst $ PForAll (PRange 100 204)) "213   1223 23    55"
--   <BLANKLINE>
--   FalseP PRegexs (6) | only matched 4 of {6} | leftovers="" | as="213   1223 23    55"
--   |
--   +- FalseP PBoth
--   |  |
--   |  +- FalseP not all matched | PEq2 6 == 4
--   |  |
--   |  `- FalseP PFst a=[213,1223,23,55] snd=""
--   |     |
--   |     `- FalseP PForAll | cnt=4 (i=0, a=213)
--   |        |
--   |        +- FalseP i=0: 213 > 204 (Over)
--   |        |
--   |        +- FalseP i=1: 1223 > 204 (Over)
--   |        |
--   |        +- FalseP i=2: 23 < 100 (Under)
--   |        |
--   |        `- FalseP i=3: 55 < 100 (Under)
--   |
--   `- only matched 4 of {6} | leftovers=""
--      |
--      +- i=0 | b=213 | used="213   " | remaining="1223 23    55"
--      |
--      +- i=1 | b=1223 | used="1223 " | remaining="23    55"
--      |
--      +- i=2 | b=23 | used="23    " | remaining="55"
--      |
--      `- i=3 | b=55 | used="55" | remaining=""
--   <BLANKLINE>
--
pregexs :: (Foldable t, Eq a, Show a, Show b) => [RE a b] -> Pred z ([b],[a]) -> Pred z (t a)
pregexs rs p = pregexs' RLong rs (PBoth (pmsgIfNotTrue "not all matched" peq2) p)

-- | tack on 'RType'
pregexs' :: (Foldable t, Eq a, Show a, Show b) => RType -> [RE a b] -> Pred z ((Int,Int),([b],[a])) -> Pred z (t a)
pregexs' t = PRegexs . map (t,)

{-
-- | mconcat the result: made sense when we used Stash but now replaced by PRegexV
pregexsS :: (Foldable t, Eq a, Show a, Show b, Monoid b) =>
                   [RE a b] -> Pred z (b, [a]) -> Pred z (t a)
pregexsS rs = pregexs rs . phide . PFn "mconcat" (first mconcat)
-}

-- | most useful use of PRegexN
--   >>> pe2' (pregexN (These 3 5) (spaces *> _d) 0 1) "12  34   56"
--   <BLANKLINE>
--   TrueP  PRegexN {3,5} | matched all(5) | leftovers="6"
--   |
--   +- TrueP  PConst a=("12345","6")
--   |
--   `- matched all(5) | leftovers="6"
--      |
--      +- i=0 | b='1' | used="1" | remaining="2  34   56"
--      |
--      +- i=1 | b='2' | used="2" | remaining="  34   56"
--      |
--      +- i=2 | b='3' | used="  3" | remaining="4   56"
--      |
--      +- i=3 | b='4' | used="4" | remaining="   56"
--      |
--      `- i=4 | b='5' | used="   5" | remaining="6"
--   <BLANKLINE>
--
pregexN :: (Foldable t, Eq a, Show a, Show b) => These Int Int -> RE a b -> Pred z ((Int, Int), [a]) -> Pred z ([b], [a]) -> Pred z (t a)
pregexN th = PRegexN th . (RLong,)

--pregexIP :: These Int Int -> RE a x -> RE a b ->
--pregexIP th delim regex = pregex regex $ PBoth [delim *> regex] PRegexN th . N.fromList . map (RLong,)

porder :: (Foldable t, Show a) => (a -> a -> Bool) -> Pred z (t a)
porder cmp = pgroupBy cmp $ POne 0 0 1

-- | runs 'PISect' after getting rid of duplicates
--
--   >>> :set -XTypeApplications
--   >>> pe2' (pisectNub @[] 1) ("aaabc","adbbef")
--   <BLANKLINE>
--   TrueP  PISect as="abc" bs="adbef" left="c" isect="ab" right="def"
--   |
--   `- TrueP  PConst a=("c","ab","def")
--   <BLANKLINE>
--
--   >>> :set -XTypeApplications
--   >>> pe1' (pisectNub @[] 1) ("aaabc","adef")
--   <BLANKLINE>
--   TrueP  PISect left="bc" isect="a" right="def"
--   |
--   `- TrueP  PConst a=("bc","a","def")
--   <BLANKLINE>
--
--   >>> :set -XTypeApplications
--   >>> pe1' (pisectNub @[] 1) ("aaabc","adef")
--   <BLANKLINE>
--   TrueP  PISect left="bc" isect="a" right="def"
--   |
--   `- TrueP  PConst a=("bc","a","def")
--   <BLANKLINE>
--
--   >>> :set -XTypeApplications
--   >>> pe1' (pisectNub @[] 1) ("aaabc","adbbef")
--   <BLANKLINE>
--   TrueP  PISect left="c" isect="ab" right="def"
--   |
--   `- TrueP  PConst a=("c","ab","def")
--   <BLANKLINE>
--
pisectNub :: (Foldable t, Ord a, Show a) => Pred z ([a], [a], [a]) -> Pred z (t a, t a)
pisectNub = phide . pstar2 "nub" (nub . toList) . PISect

-- | runs 'PISectList' after getting rid of duplicates
pisectListNub :: (Foldable t, Foldable u, Ord a, Show a) =>
  Pred z ([a], [a]) -> Pred z (u (t a))
pisectListNub = phide . pfn (fmap (nub . toList) . toList) . PISectList

-- | lifted version of 'Control.Arrow.first'
pfirst :: (Show b, Show x) => (a -> b) -> Pred z (b, x) -> Pred z (a, x)
pfirst = PFn "pfirst" . first

-- | lifted version of 'Control.Arrow.second'
psecond :: (Show b, Show x) => (a -> b) -> Pred z (x, b) -> Pred z (x, a)
psecond = PFn "psecond" . second

newtype App s r a = App { unApp :: S.StateT s (R.ReaderT r Identity) a }
  deriving (Monad, R.MonadReader r, S.MonadState s, Applicative, Functor)

data Config z = Config { _cLog :: Seq String, _cZ :: z, _cCnt :: Map String Int } deriving Show

--instance TD.ToExpr z => TD.ToExpr (Config z)

cLog :: Lens' (Config z) (Seq String)
cLog afb c = (\b -> c { _cLog = b }) <$> afb (_cLog c)

cZ :: Lens (Config z) (Config z1) z z1
cZ afb c = (\b -> c { _cZ = b }) <$> afb (_cZ c)

cCnt :: Lens' (Config z) (Map String Int)
cCnt afb c = (\b -> c { _cCnt = b }) <$> afb (_cCnt c)

instance Semigroup z => Semigroup (Config z) where
  Config a b c <> Config a1 b1 c1 = Config (a<>a1) (b<>b1) (M.unionWith (+) c c1)

instance Monoid z => Monoid (Config z) where
  mempty = Config mempty mempty mempty

add1 :: S.MonadState (Config z) m => String -> m ()
add1 nm = cCnt %= M.insertWith (+) nm 1

add11 :: (R.MonadReader POpts m, S.MonadState (Config z) m) => String -> m (POpts,Int)
add11 nm = cCnt %= M.insertWith (+) nm 1 >> R.asks (id &&& oHide)

eval :: (PES z, Show a) => POpts -> Pred z a -> a -> (TT, Config z)
eval o p = flip R.runReader o . flip S.runStateT mempty . unApp . eval' p

eval' :: (PES z, Show a) => Pred z a -> a -> App (Config z) POpts TT


eval' (PConst b) a = do
  let nm = "PConst"
  (opts,_) <- add11 nm
  return $ Node (b & peStrings %~ ([showLit opts 1 "" nm <> showA opts 1 " a=" a] <>)) []

eval' (PLift s ab) a = do
  let nm = "PLift" `stringAp` s
  (opts,_) <- add11 nm
  return $ mkNode (_BoolP # ab a, [nm, showA opts 1 "a=" a]) []

eval' (PFn s ab p) a = do
  let nm = "PFn" `stringAp` s
  (opts,n) <- add11 nm
  if n>0 then R.local (\o -> o { oHide = n-1 }) $ eval' p (ab a)
  else do
    ll <- eval' p (ab a)
    return $ mkNode (getBool ll, [nm, showA opts 0 "a=" a, showA opts 0 "b=" (ab a)]) [ll]

eval' (PString ci sop s) t = do
  let nm0 = "PString" <> show ci
      nm = nm0 <> " " <> fromStringOperator sop
      b = scompare ci sop s t
  (opts,_) <- add11 nm
  return $ mkNode (_BoolP # b, [nm0 <> " " <> showStringOperator sop (showLit opts 0 "" (sdisp t)) (showLit opts 0 "" (sdisp s))]) []

eval' (PDist ci s p) t = do
  let nm = "PDist" <> show ci
      d = dist ci (sstring s) (sstring t)
  ll <- eval' p d
  (opts,_) <- add11 nm
  return $ mkNode (getBool ll, [nm, "dist=" <> show d, showLit opts 1 "s=" (sstring s), showLit opts 1 "t=" (sstring t)]) [ll]

eval' (PCmp c a') a = do
  let nm = show c <> " " <> show a'
  (opts,_) <- add11 ("PCmp(" <> nm <> ")")
  let b = snd (ccmp c) a a'
  return $ mkNode (_BoolP # b, [showA opts 0 "" a <> " " <> nm]) []

eval' (PEq isequal a') a = do
  let nm = equalShow isequal <> " " <> show a'
  (opts,_) <- add11 ("PEq2(" <> nm <> ")")
  let b = isequal == (a == a')
  return $ mkNode (_BoolP # b, [showA opts 0 "" a <> " " <> nm]) []

eval' (PCmp2 c) (a, a') = do
  let nm = show c
  (opts,_) <- add11 ("PCmp2(" <> nm <> ")")
  let b = snd (ccmp c) a a'
  return $ mkNode (_BoolP # b, ["PCmp2 " <> showA opts 0 "" a <> " " <> nm <> showA opts 0 " " a']) []

eval' (PEq2 isequal) (a, a') = do
  let nm = equalShow isequal
  (opts,_) <- add11 nm
  let b = isequal == (a == a')
  return $ mkNode (_BoolP # b, ["PEq2 " <> showA opts 0 "" a <> " " <> nm <> showA opts 0 " " a']) []

eval' (PMatch sop as') (toList -> as) = do
  let nm = "PMatch " <> fromStringOperator sop
  (opts,_) <- add11 nm
  let fn = case sop of
            SNone -> (==)
            SPrefix -> isPrefixOf
            SInfix -> isInfixOf
            SSuffix -> isSuffixOf
  let b = as' `fn` as
  return $ mkNode (_BoolP # b, ["PMatch " <> showStringOperator sop (showA opts 0 "" as) (showA opts 0 "" as')]) []

eval' (PRegexs regexs p) (toList -> as) = do
  let nm = "PRegexs (" <> show (length regexs) <> ")"
  (opts,_) <- add11 nm
  let rs = runRegexs (N.fromList regexs) as
  let leftovers = rs ^? _last . _3 ^. non as
  let (lrmsgs,tt) = regexsToTT opts (join These (length regexs)) leftovers rs
  ll <- eval' p ((length regexs, length rs), (unzip3 rs ^. _1, leftovers))
--  let msg | length rs == length regexs = "matched all"
--          | null rs = "matched none"
--          | otherwise = "only matched " <> show (length rs)
  return $ mkNode (getBool ll, [nm] <> either id id lrmsgs <> [showA opts 2 "as=" as]) [ll,tt]

eval' (PRegexV regexs e p) s = do
  let nm = "PRegexV (" <> show (recLen regexs) <> ")"
  (_opts,_) <- add11 nm
  let fr (RResult i aa used remn) = mkNodeDebug (TrueP, ["i=" <> show i, aa, "used=" <> used, "remaining=" <> remn]) []
  case evalRXHolder s (toRXHolder regexs) of
    (ws, Left remn) -> do
       let msgs = ["only matched " <> show (length ws) <> " of " <> show (recLen regexs),"leftovers=" <> remn]
       let ns = mkNodeDebug (TrueP, msgs) (map fr ws)
       ll <- eval' e remn
       return $ mkNode (getBool ll, [nm] <> msgs) [ll,ns]
    (ws, Right ((_,remn),rec)) -> do
       let msgs = ["matched all", "leftovers=" <> remn]
       let ns = mkNodeDebug (TrueP, ["matched all", "leftovers=" <> remn]) (map fr ws)
       ll <- eval' p (rec,remn)
       return $ mkNode (getBool ll, [nm] <> msgs) [ll,ns]

eval' (PRegex t regex e p) (toList -> as) = do
  let nm = "PRegex " <> show t
  (opts,_) <- add11 nm
  case rprefix t regex as of
    Nothing -> addMessagePre (nm <> " no regex match") <$> eval' e ()
    Just (b,rs) -> do
                     ll <- eval' p (b,rs)
                     return $ mkNode (getBool ll, [nm <> showA opts 1 " as=" as <> showA opts 1 " b=" b <> showA opts 1 " rs=" rs]) [ll]

eval' (PRegexI t regex e p) (toList -> as) = do
  let nm = "PRegexI " <> show t
  (opts,_) <- add11 nm
  case rinfix t regex as of
    Nothing -> addMessagePre (nm <> " no regex match") <$> eval' e ()
    Just z@(before,b,after) -> do
                     ll <- eval' p z
                     return $ mkNode (getBool ll, [nm <> showA opts 1 " as=" as <> showA opts 1 " b=" b <> showA opts 1 " used=" before <> showA opts 1 " remaining=" after]) [ll]

eval' (PRegexN thij regex e p) (toList -> as) = do
  let nm = "PRegexN " <> dispIJ thij
  (opts,_) <- add11 nm
  let (rs,leftovers) = runRegexN thij regex as
      (lrmsgs,tt) = regexsToTT opts thij leftovers rs
      ii = these id (const 0) const thij
  case lrmsgs of
       Left msgs -> do
         ll <- eval' e ((length rs, ii), leftovers)
         return $ mkNode (getBool ll, [nm] <> msgs) [ll,tt]
       Right msgs -> do
         ll <- eval' p (rs ^.. traverse . _1, leftovers)
         return $ mkNode (getBool ll, [nm] <> msgs) [ll,tt]

eval' (PRegexIP thij t rdelim regex e p) (toList -> as) = do
  let nm = "PRegexIP" <> dispIJ thij
  (opts,_) <- add11 nm
  let ii = these id (const 0) const thij
  if theseRight (<=0) False thij then do
     ll <- eval' e ((0, ii), as)
     return $ mkNode (getBool ll, [nm,"noop as max <= 0"]) [ll]
  else case rprefix t regex as of
    Nothing -> do
         ll <- eval' e ((0, ii), as)
         return $ mkNode (getBool ll, [nm,"matched nothing"]) [ll]
    Just (b,as') -> do
                      let newthij = bimapThese pred pred thij
                      let (rs,leftovers) = runRegexN newthij (t, rdelim *> regex) as'
                          -- force in the first match into rs
                          (lrmsgs,tt) = regexsToTT opts thij leftovers ((b, take (length as - length as') as, as'):rs)
                      case lrmsgs of
                           Left msgs -> do
                             ll <- eval' e ((length rs, ii), leftovers)
                             return $ mkNode (getBool ll, [nm] <> msgs) [ll,tt]
                           Right msgs -> do
                             ll <- eval' p (b: rs ^.. traverse . _1, leftovers)
                             return $ mkNode (getBool ll, [nm] <> msgs) [ll,tt]

eval' (PRange a1 a2) a = do
  opts <- R.ask
  let nm = showRange a1 a2
  add1 nm
  let (b,msg) = between' a1 a2 a
  return $ mkNode (_BoolP # (b == EQ), [showA opts 0 "" a <> showLit opts 0 " " msg]) []

eval' (PElem as) a = do
  opts <- R.ask
  let nm = "`elem` " <> showElem opts as
  add1 nm
  return $ mkNode (_BoolP # (a `elem` as), [showA opts 0 "" a <> " " <> nm]) []

eval' (PLen p) as = do
  let nm = "PLen"
  (opts,_) <- add11 nm
  ll <- eval' p (length as)
  return $ mkNode (getBool ll, [nm <> " " <> show (length as) <> showA opts 1 " as=" as]) [ll]

eval' PEmpty s = do
  let nm = "PEmpty"
  (opts,_) <- add11 nm
  return $ mkNode (_BoolP # is _Empty s, [nm <> showA opts 1 " s=" s]) []

eval' PNull as = do
  let nm = "PNull"
  (opts,_) <- add11 nm
  return $ mkNode (_BoolP # null as, [nm <> " length=" <> show (length as) <> showA opts 1 " as=" as]) []

eval' (PBoth pa pb) (a, b) = do
  let nm = "PBoth"
  add1 nm
  evalBinStrict nm (&&) <$> eval' pa a <*> eval' pb b

eval' (PFst p) (a, x) = do
  let nm = "PFst"
  (opts,n) <- add11 nm
  if n > 0 then R.local (\o -> o { oHide = n-1 }) $ eval' p a
  else do
         ll <- eval' p a
         return $ mkNode (getBool ll, [nm <> showA opts 1 " a=" a <> showA opts 1 " snd=" x]) [ll]

eval' (PSnd p) (x, a) = do
  let nm = "PSnd"
  (opts,n) <- add11 nm
  if n > 0 then R.local (\o -> o { oHide = n-1 }) $ eval' p a
  else do
         ll <- eval' p a
         return $ mkNode (getBool ll, [nm <> showA opts 1 " a=" a <> showA opts 1 " fst=" x]) [ll]

eval' (PSwap p) pab = do
  let nm = "PSwap"
  (opts,_) <- add11 nm
  rr <- eval' p (pab ^. swapped)
  return $ mkNode (getBool rr, [nm <> showA opts 1 " a,b=" pab]) [rr]

eval' (PReverse p) t = do
  let nm = "PReverse"
  (opts,_) <- add11 nm
  rr <- eval' p (t ^. reversed)
  return $ mkNode (getBool rr, [nm <> showA opts 1 " a,b=" t]) [rr]

eval' (PSplitAt i p) (toList -> as) = do
  let nm = "PSplitAt " <> show i
      n = length as
      (as1,as2) = if i>=0 then splitAt i as
                  else splitAt (n+i) as ^. swapped
      msg1 = ["out of range(" <> show n <> ")" | abs i > n]
  (opts,_) <- add11 nm
  ll <- eval' p (as1,as2)
  return $  mkNode (getBool ll, [nm] <> msg1 <> [showA opts 1 "lhs=" as1 <> showA opts 1 " rhs=" as2]) [ll]

eval' (PAnd p q) a = do
  let nm = "PAnd"
  add1 nm
  evalBinStrict nm (&&) <$> eval' p a <*> eval' q a

eval' (POr p q) a = do
  let nm = "POr"
  add1 nm
  evalBinStrict nm (||) <$> eval' p a <*> eval' q a

eval' (PXor p q) a = do
  let nm = "PXor"
  add1 nm
  evalBinStrict nm (/=) <$> eval' p a <*> eval' q a

eval' (PEquiv p q) a = do
  let nm = "PEquiv"
  add1 nm
  evalBinStrict nm (==) <$> eval' p a <*> eval' q a

eval' (PImpl p q) a = do
  let nm = "PImpl"
  add1 nm
  evalBinStrict nm impl <$> eval' p a <*> eval' q a

eval' (PNot p) a = do
  let nm = "PNot"
  add1 nm
  ll <- eval' p a
  return $ mkNode (getBool ll & _BoolP %~ not, [nm])  [ll]

eval' (POps ps q) a = do
  let nm = "POps"
  (opts,_) <- add11 nm
  ts <- zipWithM (\i p -> ((i, a),) <$> eval' p a) [0::Int ..] ps
  case splitAndP opts [nm] ts of
    Left e -> return e
    Right (bads,goods) -> do
      let xs = ts ^.. traverse . _2 . root . peBoolP . _BoolP
      ll <- eval' q xs
      let ll' = ll & branches %~ (<> map fixit ts)
      return $ mkNode (getBool ll, [nm] <> [show (length bads, length goods)]) [ll']

-- todo: need to limit output ala PForAll
eval' (POrder c) (toList -> as) = do
  opts <- R.ask
  let nm = "POrder"
      xs = isSorted c as
      (ts, (_je, msg1)) = orderImpl opts xs
  add1 (nm <> "(" <> show c <> ")")
  return $ mkNode (_BoolP # all fst xs, [nm <> " (" <> show c <> ")" <> msg1]) (map fixit ts)

eval' (POrderEq bb) (toList -> as) = do
  opts <- R.ask
  let nm = "POrderEq"
      xs = isSortedEq bb as
      (ts, (_je, msg1)) = orderImpl opts xs
  add1 (nm <> "(" <> equalShow bb <> ")")
  return $ mkNode (_BoolP # all fst xs, [nm <> " (" <> equalShow bb <> ")" <> msg1]) (map fixit ts)

eval' (PChangeOpts f p) a = do
  opts <- R.ask
  let nm = "PChangeOpts"
      optsnew = f opts
      n = oHide optsnew
  add1 nm
  if n > 0 then R.local (\o -> (f o) { oHide = n-1 }) $ eval' p a
  else do
         ll <- R.local f $ eval' p a
         let df2 = let dfs = diffOpts opts optsnew
                       ss = " diff(" <> show (length dfs) <> ") [" <> intercalate " | " dfs <> "]"
                   in if null dfs then " no diff" else ss
         return $ mkNode (getBool ll, [nm <> df2 <> showA optsnew 2 " new=" optsnew <> showA opts 2 " old=" opts]) [ll]

eval' (PShow1 p) a = do
  opts <- R.ask
  let nm = "PShow1"
  add1 nm
  ll <- eval' p a
  return $ let n1 = mkNodeDebug (TrueP, [showA opts 0 "a=" a]) []
           in mkNode (getBool ll, [nm]) [ll, n1]

eval' (PShowS1 p) a = do
  opts <- R.ask
  let nm = "PShowS1"
  add1 nm
  ll <- eval' p a
  return $ let n1 = mkNodeDebug (TrueP, [showLit opts 0 "a=" (sstring a)]) []
           in mkNode (getBool ll, [nm]) [ll, n1]

eval' (PShow p) (toList -> as) = do
  opts <- R.ask
  ll <- eval' p as
  let nm = "PShow"
      mm = mkNodeDebug (TrueP, ["===== " <> nm <> " ====="]) ns
      ns = zipWith (\i a -> mkNodeDebug (TrueP, ["i=" <> show i <> showA opts 0 " a=" a]) []) [0::Int ..] as
  add1 nm
  return $ mkNode (getBool ll, [nm]) [ll, mm]

eval' (PShowS p) (toList -> as) = do
  opts <- R.ask
  ll <- eval' p as
  let nm = "PShowS"
      mm = mkNodeDebug (TrueP, ["===== " <> nm <> " ====="]) ns
      ns = zipWith (\i a -> mkNodeDebug (TrueP, ["i=" <> show i <> showLit opts 0 " a=" (sstring a)]) []) [0::Int ..] as
  add1 nm
  return $ mkNode (getBool ll, [nm]) [ll, mm]

eval' (POrDie s p) a = do
  let nm = "POrDie " <> s
  add1 nm
  ll <- eval' p a
  return $ case getBool ll of
       TrueP -> mkNode (TrueP, [nm <> ":ok"]) [ll]
       FalseP -> mkNode (FailP (s :| []), [nm <> ": found False"]) [ll]
       FailP es -> mkNode (FailP (s N.<| es), [nm <> ": found Exception"]) [ll]

eval' (PCatch e p) a = do
  let nm = "PCatch"
  add1 nm
  ll <- eval' p a
  case getBool ll of
     FailP excs -> do
                       ee <- eval' e a
                       return $ mkNode (getBool ee, [nm <> ":Exception caught"] <> toList excs) [ee, ll]
     _ -> return $ mkNode (getBool ll, [nm <> ":no exception"]) [ll]

eval' (PMsg hide s p) a = do
  let nm = "PMsg"
  add1 nm
  ll <- eval' p a
  return $ case hide of
             Inline -> addMessagePre s ll
             Nested -> mkNode (getBool ll, [nm <> ":" <> s]) [ll]

eval' (PTree f p) a = do
  let nm = "PTree"
  add1 nm
  f <$> eval' p a

  -- this is "coerce a" in the context of 'b' so we need access to the 'b' in Pred
  -- coerce a has many different values so we need to lock it down to 'b' somehow
  -- Pred b is a proxy b! so we are done!
eval' (PCoerce p) a = do
  let nm = "PCoerce"
  (opts,_) <- add11 nm
  ll <- eval' p (coerce a)
  let b = asProxyTypeOf (coerce a) p
  return $ mkNode (getBool ll, [nm <> showA opts 0 " a=" a <> showA opts 0 " coerced=" b]) [ll]

eval' (PApp a p) ab = do
  opts <- R.ask
  let nm = "PApp"
      b = ab a
  add1 nm
  ll <- eval' p b
  return $ mkNode (getBool ll, [nm <> showA opts 0 " a=" a <> showA opts 1 " b=" b]) [ll]

eval' (PJoin a) pa = do
  opts <- R.ask
  let nm = "PJoin"
  add1 nm
  ll <- eval' pa a -- eval unpeels one layer so now we need 'a' to pa
  return $ mkNode (getBool ll, [nm <> showA opts 0 " a=" a]) [ll]

-- uses lens vocabulary of bigger is 's' and smaller is 'a'
eval' (PView g p) s = do
  opts <- R.ask
  let nm = "PView"
      a = s ^. g
  add1 nm
  ll <- eval' p a
  return $ mkNode (getBool ll, [nm <> showA opts 1 " s=" s <> showA opts 0 " a=" a]) [ll]

eval' (PIf mpexc mpb mpg p) a = do
  opts <- R.ask
  let nm = "PIf"
      n = oHide opts
  add1 nm
  ll <- if n > 0 then R.local (\o -> o { oHide = n-1 }) $ eval' p a
        else eval' p a
  let mrr = case getBool ll of
            FailP {} -> mpexc
            FalseP   -> mpb
            TrueP    -> mpg
      ss = nm <> " <" <> showBoolPSimple (getBool ll) <> " Branch>"
      b1 = getBool ll ^? _BoolP
  case mrr of
       Nothing -> return $ addMessagePre ("<passthrough " <> showBoolPSimple (getBool ll) <> ">") ll
       Just rr' -> do
         rr <- eval' rr' a
         return $
          let b2 = getBool rr ^? _BoolP
              ll' = if b1 == b2 then ll
                    else addMessagePre ("<override with " <> showBoolPSimple (getBool rr) <> ">") ll
          in if n>0 then addMessagePre ss (rr & branches %~ (<>[ll']))
             else mkNode (getBool rr, [ss]) [rr,ll']

eval' (PHead e p) as = do
  let nm = "PHead"
  add1 nm
  opts <- R.ask
  case uncons as of
     Nothing -> addMessagePre (nm <> " empty") <$> eval' e ()
     Just (a, _) -> do
       ll <- eval' p a
       return $ mkNode (getBool ll, [nm <> showA opts 0 " " a]) [ll]

eval' (POne e e2 p) s = do
  let nm = "POne"
  add1 nm
  opts <- R.ask
  case uncons s of
     Nothing -> addMessagePre (nm <> " empty!") <$> eval' e ()
     Just (a, s') | is _Empty s' -> do
       ll <- eval' p a
       return $ mkNode (getBool ll, [nm <> showA opts 0 " " a]) [ll]
                 | otherwise -> do
       ll <- eval' e2 (a,s')
       return $ mkNode (getBool ll, [nm <> " extra values!" <> showA opts 0 " a=" a <> showA opts 0 " s'=" s']) [ll]

eval' (POneT e e2 p) (toList -> as) = do
  let nm = "POneT"
  add1 nm
  opts <- R.ask
  case as of
     [] -> addMessagePre (nm <> " empty!") <$> eval' e ()
     a:s' | null s' -> do
       ll <- eval' p a
       return $ mkNode (getBool ll, [nm <> showA opts 0 " " a]) [ll]
                 | otherwise -> do
       ll <- eval' e2 (a,s')
       return $ mkNode (getBool ll, [nm <> " extra values!" <> showA opts 0 " a=" a <> showA opts 0 " as=" s']) [ll]


eval' (PUnconsT e p) (toList -> as) = do
  let nm = "PUnconsT"
  add1 nm
  opts <- R.ask
  case uncons as of
     Nothing -> addMessagePre (nm <> " empty") <$> eval' e ()
     Just (a, s) -> do
       ll <- eval' p (a, s)
       return $ mkNode (getBool ll, [nm <> showA opts 0 " a=" a <> showA opts 1 " as=" s]) [ll]

eval' (PUncons e p) s' = do
  let nm = "PUncons"
  add1 nm
  opts <- R.ask
  case uncons s' of
     Nothing -> addMessagePre (nm <> " empty") <$> eval' e ()
     Just (a, s) -> do
       ll <- eval' p (a, s)
       return $ mkNode (getBool ll, [nm <> showA opts 0 " a=" a <> showA opts 1 " s=" s]) [ll]

eval' (PLast e p) as = do
  let nm = "PLast"
  add1 nm
  opts <- R.ask
  case unsnoc as of
       Nothing -> addMessagePre (nm <> " empty") <$> eval' e ()
       Just (_, a) -> do
         ll <- eval' p a
         return $ mkNode (getBool ll, [nm <> showA opts 0 " " a]) [ll]

eval' (PUnsnocT e p) (toList -> as) = do
  let nm = "PUnsnocT"
  add1 nm
  opts <- R.ask
  case unsnoc as of
       Nothing -> addMessagePre (nm <> " empty") <$> eval' e ()
       Just (s, a) -> do
         ll <- eval' p (s, a)
         return $ mkNode (getBool ll, [nm <> showA opts 0 " a=" a <> showA opts 1 " as=" s]) [ll]

eval' (PUnsnoc e p) s' = do
  let nm = "PUnsnoc"
  add1 nm
  opts <- R.ask
  case unsnoc s' of
       Nothing -> addMessagePre (nm <> " empty") <$> eval' e ()
       Just (s, a) -> do
         ll <- eval' p (s, a)
         return $ mkNode (getBool ll, [nm <> showA opts 0 " a=" a <> showA opts 1 " s=" s]) [ll]

eval' (PIx i e p) as = do
  let nm = "PIx " <> show i
  add1 nm
  opts <- R.ask
  case as ^? ix i of
       Nothing -> addMessagePre (nm <> " not found") <$> eval' e ()
       Just a -> do
         ll <- eval' p a
         return $ mkNode (getBool ll, [nm <> showA opts 0 " " a]) [ll]

eval' (PISect p) (toList *** toList -> (as,bs)) = do
  let nm = "PISect"
  (opts,_) <- add11 nm
  let (x,y,z) = isect (as,bs)
  ll <- eval' p (x,y,z)
  return $ mkNode (getBool ll, [nm
                             <> showA opts 2 " as=" as
                             <> showA opts 2 " bs=" bs
                             <> showA opts 1 " left=" x
                             <> showA opts 1 " isect=" y
                             <> showA opts 1 " right=" z
                             ]) [ll]

eval' (PISectList p) (fmap toList . toList -> aas) = do
  let nm = "PISectList"
  (opts,_) <- add11 nm
  let (bs,gs) = isectList aas
  ll <- eval' p (bs,gs)
  return $ mkNode (getBool ll, [nm
                             <> showA opts 2 " aas=" aas
                             <> showA opts 1 " unmatched=" bs
                             <> showA opts 1 " matched=" gs
                             ]) [ll]

eval' (PMorph amb p) (toList -> as) = do
  let nm = "PMorph"
  (opts,_) <- add11 nm
  let (bs,gs) = partitionEithers (map (maybeToEither amb) as)
  ll <- eval' p (bs,gs)
  return $ mkNode (getBool ll, [nm <> showA opts 2 " " as <> showA opts 1 " bad=" bs <> showA opts 1 " good=" gs]) [ll]

eval' (PMaybe p q) lr = do
  let nm = "PMaybe"
  add1 nm
  opts <- R.ask
  case lr of
      Nothing -> addMessagePre (nm <> " (Nothing)") <$> eval' p ()
      Just b -> do
                  rr <- eval' q b
                  return $ mkNode (getBool rr, [nm <> " (Just)" <> showA opts 0 " " b]) [rr]

eval' (PEither p q) lr = do
  let nm = "PEither"
  add1 nm
  opts <- R.ask
  case lr of
    Left a -> do
                ll <- eval' p a
                return $ mkNode (getBool ll, [nm <> " (Left)" <> showA opts 0 " " a]) [ll]
    Right b -> do
                rr <- eval' q b
                return $ mkNode (getBool rr, [nm <> " (Right)" <> showA opts 0 " " b]) [rr]

eval' (PThese p q pq) lr = do
  let nm = "PThese"
  add1 nm
  opts <- R.ask
  case lr of
    This a -> do
                ll <- eval' p a
                return $ mkNode (getBool ll, [nm <> " (This)" <> showA opts 0 " a=" a]) [ll]
    That b -> do
               rr <- eval' q b
               return $ mkNode (getBool rr, [nm <> " (That)" <> showA opts 0 " b=" b]) [rr]
    These a b -> do
               ll <- eval' pq (a, b)
               return $ mkNode (getBool ll, [nm <> " (These)" <> showA opts 0 " a=" a <> showA opts 0 " b=" b]) [ll]


-- too many exceptions! we are nesting an exception
-- should we concatenate into one line
eval' (PPrism s f e p) a = do
  let nm = "PPrism"
  add1 nm
  opts <- R.ask
  case f a of
    Nothing -> addMessagePre (nm <> " (Nothing) [" <> s <> "]") <$> eval' e ()
    Just b -> do
              rr <- eval' p b
              return $ mkNode (getBool rr, [nm <> " (Just) [" <> s <> "]" <> showA opts 1 " " b]) [rr]

eval' (PPrismL s f e p) (a, x) = do
  let nm = "PPrismL"
  add1 nm
  opts <- R.ask
  case f a of
    Nothing -> addMessagePre (nm <> " (Nothing) [" <> s <> "]") <$> eval' e x
    Just b -> do
              rr <- eval' p (b, x)
              return $ mkNode (getBool rr, [nm <> " (Just) [" <> s <> "]" <> showA opts 1 " " b]) [rr]

eval' (PPrismR s f e p) (x, a) = do
  let nm = "PPrismR"
  add1 nm
  opts <- R.ask
  case f a of
    Nothing -> addMessagePre (nm <> " (Nothing) [" <> s <> "]") <$> eval' e x
    Just b -> do
              rr <- eval' p (x, b)
              return $ mkNode (getBool rr, [nm <> " (Just) [" <> s <> "]" <> showA opts 1 " " b]) [rr]

eval' (PPrismLE s f p q) (a, x) = do
  let nm = "PPrismLE"
  add1 nm
  opts <- R.ask
  case f a of
    Left b -> do
                rr <- eval' p (b, x)
                return $ mkNode (getBool rr, [nm <> " (Left) [" <> s <> "]" <> showA opts 1 " " b]) [rr]
    Right c -> do
                rr <- eval' q (c, x)
                return $ mkNode (getBool rr, [nm <> " (Right) [" <> s <> "]" <> showA opts 1 " " c]) [rr]

eval' (PPrismRE s f p q) (x, a) = do
  let nm = "PPrismRE"
  add1 nm
  opts <- R.ask
  case f a of
    Left b -> do
                rr <- eval' p (x, b)
                return $ mkNode (getBool rr, [nm <> " (Left) [" <> s <> "]" <> showA opts 1 " " b]) [rr]
    Right c -> do
                rr <- eval' q (x, c)
                return $ mkNode (getBool rr, [nm <> " (Right) [" <> s <> "]" <> showA opts 1 " " c]) [rr]

eval' (PLinear noextravalues qps) (toList -> as) = do
  let nm = "PLinear"
  add1 nm
  linearImpl nm noextravalues qps as

-- if too many 'ts' then show first n and last n and then 1 bad one if not already shown
-- better be real sure that the good one or bad one gets included else we change the result of eval!
-- redundant cos covered by pforall using PPartition but is used a lot and has less extra junk
eval' (PForAll p) (toList -> as) = do
  let nm = "PForAll"
  (opts,_) <- add11 nm
  ts <- zipWithM (\i a -> ((i, a),) <$> eval' p a) [0::Int ..] as
  return $ case splitAndP opts [nm] ts of
       Left e -> e
       Right ([], _) -> mkNode (TrueP, [nm]) (map fixit ts)
       Right (bads@(b:_), _) -> mkNode (FalseP, [nm] <> ["cnt=" <> show (length bads) <> " " <> formatList opts [b]]) (map fixit ts)

-- if too many 'ts' then show first n and last n and then 1 good one if not already shown
-- todo: NOPE if exists has one that is True then if succeeds even if the predicate fails???
eval' (PExists p) (toList -> as) = do
  let nm = "PExists"
  (opts,_) <- add11 nm
  ts <- zipWithM (\i a -> ((i, a),) <$> eval' p a) [0::Int ..] as
  return $ case splitAndP opts [nm] ts of
       Left e -> e
       Right (_, goods@(g:_)) -> mkNode (TrueP, [nm] <> ["cnt=" <> show (length goods) <> " " <> formatList opts [g]]) (map fixit ts)
       Right _ -> mkNode (FalseP, [nm]) (map fixit ts) -- in this case all are bad!

eval' (PZipExact ps e q) (toList -> as) = do
  let nm = "PZipExact"
  (opts,_) <- add11 nm
  let mmsg1 = if length ps /= length as
              then Just (" length ps " <> show (length ps) <> " /= length as " <> show (length as) <> " ")
              else Nothing
  case mmsg1 of
       Just msg1 -> do
               ll <- eval' e (length ps,length as)
               return $ mkNode (getBool ll, [nm,msg1]) [ll]
       Nothing -> do
               ts <- zipWithM (\(i, p) a -> ((i, a),) <$> eval' p a) (zip [0::Int ..] ps) as
               let msgs = nm : maybeToList mmsg1 <> [showA opts 2 "as=" as]
               case splitAndP opts msgs ts of
                    Left ex -> return ex
                    Right (bads,goods) -> do
                      let xs :: [Bool] = ts ^.. traverse . _2 . root . peBoolP . _BoolP
                      ll <- eval' q xs
                      let ll' = ll & branches %~ (<> map fixit ts)
                      return $ mkNode (getBool ll, msgs <> ["(bad,good)=" <> show (length bads, length goods)]) [ll']

eval' (PSeq ps q) (toList -> as) = do
  let nm = "PSeq"
  (opts,_) <- add11 nm
  let mmsg1 = if length ps /= length as
              then Just ("length ps " <> show (length ps) <> " /= length as " <> show (length as) <> " ")
              else Nothing
  ts <- zipWithM (\(i, p) a -> ((i, a),) <$> eval' p a) (zip [0::Int ..] ps) as
  let msgs = nm : maybeToList mmsg1 <> [showA opts 2 "as=" as]
  case splitAndP opts msgs ts of
    Left e -> return e
    Right (bads,goods) -> do
      let xs :: [Bool] = ts ^.. traverse . _2 . root . peBoolP . _BoolP
      ll <- eval' q (xs,drop (length ps) as)
      let ll' = ll & branches %~ (map fixit ts <>)
      return $ mkNode (getBool ll, msgs <> [show (length bads, length goods)]) [ll']


-- probably need to use showA but since is comparison ...
-- todo: need to limit output ala PForAll
-- the key is to leverage splitAndP and returnTS cos they do all the work!
-- Note: if any single element fails the predicate then exit! makes sense: we are saying that the predicate has an exception so stop!
eval' (PPartition p pbg) (toList -> as) = do
  let nm = "PPartition"
  (opts,_) <- add11 nm
  ts <- zipWithM (\i a -> ((i, a),) <$> eval' p a) [0::Int ..] as
  case splitAndP opts [nm] ts of
       Left e -> return e
       -- means there are no errors so we can filter
       -- we already have the index so dont add it again!
       Right z -> do
            ll <- eval' pbg $ join (***) (map (snd.fst)) z
            return $ partitionImpl2 opts nm ts z ll

-- key thing is that break only processes as much as it needs to unlike all the others
-- so if there is a PFail somewhere past the first TrueP then we never see it
-- that first predicate sole purpose is to break the list
eval' (PBreak p p12) (toList -> as) = do
  let nm = "PBreak"
  (opts,_) <- add11 nm
  -- only process as many as you need: so if we get an exception we stop!
  -- if we get a True then we stop
  tss <- zipWithM (\i a -> ((i, a),) <$> eval' p a) [0::Int ..] as
  let (ts,ts') = break (isn't _FalseP . view (_2 . boolP)) tss
  case splitAndP opts [nm] (ts <> take 1 ts') of
       Left e -> return e
       Right (bads, _) -> do
            ll <- eval' p12 (take (length ts) as, drop (length ts) as)
            return $ breakImpl2 opts nm (ts<>take 1 ts') (bads, ts') ll

eval' (PSpan p p12) (toList -> as) = do
  let nm = "PSpan"
  (opts,_) <- add11 nm
  -- only process as many as you need: so if we get an exception we stop!
  -- if we get a True then we stop
  tss <- zipWithM (\i a -> ((i, a),) <$> eval' p a) [0::Int ..] as
  let (ts,ts') = span (isn't _FalseP . view (_2 . boolP)) tss
  case splitAndP opts [nm] (ts <> take 1 ts') of
       Left e -> return e
       Right (bads, _) -> do
            ll <- eval' p12 (take (length ts) as, drop (length ts) as)
            return $ breakImpl2 opts nm (ts<>take 1 ts') (bads, ts') ll

eval' (PJson p q) v = do
  let nm = "PJson"
  (opts,_) <- add11 nm
  let xs = jvisitor p v -- es are any failures [TT] cos of a crap Pred for searching json!
      -- need to handle the zero case so the user has a clue: else just returns True
      -- then also need to make sure 'q' gets called
  ll <- eval' q xs
  let msgs = nm : ["json search failed" | null xs]
  let ns' = flip imap xs $ \i (jp,a) -> mkNodeDebug (TrueP, ["i=" <> show i, showA opts 1 "" (reverse $ toList jp), showA opts 2 "a=" a]) []
  let ns = [ll,mkNodeDebug (TrueP, ["Debugging jpaths"]) ns']
  return $ case getBool ll of
       FailP e -> mkNode (FailP e, msgs) ns
       b -> mkNode (b, msgs) ns

eval' (PJsonKey p q) v = do
  let nm = "PJsonKey"
  (opts,_) <- add11 nm
  let xs = jvisitor (matchKeyP p) v -- es are any failures [TT] cos of a crap Pred for searching json!
      -- need to handle the zero case so the user has a clue: else just returns True
      -- then also need to make sure 'q' gets called
  ll <- eval' q (xs & traverse . _2 %~ snd)
  let msgs = nm : ["json search failed" | null xs]
  let ns' = flip imap xs $ \i (jp,(k,val)) -> mkNodeDebug (TrueP, ["i=" <> show i, "key=" <> k, showA opts 1 "" (reverse $ toList jp), showA opts 2 "value=" val]) []
  let ns = [ll,mkNodeDebug (TrueP, ["Debugging jpaths"]) ns']
  return $ case getBool ll of
       FailP e -> mkNode (FailP e, msgs) ns
       b -> mkNode (b, msgs) ns

eval' (PJsonP jps p q) v = do
  opts <- R.ask
  let nm = "PJsonP" <> showLit opts 1 " path=" (showJPaths jps)
  add1 nm
  let (tt, mv, jps') = jpath [] opts jps v
  ll <- case mv of
             Left e -> addMessagesPre [e, showLit opts 1 "matched up to=" (showJPaths jps')] <$> eval' p ()
             Right v' -> addMessagePre "matched" <$> eval' q v'
      -- need to handle the zero case so the user has a clue: else just returns True
      -- then also need to make sure 'q' gets called
  let msgs = [nm]
  return $ case getBool ll of
       FailP e -> mkNode (FailP e, msgs) [ll,tt]
       b -> mkNode (b, msgs) [ll,tt]

eval' (PState thazz p) a = do
  let nm1 = "PState"
      nm = nm1 <> beforeafter thazz
  (opts,_) <- add11 nm
  let fff azz = do
       oldz <- use cZ
       newz <- cZ <%= azz a
       return (oldz,newz)
  case thazz of
      This azz -> do
        (oldz,newz) <- fff azz
        ll <- eval' p a
        let before = mkNodeDebug (TrueP, [nm1 <> "-" <> showA opts 1 " old state=" oldz <> showA opts 1 " new state=" newz]) []
        return $ mkNode (getBool ll, [nm <> showA opts 0 " a=" a]) [before,ll]
      That azz -> do
        ll <- eval' p a
        (oldz',newz') <- fff azz
        let after = mkNodeDebug (TrueP, [nm1 <> "+" <> showA opts 1 " old state=" oldz' <> showA opts 1 " new state=" newz']) []
        return $ mkNode (getBool ll, [nm <> showA opts 0 " a=" a]) [ll,after]
      These azz azz' -> do
        (oldz,newz) <- fff azz
        let before = mkNodeDebug (TrueP, [nm1 <> "-" <> showA opts 1 " old state=" oldz <> showA opts 1 " new state=" newz]) []
        ll <- eval' p a
        (oldz',newz') <- fff azz'
        let after = mkNodeDebug (TrueP, [nm1 <> "+" <> showA opts 1 " old state=" oldz' <> showA opts 1 " new state=" newz']) []
        return $ mkNode (getBool ll, [nm <> showA opts 0 " a=" a]) [before,ll,after]

eval' (PGet p) a = do
  let nm = "PGet"
  (opts,_) <- add11 nm
  z <- use cZ
  ll <- eval' p (z,a)
  return $ mkNode (getBool ll, [nm <> showA opts 0 " a=" a <> showA opts 1 " state=" z ]) [ll]
{-
eval' (PPut z) a = do
  let nm = "PPut"
  (opts,_) <- add11 nm
  oldz <- cZ <<.= z
  return $ mkNode (TrueP, [nm <> showA opts 0 " a=" a <> showA opts 1 " oldstate=" oldz ]) []
-}
eval' (PLog thazs p) a = do
  let nm = nm1 <> beforeafter thazs
      nm1 = "PLog"
  (opts,_) <- add11 nm
  let fff (lw,azs) = do
       z <- use cZ
       let s = azs (a, z)
       cLog %= (Seq.:|> (lw <> s))
       return $ mkNodeDebug (TrueP, ["PLog" <> lw <> showLit opts 0 " " s <> showA opts 1 " state=" z]) []

      (m1,m2) = case thazs of
                  This f -> (Just ("-",f), Nothing)
                  That f' -> (Nothing, Just ("+",f'))
                  These f f' -> (Just ("-",f), Just ("+",f'))
  ls <- maybeToList <$> traverse fff m1
  ll <- eval' p a
  rs <- maybeToList <$> traverse fff m2
  return $ mkNode (getBool ll, [nm <> showA opts 0 " a=" a]) (ls <> (ll : rs))

linearImpl :: (PES z, Show a) =>
                    String
                    -> Rigid
                    -> [(Pred z Int, Pred z a)]
                    -> [a]
                    -> App (Config z) POpts TT
linearImpl nm noextravalues qps as =  do
    opts <- R.ask
    tss <- zipWithM (\j a -> ((j, a),) <$> zipWithM (\i (_,p) -> ((i, a),) <$> eval' p a) [0::Int ..] qps) [0::Int ..] as
        -- one mega mkNode with subnodes and subnodes beneath if failure
        -- process one 'a' over all the ps and summarise which single p worked -- if not it is a left [need to stash all the values for output]
        -- do repeatedly then pass back over the list and adjust the summary for each one based on previous info if there is an error
        -- map has predicates to values used for the next predicate on [Int]
    let (ret, vvv) = flip S.runState (M.empty :: Map Int [Int]) $
            forM tss $ \((j, a), ts) ->
              (, (a, ts)) <$>
                 let cmap = toCMap' (^. _2 . boolP) ts
                 in case (getC (FailP ("" :| [])) cmap
                         ,getC FalseP cmap
                         ,getC TrueP cmap) of
                     ([], [], []) -> return MissingPredicates
                     ([], _, [g]) -> do
                                     let pind = g ^. _1 . _1
                                     id %= M.insertWith (<>) pind [j]
                                     return (OneMatch j)
                     (_, _, gs@(_:_)) -> do
                                         let ii = gs ^.. traverse . _1 . _1
                                         id %= M.unionWith (<>) (M.fromList (map (, [j]) ii))
                                         return (MoreThanOneMatch ii)
                     (_, _:_, _) -> return (NoMatch j)
                     (es@(_:_), _, _) -> return (ErrorsInPred (es ^.. traverse . _1 . _1)) -- create a single mkNode

        errs = filter (linearityFilter noextravalues) (map fst ret)

        ns = ret <&> \(rc, (a, ts)) ->
               let aa = showA opts 0 " a=" a
               in case splitAndP opts ([nm] <> ["rc=" <> show rc]) ts of
                   Left e -> e
                   Right (_, goods@(g:_)) ->
                     case rc of
                       OneMatch _ -> mkNode (TrueP, [nm] <> [show rc <> aa <> " cnt=" <> show (length goods) <> " " <> formatList opts [g]]) (map fixit ts)
                       _ -> mkNode (FalseP, [nm <> " " <> show rc <> aa]) (map fixit ts)
                   Right _ ->
                     case rc of
                       NoMatch _ | noextravalues == Loose -> mkNode (TrueP, [nm <> " " <> show rc <> aa]) (map fixit ts)
                       _ -> mkNode (FalseP, [nm <> " " <> show rc <> aa]) (map fixit ts)

        -- grafts showPred tree if debug mode
        fn p tt = mkNode (getBool tt, []) [tt, fmap (\n -> BoolPE (getBool tt) False [n]) (showPred opts p)]
        zzz = map (\(q, p) -> if oDebug opts >= 1 then PTree (fn p) q else q) qps
        cnts = map (\j -> maybe 0 length (M.lookup j vvv)) [0 .. length qps -1]

    ll <- addMessagePre "Predicates" <$> eval' (pzipand zzz) cnts

    let msgs = [if null errs then "" else "errors(" <> show (length errs) <> "): " <> intercalate " | " (map show errs)
               ,showA opts 2 "debug=" (map fst ret) <> showA opts 2 " match=" (itoList vvv)
               ]
    return $ case getBool ll of
           FailP e -> mkNode (FailP ("Failed Pred [Int]" N.<| e), nm : msgs) (ll : ns)
           FalseP -> mkNode (FalseP, nm <> " Failed Pred [Int]" : msgs) (ll : ns)
           TrueP -> mkNode (_BoolP # null errs, nm :msgs) (ll : ns)

runPred :: (PES z, Show a) => Pred z a -> a -> Either PE ()
runPred = runPredImpl o2

runPredImpl :: (PES z, Show a) => POpts -> Pred z a -> a -> Either PE ()
runPredImpl (setc0 -> o) p a =
  let (tt,cfg) = eval o p a
      v1 = take 2000 (drawTree (toNodeString o <$> tt))
      v2 = showA o 0 "" a
      v3 = toList (_cLog cfg)
  in case getBool tt of
       TrueP -> Right ()
       FalseP -> Left $ Left $ PredE v1 v2 v3
       FailP e -> Left $ Right $ PredExceptionE e v1 v2 v3

pe, pe1, pe2, pe3, pe', pe1', pe2', pe3', peu, peu1, peu2, peu3, pev, pev1, pev2, pev3, pep, pep1, pep2, pep3 :: (PES z, Show a) => Pred z a -> a -> IO ()
pe = peWith (horizontal o0)
pe1 = peWith (horizontal o1)
pe2 = peWith (horizontal o2)
pe3 = peWith (horizontal o3)

-- for use with doctest as we dont want colors cos will mess up the ouput
pe' = peWith (horizontal $ setc0 o0)
pe1' = peWith (horizontal $ setc0 o1)
pe2' = peWith (horizontal $ setc0 o2)
pe3' = peWith (horizontal $ setc0 o3)

peu = peWith (unicode o0)
peu1 = peWith (unicode o1)
peu2 = peWith (unicode o2)
peu3 = peWith (unicode o3)
pev = peWith (vertical o0)
pev1 = peWith (vertical o1)
pev2 = peWith (vertical o2)
pev3 = peWith (vertical o3)
pep = peWith (pptree o0)
pep1 = peWith (pptree o1)
pep2 = peWith (pptree o2)
pep3 = peWith (pptree o3)

pev' :: (PES z, Show a) => Width -> Pred z a -> a -> IO ()
pev' w = peWith (vertical' w defOpts)

peWith :: (PES z, Show a) => POpts -> Pred z a -> a -> IO ()
peWith o p = prtTTConfig o . eval o p

prtTTConfig :: PES z => POpts -> (TT, Config z) -> IO ()
prtTTConfig o (tt, c) = do
  prtImpl o $ toNodeString o <$> tt
  when (oDebug o > 2) $ print c

type PES z = (Monoid z, Show z)

-- | match on key of object using string predicate
matchKeyP :: PES z => Pred z String -> (NonEmpty JPath, Value) -> Maybe (String, Value)
matchKeyP p (JPKey k :| _, v) =
  case getBool (fst (eval defOpts p k)) of
    TrueP -> Just (k, v)
    _ -> Nothing
matchKeyP _ _ = Nothing

-- using Pred cos makes it easier: just ignoring result unless TrueP
-- we dont trace this stuff cos not needed
-- the value-add is that it returns a String
matchStringP :: PES z => Pred z String -> (NonEmpty JPath, Value) -> Maybe String
matchStringP p (x :| _, _) =
  case x ^? _JPValue . _String . to T.unpack of
    Just s -> do
                let (ll,_) = eval defOpts p s
                case getBool ll of
                  TrueP -> Just s
                  _ -> Nothing
    Nothing -> Nothing

-- | match on any json 'String'
--
--   >>> pe1' (pjsonString 1 (psnds $ PLinear Rigid $ map (preq . peq) ["Vladimir"])) json2
--   <BLANKLINE>
--   FalseP PJson
--   |
--   +- FalseP PLinear | errors(7): NoMatch 0 | NoMatch 1 | NoMatch 2 | NoMatch 3 | NoMatch 4 | NoMatch 5 | NoMatch 6
--   |  |
--   |  +- TrueP  Predicates | PZipAnd | PZipExact | (bad,good)=(0,1)
--   |  |  |
--   |  |  `- TrueP  PLift and | a=[True]
--   |  |     |
--   |  |     `- TrueP  i=0
--   |  |        |
--   |  |        +- TrueP  1 == 1
--   |  |        |
--   |  |        `- a == "Vladimir"
--   |  |
--   |  +- FalseP PLinear NoMatch 0 a="Diaz"
--   |  |  |
--   |  |  `- FalseP i=0: "Diaz" == "Vladimir"
--   |  |
--   |  +- FalseP PLinear NoMatch 1 a="Daniel"
--   |  |  |
--   |  |  `- FalseP i=0: "Daniel" == "Vladimir"
--   |  |
--   |  +- FalseP PLinear NoMatch 2 a="Red"
--   |  |  |
--   |  |  `- FalseP i=0: "Red" == "Vladimir"
--   |  |
--   |  +- FalseP PLinear NoMatch 3 a="Rose"
--   |  |  |
--   |  |  `- FalseP i=0: "Rose" == "Vladimir"
--   |  |
--   |  +- FalseP PLinear NoMatch 4 a="Doe"
--   |  |  |
--   |  |  `- FalseP i=0: "Doe" == "Vladimir"
--   |  |
--   |  +- FalseP PLinear NoMatch 5 a="John"
--   |  |  |
--   |  |  `- FalseP i=0: "John" == "Vladimir"
--   |  |
--   |  +- FalseP PLinear NoMatch 6 a="Vygodsky"
--   |  |  |
--   |  |  `- FalseP i=0: "Vygodsky" == "Vladimir"
--   |  |
--   |  `- TrueP  PLinear | OneMatch 7 a="Vladimir" cnt=1 (i=0, a="Vladimir")
--   |     |
--   |     `- TrueP  i=0: "Vladimir" == "Vladimir"
--   |
--   `- Debugging jpaths
--      |
--      +- i=0 | [JPIndex 0,JPKey "lastName",JPValue (String "Diaz")]
--      |
--      +- i=1 | [JPIndex 0,JPKey "firstName",JPValue (String "Daniel")]
--      |
--      +- i=2 | [JPIndex 1,JPKey "lastName",JPValue (String "Red")]
--      |
--      +- i=3 | [JPIndex 1,JPKey "firstName",JPValue (String "Rose")]
--      |
--      +- i=4 | [JPIndex 2,JPKey "lastName",JPValue (String "Doe")]
--      |
--      +- i=5 | [JPIndex 2,JPKey "firstName",JPValue (String "John")]
--      |
--      +- i=6 | [JPIndex 3,JPKey "lastName",JPValue (String "Vygodsky")]
--      |
--      `- i=7 | [JPIndex 3,JPKey "firstName",JPValue (String "Vladimir")]
--   <BLANKLINE>
--
--   >>> pe2' (pjsonString (sinfix "iso") $ psnds $ PShow 1) json1
--   <BLANKLINE>
--   TrueP  PJson
--   |
--   +- TrueP  PShow
--   |  |
--   |  +- TrueP  PConst a=["ISO 8879:1986"]
--   |  |
--   |  `- ===== PShow =====
--   |     |
--   |     `- i=0 a="ISO 8879:1986"
--   |
--   `- Debugging jpaths
--      |
--      `- i=0 | [JPKey "glossary",JPKey "GlossDiv",JPKey "GlossList",JPKey "GlossEntry",JPKey "Abbrev",JPValue (String "ISO 8879:1986")] | a="ISO 8879:1986"
--   <BLANKLINE>
--
pjsonString :: PES z => Pred z String -> Pred z [(NonEmpty JPath, String)] -> Pred z Value
pjsonString = PJson . matchStringP

-- | 'PJsonKey' but expects exactly one match
--
--   >>> pe' (pjsonKeyOne "abbrev" 1) json1
--   <BLANKLINE>
--   TrueP  PJsonKey
--   |
--   +- TrueP  POne String "ISO 8879:1986"
--   |  |
--   |  `- TrueP
--   |
--   `- Debugging jpaths
--      |
--      `- i=0 | key=Abbrev
--   <BLANKLINE>
--
--   >>> pe' (pjsonKeyOne "abbrev" 1) json0
--   <BLANKLINE>
--   FalseP PJsonKey | json search failed
--   |
--   +- FalseP POne empty!
--   |
--   `- Debugging jpaths
--   <BLANKLINE>
--
--   >>> pe' (pjsonKeyOne "title" 1) json1
--   <BLANKLINE>
--   FalseP PJsonKey
--   |
--   +- FalseP POne extra values! a=String "S" s'=[String "example glossary"]
--   |  |
--   |  `- FalseP
--   |
--   `- Debugging jpaths
--      |
--      +- i=0 | key=title
--      |
--      `- i=1 | key=title
--   <BLANKLINE>
--
--   >>> pe1' (pjsonKeyOne (sinfix "seeal") $ jarray 0 $ PLinear Rigid [preq "xml",preq "gml"]) json1
--   <BLANKLINE>
--   TrueP  PJsonKey
--   |
--   +- TrueP  POne Array [String "GML",String "XML"]
--   |  |
--   |  `- TrueP  PPrism (Just) [jarray] [String "GML",String "XML"]
--   |     |
--   |     `- TrueP  PLinear
--   |        |
--   |        +- TrueP  Predicates | PZipAnd | PZipExact | (bad,good)=(0,2)
--   |        |  |
--   |        |  `- TrueP  PLift and | a=[True,True]
--   |        |     |
--   |        |     +- TrueP  i=0
--   |        |     |  |
--   |        |     |  +- TrueP  1 == 1
--   |        |     |  |
--   |        |     |  `- PStringCI a == String "xml"
--   |        |     |
--   |        |     `- TrueP  i=1
--   |        |        |
--   |        |        +- TrueP  1 == 1
--   |        |        |
--   |        |        `- PStringCI a == String "gml"
--   |        |
--   |        +- TrueP  PLinear | OneMatch 0 a=String "GML" cnt=1 (i=1, a=String "GML")
--   |        |  |
--   |        |  +- FalseP i=0: PStringCI String "GML" == String "xml"
--   |        |  |
--   |        |  `- TrueP  i=1: PStringCI String "GML" == String "gml"
--   |        |
--   |        `- TrueP  PLinear | OneMatch 1 a=String "XML" cnt=1 (i=0, a=String "XML")
--   |           |
--   |           +- TrueP  i=0: PStringCI String "XML" == String "xml"
--   |           |
--   |           `- FalseP i=1: PStringCI String "XML" == String "gml"
--   |
--   `- Debugging jpaths
--      |
--      `- i=0 | key=GlossSeeAlso | [JPKey "glossary",JPKey "GlossDiv",JPKey "GlossList",JPKey "GlossEntry",JPKey "GlossDef",JPKey "GlossSeeAlso"]
--   <BLANKLINE>
--
--   >>> pe' (pjsonKeyOne "abbrev" $ sinfix "iso") json1
--   <BLANKLINE>
--   TrueP  PJsonKey
--   |
--   +- TrueP  POne String "ISO 8879:1986"
--   |  |
--   |  `- TrueP  PStringCI String "iso" `isInfixOf` String "ISO 8879:1986"
--   |
--   `- Debugging jpaths
--      |
--      `- i=0 | key=Abbrev
--   <BLANKLINE>
--
pjsonKeyOne :: Pred z String -> Pred z Value -> Pred z Value
pjsonKeyOne q = PJsonKey q . psnds . pone

pjsonKeyOne' :: Pred z String -> Pred z (NonEmpty JPath, Value) -> Pred z Value
pjsonKeyOne' q = PJsonKey q . pone

jkeyPrint :: PES z => AsValue s => Pred z String -> s -> IO [Value]
jkeyPrint pk js = jkeyPrint' $ jvisitor (matchKeyP pk) (js ^?! _Value)


