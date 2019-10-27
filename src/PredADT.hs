-- conquer requires a non showable version to work
{-# OPTIONS -Wall #-}
{-# OPTIONS -Wno-unused-imports #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
module PredADT where
import Data.Foldable
import Control.Lens
import Control.Lens.Extras
import Control.Arrow
import Data.List hiding (uncons)
import Data.Function
import Data.Tree
import Data.Tree.Lens
import Data.Time.Lens
import Data.Time
import Data.List.NonEmpty (NonEmpty(..))
import qualified Data.List.NonEmpty as N
import Data.Char
import Data.Maybe
import qualified Data.Map.Strict as M
import Data.Map.Strict (Map)
import qualified Control.Monad.State.Strict as S
import Control.Monad
import qualified Data.Text as T
import Data.Text (Text)
import Data.Vector (Vector)
import Data.HashMap.Strict (HashMap)
import qualified Data.HashMap.Strict as H
import Data.Scientific
import Data.Aeson
import Data.Aeson.Lens
import PredHelper
import Data.Functor.Contravariant.Divisible
import Data.Proxy
import Data.Coerce
import Data.String
import Data.Void
import Data.Hashable
import Data.Either
import Data.These
import Data.These.Combinators
import RegexHelper
import VinylHelper
import JsonHelper
import Data.Vinyl
import Data.Vinyl.TypeLevel
import qualified Data.Vinyl.Functor as W
import qualified GHC.TypeLits as G
import Text.Regex.Applicative

import PredJson -- needed for doctest

data Pred a = Pred {
    _ppred :: Tree String
  , _pfn :: POpts -> a -> TT
  }

instance (IsString a, SConv a) => IsString (Pred a) where
  fromString = _PString CI SNone . fromString

-- PFn does this better cos wraps it instead of being hidden
instance Contravariant Pred where
  contramap f (Pred px p) = Pred px (\z a -> p z (f a))

-- associativity problems -- these are monoidal so has to violate laws
-- cos of extra wrappers on px and qq
instance Divisible Pred where
  conquer = _PConst' (BoolPE TrueP True []) -- need a non showable version
  -- acts as 'and' so conquer must be True to be the identity
  divide abc (Pred px p) (Pred qq q) =
    Pred (Node "divide" [px,qq])
    $ \opts a ->
             let (ll,rr) = (p opts *** q opts) (abc a)
                 nm = "divide"
             in [ll,rr] & case (getBool ll, getBool rr) of
                 (l@FailP {}, r@FailP {}) -> mkNode (l <> r, [nm <> " (b)"])
                 (l@FailP {}, _) -> mkNode (l, [nm <> " (l)"])
                 (_, r@FailP {}) -> mkNode (r, [nm <> " (r)"])
                 (b, b1) -> mkNode (liftBool2 (&&) b b1, [nm])

-- todo no way this will work: what should lose be?
instance Decidable Pred where
--  lose = _PConst' (BoolPE FalseP True [])  -- or fail! like absurd
--  lose _ = _PConst' (BoolPE (FailP ("" :| [])) True [])  -- or fail! like absurd
  lose f = Pred (pure mempty) (\_  a -> absurd (f a))
  choose alr (Pred px p) (Pred qq q) =
    Pred (Node "choose" [px,qq]) $ \opts a -> case alr a of
                                                Left b -> p opts b
                                                Right c -> q opts c

runp :: POpts -> Pred a -> a -> IO ()
runp o (Pred _ px) a = putStrLn $ drawTree (toNodeString o <$> px o a)

showPred :: Pred a -> Tree String
showPred (Pred x _) = x

instance Show (Pred a) where
--  show (Pred x _) = "Pred\n"  <> drawTree x
  show (Pred x _) = "Pred\n"  <> showImpl defOpts x
--     v1 = take 2000 (drawTree (toNodeString <$> t))

pp, ppu :: Pred a -> IO ()
pp = ppWith (horizontal defOpts)
ppu = ppWith (unicode defOpts)

ppWith :: POpts -> Pred a -> IO ()
ppWith o (Pred x _) = prtImpl o x

infixr 3 `_PAnd`
infixr 2 `_POr`
infixr 2 `_PXor`
infixr 2 `_PEquiv`
infixr 2 `_PImpl`

-- | indexing
--
-- >>> pe' (5 .! peq 'f') ['a'..'z']
-- <BLANKLINE>
-- TrueP  PIx 5 'f'
-- |
-- `- TrueP  'f' == 'f'
-- <BLANKLINE>
--
-- >>> pe' (5 .! peq 'f' + 1) ['a'..'z']
-- <BLANKLINE>
-- TrueP  POr
-- |
-- +- TrueP  PIx 5 'f'
-- |  |
-- |  `- TrueP  'f' == 'f'
-- |
-- `- TrueP
-- <BLANKLINE>
--
-- >>> pe' (5 .! peq 'f' * 1) ['a'..'z']
-- <BLANKLINE>
-- TrueP  PAnd
-- |
-- +- TrueP  PIx 5 'f'
-- |  |
-- |  `- TrueP  'f' == 'f'
-- |
-- `- TrueP
-- <BLANKLINE>
--
-- >>> pe' (5 .! peq 'f' `_PBoth` 1) (['a'..'z'],())
-- <BLANKLINE>
-- TrueP  PBoth
-- |
-- +- TrueP  PIx 5 'f'
-- |  |
-- |  `- TrueP  'f' == 'f'
-- |
-- `- TrueP
-- <BLANKLINE>
--
-- >>> pe' (5 .! peq 'f' `_PBoth` _PLen (pgt 4)) (['a'..'z'],"af")
-- <BLANKLINE>
-- FalseP PBoth
-- |
-- +- TrueP  PIx 5 'f'
-- |  |
-- |  `- TrueP  'f' == 'f'
-- |
-- `- FalseP PLen 2
--    |
--    `- FalseP 2 > 4
-- <BLANKLINE>
--
(.!) = pix
(.!), pix :: (Show (IxValue s), Show (Index s),
              Ixed s) =>
             Index s -> Pred (IxValue s) -> Pred s
pix i = _PIx i 0

instance Show a => Num (Pred a) where
  (+) = _POr
  (*) = _PAnd
  negate = _PNot
  p - q = _POr p (_PNot q)
  fromInteger n | n == 0 = pfalse
                | n == 1 = ptrue
                | n == 2 = pfail ""
                | otherwise = pfail ("fromInteger: n=" ++ show n ++ ": use 0 or 1")
  abs = id
  signum = id

-- | leaf constructor that sets the final state. see 'BoolPE'
--
-- >>> pe2' (ptrue' "true predicate") ()
-- <BLANKLINE>
-- TrueP  PConst a=() | true predicate
-- <BLANKLINE>
--
-- >>> pe2' (pfalse' "false predicate") ()
-- <BLANKLINE>
-- FalseP PConst a=() | false predicate
-- <BLANKLINE>
--
-- >>> pe2' (pfail "failed predicate") ()
-- <BLANKLINE>
-- [Error failed predicate] PConst a=()
-- <BLANKLINE>
--
_PConst :: Show a => BoolPE -> Pred a
_PConst b =
  Pred (Node (nm <> " " <> toNodeString (setc0 o0) b) [])
  (\opts a -> Node (b & peStrings %~ ([showLit opts 1 "" nm <> showA opts 1 " a=" a] <>)) [])
 where nm = "PConst"

-- | used by 'Divisible' as we cannot use the Showable version of '_PConst'
_PConst' :: BoolPE -> Pred a
_PConst' b =
  Pred (Node (nm <> " " <> toNodeString (setc0 o0) b) [])
  (\opts _ -> Node (b & peStrings %~ ([showLit opts 1 "" nm] <>)) [])
 where nm = "PConst'"

-- | lifts a predicate function
--
-- >>> pe1' (_PLift "or" or) [True,False,True]
-- <BLANKLINE>
-- TrueP  PLift or | a=[True,False,True]
-- <BLANKLINE>
--
_PLift :: Show a => String -> (a -> Bool) -> Pred a
_PLift s ab = Pred (Node nm [])
  (\opts a -> mkNode (_BoolP # ab a, [nm, showA opts 1 "a=" a]) [])
 where nm = "PLift" `stringAp` s

_PFn :: (Show b, Show a) => String -> (a -> b) -> Pred b -> Pred a
_PFn s ab (Pred x p) =
  Pred (Node nm [x]) $ \opts a ->
      let b = ab a
          n = oHide opts
       in if n > 0 then p opts { oHide = n-1 } b
       else let ll = p opts b
            in mkNode (getBool ll, [nm `stringAp` s, showA opts 0 "a=" a, showA opts 0 "b=" b]) [ll]
  where nm = "PFn"

-- | lifts a string to a 'Pred' using 'StringOperator' and case sensitivity
--
-- >>> pe' (sinfix "abc") "xxxAbCyyy"
-- <BLANKLINE>
-- TrueP  PStringCI "abc" `isInfixOf` "xxxAbCyyy"
-- <BLANKLINE>
--
_PString :: SConv s => Case -> StringOperator -> s -> Pred s
_PString ci sop s =
  Pred (Node (nm <> " " <> showStringOperator sop "a" (sdisp s)) []) $
  \opts t ->
    let b = scompare ci sop s t
    in mkNode (_BoolP # b, [nm <> " " <> showStringOperator sop (showLit opts 0 "" (sdisp t)) (showLit opts 0 "" (sdisp s))]) []
  where nm = "PString" <> show ci

-- | finds the levenshtein distance between the two strings
--
-- runs the predicate Pred Int using that calculated distance
--
-- >>> pe1' (_PDist CS "abc" $ plt 2) "abCd"
-- <BLANKLINE>
-- FalseP PDistCS | dist=2 | s=abc | t=abCd
-- |
-- `- FalseP 2 < 2
-- <BLANKLINE>
--
-- >>> pe1' (_PDist CS "abc" 1) "abc"
-- <BLANKLINE>
-- TrueP  PDistCS | dist=0 | s=abc | t=abc
-- |
-- `- TrueP  PConst a=0
-- <BLANKLINE>
--
-- >>> pe1' (_PDist CS "abc" 1) "Abc"
-- <BLANKLINE>
-- TrueP  PDistCS | dist=1 | s=abc | t=Abc
-- |
-- `- TrueP  PConst a=1
-- <BLANKLINE>
--
-- >>> pe1' (_PDist CS "abc" 1) "Abcxyz"
-- <BLANKLINE>
-- TrueP  PDistCS | dist=4 | s=abc | t=Abcxyz
-- |
-- `- TrueP  PConst a=4
-- <BLANKLINE>
--
-- >>> pe1' (_PDist CI "abc" 1) "Abcxyz"
-- <BLANKLINE>
-- TrueP  PDistCI | dist=3 | s=abc | t=Abcxyz
-- |
-- `- TrueP  PConst a=3
-- <BLANKLINE>
--
_PDist :: (SConv a1, SConv a2) => Case -> a1 -> Pred Int -> Pred a2
_PDist ci s (Pred x p) =
  Pred (Node (nm <> " " <> sdisp s) [x]) $
  \opts t ->
    let d = dist ci (sstring s) (sstring t)
        ll = p opts d
    in mkNode (getBool ll, [nm, "dist=" <> show d, showLit opts 1 "s=" (sstring s), showLit opts 1 "t=" (sstring t)]) [ll]
  where nm = "PDist" <> show ci

-- | compare the value using the 'CmpOperator'
--
-- >>> pe2' (_PCmp Gt 4 * _PCmp Lt 10) 12
-- <BLANKLINE>
-- FalseP PAnd
-- |
-- +- TrueP  12 > 4
-- |
-- `- FalseP 12 < 10
-- <BLANKLINE>
--
_PCmp :: (Ord a, Show a) => CmpOperator -> a -> Pred a
_PCmp c a' = Pred (Node ("a " <> show c <> " " <> show a') [])
    $ \opts a -> let b = snd (ccmp c) a a'
                 in mkNode (_BoolP # b, [showA opts 0 "" a <> " " <> show c <> showA opts 0 " " a']) []

-- | compare the value using 'Eq' instance only so doesnt require 'Ord' instance
--
-- >>> pe' (_PEq False 'x') 'y'
-- <BLANKLINE>
-- TrueP  'y' /= 'x'
-- <BLANKLINE>
--
-- >>> pe' (_PEq True 'x') 'y'
-- <BLANKLINE>
-- FalseP 'y' == 'x'
-- <BLANKLINE>
--
-- >>> pe' (_PEq True 'x') 'x'
-- <BLANKLINE>
-- TrueP  'x' == 'x'
-- <BLANKLINE>
--
_PEq :: (Eq a, Show a) => Bool -> a -> Pred a
_PEq isequal a' = Pred (Node ("a " <> equalShow isequal <> " " <> show a') [])
  $ \opts a -> let b = isequal == (a == a')
               in mkNode (_BoolP # b, [showA opts 0 "" a <> " " <> equalShow isequal <> showA opts 0 " " a']) []

-- | compare the values in a tuple using the 'CmpOperator'
--
-- >>> pe2' plt2 (14,13)
-- <BLANKLINE>
-- FalseP PCmp2 14 < 13
-- <BLANKLINE>
--
-- >>> pe1' (_PCmp2 Gt * _PEq2 True + _PFst (pgt 10) + _PBoth 1 0) (12,11)
-- <BLANKLINE>
-- TrueP  POr
-- |
-- +- TrueP  POr
-- |  |
-- |  +- FalseP PAnd
-- |  |  |
-- |  |  +- TrueP  PCmp2 12 > 11
-- |  |  |
-- |  |  `- FalseP PEq2 12 == 11
-- |  |
-- |  `- TrueP  PFst a=12 snd=11
-- |     |
-- |     `- TrueP  12 > 10
-- |
-- `- FalseP PBoth
--    |
--    +- TrueP  PConst a=12
--    |
--    `- FalseP PConst a=11
-- <BLANKLINE>
--
-- >>> pe' (_PCmp2 Lt) (14,4)
-- <BLANKLINE>
-- FalseP PCmp2 14 < 4
-- <BLANKLINE>
--
-- >>> pe' (_PCmp2 Gt) (14,4)
-- <BLANKLINE>
-- TrueP  PCmp2 14 > 4
-- <BLANKLINE>
--
_PCmp2 :: (Ord a, Show a) => CmpOperator -> Pred (a, a)
_PCmp2 c  =
  Pred (Node nm []) $
    \opts (a,a') ->
    let b = snd (ccmp c) a a'
    in mkNode (_BoolP # b, ["PCmp2 " <> showA opts 0 "" a <> " " <> show c <> showA opts 0 " " a']) []
  where nm = "PCmp2"

-- | compare the values in a tuple using (==) (/=) using only Eq constraint
--
-- >>> pe' (_PEq2 True) (14,4)
-- <BLANKLINE>
-- FalseP PEq2 14 == 4
-- <BLANKLINE>
--
-- >>> pe' (_PEq2 False) (14,4)
-- <BLANKLINE>
-- TrueP  PEq2 14 /= 4
-- <BLANKLINE>
--
_PEq2 :: (Eq a, Show a) => Bool -> Pred (a, a)
_PEq2 isequal =
  Pred (Node nm []) $
    \opts (a,a') ->
    let b = isequal == (a == a')
    in mkNode (_BoolP # b, ["PEq2 " <> showA opts 0 "" a <> " " <> equalShow isequal <> showA opts 0 " " a']) []
  where nm = "PEq2"

_PMatch :: (Foldable t, Eq a, Show a) => StringOperator -> [a] -> Pred (t a)
_PMatch sop as' =
  Pred (Node nm []) $
    \opts (toList -> as) ->
    let fn = case sop of
              SNone -> (==)
              SPrefix -> isPrefixOf
              SInfix -> isInfixOf
              SSuffix -> isSuffixOf
        b = as' `fn` as
    in mkNode (_BoolP # b, ["PMatch " <> showStringOperator sop (showA opts 0 "" as) (showA opts 0 "" as')]) []
  where nm = "PMatch"

_PRegexs :: (Foldable t, Show b, Show a, Eq a) => [(RType, RE a b)] -> Pred ((Int, Int), ([b], [a])) -> Pred (t a)
_PRegexs regexs (Pred x p) =
  Pred (Node nm [x]) $
    \opts (toList -> as) ->
      let rs = runRegexs (N.fromList regexs) as
          leftovers = rs ^? _last . _3 ^. non as
          (lrmsgs, tt) = regexsToTT opts (join These (length regexs)) leftovers rs
          ll = p opts ((length regexs, length rs), (unzip3 rs ^. _1, leftovers))
      in mkNode (getBool ll, [nm] <> either id id lrmsgs <> [showA opts 2 "as=" as]) [ll,tt]
      where nm = "PRegexs (" <> show (length regexs) <> ")"

-- | matches sequentially each regex until completed or fails (using Vinyl)
--
-- >>> import Text.Regex.Applicative.Common (digit)
-- >>> pe1' (_PRegexV (double :& sym 'x' :& string "abc" :& digit :& RNil) 0 $ _PFst $ pri @0 (pgt 33)) "234.56xabc7zzzz"
-- <BLANKLINE>
-- TrueP  PRegexV (4) | matched all | leftovers=zzzz
-- |
-- +- TrueP  PFst a={234.56, 'x', "abc", 7} snd="zzzz"
-- |  |
-- |  `- TrueP  PFn @0 | a={234.56, 'x', "abc", 7} | b=234.56
-- |     |
-- |     `- TrueP  234.56 > 33.0
-- |
-- `- matched all | leftovers=zzzz
--    |
--    +- i=0 | a=234.56 | used=234.56 | remaining=xabc7zzzz
--    |
--    +- i=1 | a='x' | used=x | remaining=abc7zzzz
--    |
--    +- i=2 | a="abc" | used=abc | remaining=7zzzz
--    |
--    `- i=3 | a=7 | used=7 | remaining=zzzz
-- <BLANKLINE>
--
-- >>> import Text.Regex.Applicative.Common (digit)
-- >>> pe1' (_PRegexV (double :& sym 'x' :& string "abc" :& digit :& RNil) 0 $ _PFst $ pri @0 (pgt 33)) "234.56xabczzzz"
-- <BLANKLINE>
-- FalseP PRegexV (4) | only matched 3 of 4 | leftovers=zzzz
-- |
-- +- FalseP PConst a="zzzz"
-- |
-- `- only matched 3 of 4 | leftovers=zzzz
--    |
--    +- i=0 | a=234.56 | used=234.56 | remaining=xabczzzz
--    |
--    +- i=1 | a='x' | used=x | remaining=abczzzz
--    |
--    `- i=2 | a="abc" | used=abc | remaining=zzzz
-- <BLANKLINE>
--
-- >>> import Text.Regex.Applicative.Common (digit)
-- >>> pe1' (_PRegexV (double :& sym 'x' :& string "abc" :& digit :& RNil) 0 $ _PFst $ prx (pgt 33)) "234.56xabc7zzzz"
-- <BLANKLINE>
-- FalseP PRegexV (4) | matched all | leftovers=zzzz
-- |
-- +- FalseP PFst a={234.56, 'x', "abc", 7} snd="zzzz"
-- |  |
-- |  `- FalseP PFn prx | a={234.56, 'x', "abc", 7} | b=7
-- |     |
-- |     `- FalseP 7 > 33
-- |
-- `- matched all | leftovers=zzzz
--    |
--    +- i=0 | a=234.56 | used=234.56 | remaining=xabc7zzzz
--    |
--    +- i=1 | a='x' | used=x | remaining=abc7zzzz
--    |
--    +- i=2 | a="abc" | used=abc | remaining=7zzzz
--    |
--    `- i=3 | a=7 | used=7 | remaining=zzzz
-- <BLANKLINE>
--
-- >>> import Text.Regex.Applicative.Common (digit)
-- >>> pe1' (_PRegexV (double :& sym 'x' :& string "abc" :& digit :& RNil) 0 $ _PFst $ prx (peq 'y')) "234.56xabc7zzzz"
-- <BLANKLINE>
-- FalseP PRegexV (4) | matched all | leftovers=zzzz
-- |
-- +- FalseP PFst a={234.56, 'x', "abc", 7} snd="zzzz"
-- |  |
-- |  `- FalseP PFn prx | a={234.56, 'x', "abc", 7} | b='x'
-- |     |
-- |     `- FalseP 'x' == 'y'
-- |
-- `- matched all | leftovers=zzzz
--    |
--    +- i=0 | a=234.56 | used=234.56 | remaining=xabc7zzzz
--    |
--    +- i=1 | a='x' | used=x | remaining=abc7zzzz
--    |
--    +- i=2 | a="abc" | used=abc | remaining=7zzzz
--    |
--    `- i=3 | a=7 | used=7 | remaining=zzzz
-- <BLANKLINE>
--
-- >>> pe1' (_PRegexV (ratio :& void spaces1 :& int :& void spaces1 :& word :& RNil) 0 $ _PFst $ prx "HELlo" * prx (pgt (9999::Int))) "12367   99  hellx world"
-- <BLANKLINE>
-- FalseP PRegexV (5) | matched all | leftovers= world
-- |
-- +- FalseP PFst a={12367 % 1, (), 99, (), "hellx"} snd=" world"
-- |  |
-- |  `- FalseP PAnd
-- |     |
-- |     +- FalseP PFn prx | a={12367 % 1, (), 99, (), "hellx"} | b="hellx"
-- |     |  |
-- |     |  `- FalseP PStringCI "hellx" == "HELlo"
-- |     |
-- |     `- FalseP PFn prx | a={12367 % 1, (), 99, (), "hellx"} | b=99
-- |        |
-- |        `- FalseP 99 > 9999
-- |
-- `- matched all | leftovers= world
--    |
--    +- i=0 | a=12367 % 1 | used=12367 | remaining=   99  hellx world
--    |
--    +- i=1 | a=() | used=    | remaining=99  hellx world
--    |
--    +- i=2 | a=99 | used=99 | remaining=  hellx world
--    |
--    +- i=3 | a=() | used=   | remaining=hellx world
--    |
--    `- i=4 | a="hellx" | used=hellx | remaining= world
-- <BLANKLINE>
--
-- >>> pe1' (_PRegexV (ratio :& void spaces1 :& int :& void spaces1 :& word :& RNil) 0 $ _PFst $ prx "HELlo" * pri @2 (pgt 9999)) "12367   99  hellx world"
-- <BLANKLINE>
-- FalseP PRegexV (5) | matched all | leftovers= world
-- |
-- +- FalseP PFst a={12367 % 1, (), 99, (), "hellx"} snd=" world"
-- |  |
-- |  `- FalseP PAnd
-- |     |
-- |     +- FalseP PFn prx | a={12367 % 1, (), 99, (), "hellx"} | b="hellx"
-- |     |  |
-- |     |  `- FalseP PStringCI "hellx" == "HELlo"
-- |     |
-- |     `- FalseP PFn @2 | a={12367 % 1, (), 99, (), "hellx"} | b=99
-- |        |
-- |        `- FalseP 99 > 9999
-- |
-- `- matched all | leftovers= world
--    |
--    +- i=0 | a=12367 % 1 | used=12367 | remaining=   99  hellx world
--    |
--    +- i=1 | a=() | used=    | remaining=99  hellx world
--    |
--    +- i=2 | a=99 | used=99 | remaining=  hellx world
--    |
--    +- i=3 | a=() | used=   | remaining=hellx world
--    |
--    `- i=4 | a="hellx" | used=hellx | remaining= world
-- <BLANKLINE>
--
-- >>> import Text.Regex.Applicative.Common (digit)
-- >>> pe1' (_PRegexV (_d :& ratio :& _w :& ipaddr :& _w :& digit :& RNil) 0 $ _PFst $ prx $ (plt 102)) "927.34a27.11.4.33c9junk"
-- <BLANKLINE>
-- TrueP  PRegexV (6) | matched all | leftovers=junk
-- |
-- +- TrueP  PFst a={'9', 1367 % 50, 'a', IP:27.11.4.33, 'c', 9} snd="junk"
-- |  |
-- |  `- TrueP  PFn prx | a={'9', 1367 % 50, 'a', IP:27.11.4.33, 'c', 9} | b=9
-- |     |
-- |     `- TrueP  9 < 102
-- |
-- `- matched all | leftovers=junk
--    |
--    +- i=0 | a='9' | used=9 | remaining=27.34a27.11.4.33c9junk
--    |
--    +- i=1 | a=1367 % 50 | used=27.34 | remaining=a27.11.4.33c9junk
--    |
--    +- i=2 | a='a' | used=a | remaining=27.11.4.33c9junk
--    |
--    +- i=3 | a=IP:27.11.4.33 | used=27.11.4.33 | remaining=c9junk
--    |
--    +- i=4 | a='c' | used=c | remaining=9junk
--    |
--    `- i=5 | a=9 | used=9 | remaining=junk
-- <BLANKLINE>
--
-- >>> pe2' (_PRegexV (_d :& word :& gregorian :& "abc" :& RNil) 0 $ _PFst $ prx @Day (_PView days (pgt 12) * _PView years (plt 2000))) "9hello2018-12-22abcXYZ"
-- <BLANKLINE>
-- FalseP PRegexV (4) | matched all | leftovers=XYZ
-- |
-- +- FalseP PFst a={'9', "hello", 2018-12-22, "abc"} snd="XYZ"
-- |  |
-- |  `- FalseP PFn prx | a={'9', "hello", 2018-12-22, "abc"} | b=2018-12-22
-- |     |
-- |     `- FalseP PAnd
-- |        |
-- |        +- TrueP  PView s=2018-12-22 a=22
-- |        |  |
-- |        |  `- TrueP  22 > 12
-- |        |
-- |        `- FalseP PView s=2018-12-22 a=2018
-- |           |
-- |           `- FalseP 2018 < 2000
-- |
-- `- matched all | leftovers=XYZ
--    |
--    +- i=0 | a='9' | used=9 | remaining=hello2018-12-22abcXYZ
--    |
--    +- i=1 | a="hello" | used=hello | remaining=2018-12-22abcXYZ
--    |
--    +- i=2 | a=2018-12-22 | used=2018-12-22 | remaining=abcXYZ
--    |
--    `- i=3 | a="abc" | used=abc | remaining=XYZ
-- <BLANKLINE>
--
-- >>> pe2' (_PRegexV ("abc" :& ratio :& _w :& hex :& RNil) 0 1) "abc123.456Za805f__"
-- <BLANKLINE>
-- TrueP  PRegexV (4) | matched all | leftovers=__
-- |
-- +- TrueP  PConst a=({"abc", 15432 % 125, 'Z', 688223},"__")
-- |
-- `- matched all | leftovers=__
--    |
--    +- i=0 | a="abc" | used=abc | remaining=123.456Za805f__
--    |
--    +- i=1 | a=15432 % 125 | used=123.456 | remaining=Za805f__
--    |
--    +- i=2 | a='Z' | used=Z | remaining=a805f__
--    |
--    `- i=3 | a=688223 | used=a805f | remaining=__
-- <BLANKLINE>
--
--
-- >>> import Text.Regex.Applicative.Common (digit)
-- >>> pe1' (_PRegexV (_d :& ratio :& _w :& ipaddr :& _w :& digit :& RNil) 0 $ _PFst $ pri @5 (plt 102)) "927.34a27.11.4.33c9junk"
-- <BLANKLINE>
-- TrueP  PRegexV (6) | matched all | leftovers=junk
-- |
-- +- TrueP  PFst a={'9', 1367 % 50, 'a', IP:27.11.4.33, 'c', 9} snd="junk"
-- |  |
-- |  `- TrueP  PFn @5 | a={'9', 1367 % 50, 'a', IP:27.11.4.33, 'c', 9} | b=9
-- |     |
-- |     `- TrueP  9 < 102
-- |
-- `- matched all | leftovers=junk
--    |
--    +- i=0 | a='9' | used=9 | remaining=27.34a27.11.4.33c9junk
--    |
--    +- i=1 | a=1367 % 50 | used=27.34 | remaining=a27.11.4.33c9junk
--    |
--    +- i=2 | a='a' | used=a | remaining=27.11.4.33c9junk
--    |
--    +- i=3 | a=IP:27.11.4.33 | used=27.11.4.33 | remaining=c9junk
--    |
--    +- i=4 | a='c' | used=c | remaining=9junk
--    |
--    `- i=5 | a=9 | used=9 | remaining=junk
-- <BLANKLINE>
--
-- >>> import Text.Regex.Applicative.Common (digit)
-- >>> pe1' (_PRegexV (_d :& ratio :& _w :& ipaddr :& _w :& digit :& RNil) 0 $ _PFst $ prx (plt 102)) "927.34a27.11.4.33c9junk"
-- <BLANKLINE>
-- TrueP  PRegexV (6) | matched all | leftovers=junk
-- |
-- +- TrueP  PFst a={'9', 1367 % 50, 'a', IP:27.11.4.33, 'c', 9} snd="junk"
-- |  |
-- |  `- TrueP  PFn prx | a={'9', 1367 % 50, 'a', IP:27.11.4.33, 'c', 9} | b=9
-- |     |
-- |     `- TrueP  9 < 102
-- |
-- `- matched all | leftovers=junk
--    |
--    +- i=0 | a='9' | used=9 | remaining=27.34a27.11.4.33c9junk
--    |
--    +- i=1 | a=1367 % 50 | used=27.34 | remaining=a27.11.4.33c9junk
--    |
--    +- i=2 | a='a' | used=a | remaining=27.11.4.33c9junk
--    |
--    +- i=3 | a=IP:27.11.4.33 | used=27.11.4.33 | remaining=c9junk
--    |
--    +- i=4 | a='c' | used=c | remaining=9junk
--    |
--    `- i=5 | a=9 | used=9 | remaining=junk
-- <BLANKLINE>
--
-- >>> pe2' (_PRegexV (_d :& word :& gregorian :& "abc":& RNil) 0 $ _PFst $ prx @Day (_PView days (pgt 12) * _PView years (plt 2000))) "9hello2018-12-22abcXYZ"
-- <BLANKLINE>
-- FalseP PRegexV (4) | matched all | leftovers=XYZ
-- |
-- +- FalseP PFst a={'9', "hello", 2018-12-22, "abc"} snd="XYZ"
-- |  |
-- |  `- FalseP PFn prx | a={'9', "hello", 2018-12-22, "abc"} | b=2018-12-22
-- |     |
-- |     `- FalseP PAnd
-- |        |
-- |        +- TrueP  PView s=2018-12-22 a=22
-- |        |  |
-- |        |  `- TrueP  22 > 12
-- |        |
-- |        `- FalseP PView s=2018-12-22 a=2018
-- |           |
-- |           `- FalseP 2018 < 2000
-- |
-- `- matched all | leftovers=XYZ
--    |
--    +- i=0 | a='9' | used=9 | remaining=hello2018-12-22abcXYZ
--    |
--    +- i=1 | a="hello" | used=hello | remaining=2018-12-22abcXYZ
--    |
--    +- i=2 | a=2018-12-22 | used=2018-12-22 | remaining=abcXYZ
--    |
--    `- i=3 | a="abc" | used=abc | remaining=XYZ
-- <BLANKLINE>
--
-- >>> pe2' (_PRegexV ("abc" :& ratio :& _w :& hex :& RNil) 0 1) "abc123.456Z805f__"
-- <BLANKLINE>
-- TrueP  PRegexV (4) | matched all | leftovers=__
-- |
-- +- TrueP  PConst a=({"abc", 15432 % 125, 'Z', 32863},"__")
-- |
-- `- matched all | leftovers=__
--    |
--    +- i=0 | a="abc" | used=abc | remaining=123.456Z805f__
--    |
--    +- i=1 | a=15432 % 125 | used=123.456 | remaining=Z805f__
--    |
--    +- i=2 | a='Z' | used=Z | remaining=805f__
--    |
--    `- i=3 | a=32863 | used=805f | remaining=__
-- <BLANKLINE>
--
-- >>> pe2' (_PRegexV ("abc" :& ratio :& _w :& hex :& RNil) 0 1) "abc123.456ZG805f__"
-- <BLANKLINE>
-- FalseP PRegexV (4) | only matched 3 of 4 | leftovers=G805f__
-- |
-- +- FalseP PConst a="G805f__"
-- |
-- `- only matched 3 of 4 | leftovers=G805f__
--    |
--    +- i=0 | a="abc" | used=abc | remaining=123.456ZG805f__
--    |
--    +- i=1 | a=15432 % 125 | used=123.456 | remaining=ZG805f__
--    |
--    `- i=2 | a='Z' | used=Z | remaining=G805f__
-- <BLANKLINE>
--
      --- _PRegexV ::  (RecordToList rs, ReifyConstraint Show W.Identity rs, RMap rs, RecAll W.Identity rs Show, RecAll RXHolder rs Show) =>

_PRegexV ::  (RecAll RXHolder rs Show) =>
        Rec (RE Char) rs
     -> Pred String -- leftovers
     -> Pred (Rec W.Identity rs, String)
     -> Pred String
_PRegexV regexs (Pred x e) (Pred x1 p) =
  Pred (Node nm [x,x1]) $
    \opts s ->
        let fr (RResult i aa used remn) = mkNodeDebug (TrueP, ["i=" <> show i, aa, "used=" <> used, "remaining=" <> remn]) []
        in case evalRXHolder s (toRXHolder regexs) of
             (ws, Left remn) -> let msgs = ["only matched " <> show (length ws) <> " of " <> show (recLen regexs),"leftovers=" <> remn]
                                    ns = mkNodeDebug (TrueP, msgs) (map fr ws)
                                    ll = e opts remn
                                in mkNode (getBool ll, [nm] <> msgs) [ll,ns]
             (ws, Right ((_,remn),rec)) ->
                                let msgs = ["matched all", "leftovers=" <> remn]
                                    ns = mkNodeDebug (TrueP, ["matched all", "leftovers=" <> remn]) (map fr ws)
                                    ll = p opts (rec,remn)
                                in mkNode (getBool ll, [nm] <> msgs) [ll,ns]
    where nm = "PRegexV (" <> show (recLen regexs) <> ")"

-- | tries to match the given regex using prefix search
--
-- >>> pe1' (_PRegex RLong ipaddr 0 $ _PFst $ pfn (^.. folded) $ _PShow 1) "123.2.11.22xxx"
-- <BLANKLINE>
-- TrueP  PRegex RLong as="123.2.11.22xxx" b=IP:123.2.11.22 rs="xxx"
-- |
-- `- TrueP  PFst a=IP:123.2.11.22 snd="xxx"
--    |
--    `- TrueP  PFn | a=IP:123.2.11.22 | b=[123,2,11,22]
--       |
--       `- TrueP  PShow
--          |
--          +- TrueP  PConst a=[123,2,11,22]
--          |
--          `- ===== PShow =====
--             |
--             +- i=0 a=123
--             |
--             +- i=1 a=2
--             |
--             +- i=2 a=11
--             |
--             `- i=3 a=22
-- <BLANKLINE>
--
-- >>> pe2' (_PRegex RLong (intersperseNP 4 "-" int) 0 1) "1-2-3-4"
-- <BLANKLINE>
-- TrueP  PRegex RLong as="1-2-3-4" b=[1,2,3,4] rs=""
-- |
-- `- TrueP  PConst a=([1,2,3,4],"")
-- <BLANKLINE>
--
-- >>> pe2' (_PRegex RLong (intersperseNP 4 "-" int) 0 1) "1-2-3"
-- <BLANKLINE>
-- FalseP PRegex RLong no regex match | PConst a=()
-- <BLANKLINE>
--
-- >>> pe2' (_PRegex RLong (intersperseNP 4 "-" int) 0 1) "1-2-3-4-5"
-- <BLANKLINE>
-- TrueP  PRegex RLong as="1-2-3-4-5" b=[1,2,3,4] rs="-5"
-- |
-- `- TrueP  PConst a=([1,2,3,4],"-5")
-- <BLANKLINE>
--
-- >>> pe2' (_PRegex RLong (widthExact 4 "x") 0 1) "xx"
-- <BLANKLINE>
-- FalseP PRegex RLong no regex match | PConst a=()
-- <BLANKLINE>
--
-- >>> pe2' (_PRegex RLong (widthExact 4 "x") 0 1) "xxxx"
-- <BLANKLINE>
-- TrueP  PRegex RLong as="xxxx" b=["x","x","x","x"] rs=""
-- |
-- `- TrueP  PConst a=(["x","x","x","x"],"")
-- <BLANKLINE>
--
-- >>> pe2' (_PRegex RLong (widthExact 4 "x") 0 1) "xxxxx"
-- <BLANKLINE>
-- TrueP  PRegex RLong as="xxxxx" b=["x","x","x","x"] rs="x"
-- |
-- `- TrueP  PConst a=(["x","x","x","x"],"x")
-- <BLANKLINE>
--
-- >>> pe2' (_PRegex RLong (stringCI "abCD") 0 1) "ABcd"
-- <BLANKLINE>
-- TrueP  PRegex RLong as="ABcd" b="ABcd" rs=""
-- |
-- `- TrueP  PConst a=("ABcd","")
-- <BLANKLINE>
--
-- >>> pe2' (_PRegex RLong (stringCI "abCD") 0 1) "xBcd"
-- <BLANKLINE>
-- FalseP PRegex RLong no regex match | PConst a=()
-- <BLANKLINE>
--
_PRegex :: (Foldable t, Show a, Show b) => RType -> RE a b -> Pred () -> Pred (b,[a]) -> Pred (t a)
_PRegex t regex (Pred x e) (Pred x1 p) =
  Pred (Node nm [x,x1]) $
    \opts (toList -> as) ->
     case rprefix t regex as of
      Nothing -> addMessagePre (nm <> " no regex match") (e opts ())
      Just z@(b,rs) -> let ll = p opts z
                in mkNode (getBool ll, [nm <> showA opts 1 " as=" as <> showA opts 1 " b=" b <> showA opts 1 " rs=" rs]) [ll]
  where nm = "PRegex " <> show t

-- | tries to match the given regex using infix search
--
-- >>> pe2' (_PRegexI RLong ipaddr 0 $ p_2 $ plift isIPValid) "123.4.4.200"
-- <BLANKLINE>
-- TrueP  PRegexI RLong as="123.4.4.200" b=IP:123.4.4.200 used="" remaining=""
-- |
-- `- TrueP  PFn _2 | a=("",IP:123.4.4.200,"") | b=IP:123.4.4.200
--    |
--    `- TrueP  PLift | a=IP:123.4.4.200
-- <BLANKLINE>
--
-- >>> pe2' (_PRegexI RLong ipaddr 0 $ p_2 $ plift isIPValid) "123.4.4.300"
-- <BLANKLINE>
-- FalseP PRegexI RLong as="123.4.4.300" b=IP:123.4.4.300 used="" remaining=""
-- |
-- `- FalseP PFn _2 | a=("",IP:123.4.4.300,"") | b=IP:123.4.4.300
--    |
--    `- FalseP PLift | a=IP:123.4.4.300
-- <BLANKLINE>
--
_PRegexI :: (Foldable t, Show a, Show b) => RType -> RE a b -> Pred () -> Pred ([a],b,[a]) -> Pred (t a)
_PRegexI t regex (Pred x e) (Pred x1 p) =
  Pred (Node nm [x,x1]) $
    \opts (toList -> as) ->
     case rinfix t regex as of
      Nothing -> addMessagePre (nm <> " no regex match") (e opts ())
      Just z@(before,b,after) -> let ll = p opts z
                in mkNode (getBool ll, [nm <> showA opts 1 " as=" as <> showA opts 1 " b=" b <> showA opts 1 " used=" before <> showA opts 1 " remaining=" after]) [ll]
  where nm = "PRegexI " <> show t


-- | matches i,j times
-- >>> pe2' (_PRegexN (These 3 5) (RLong, _d) 0 1) "12x"
-- <BLANKLINE>
-- FalseP PRegexN {3,5} | only matched 2 of {3,5} | leftovers="x"
-- |
-- +- FalseP PConst a=((2,3),"x")
-- |
-- `- only matched 2 of {3,5} | leftovers="x"
--    |
--    +- i=0 | b='1' | used="1" | remaining="2x"
--    |
--    `- i=1 | b='2' | used="2" | remaining="x"
-- <BLANKLINE>
--
-- >>> pe2' (_PRegexN (These 3 5) (RLong, _d) 0 1) "1234x"
-- <BLANKLINE>
-- TrueP  PRegexN {3,5} | matched all(4) | leftovers="x"
-- |
-- +- TrueP  PConst a=("1234","x")
-- |
-- `- matched all(4) | leftovers="x"
--    |
--    +- i=0 | b='1' | used="1" | remaining="234x"
--    |
--    +- i=1 | b='2' | used="2" | remaining="34x"
--    |
--    +- i=2 | b='3' | used="3" | remaining="4x"
--    |
--    `- i=3 | b='4' | used="4" | remaining="x"
-- <BLANKLINE>
--
-- >>> pe2' (_PRegexN (These 3 5) (RLong, _d) 0 1) "12345"
-- <BLANKLINE>
-- TrueP  PRegexN {3,5} | matched all(5) | leftovers=""
-- |
-- +- TrueP  PConst a=("12345","")
-- |
-- `- matched all(5) | leftovers=""
--    |
--    +- i=0 | b='1' | used="1" | remaining="2345"
--    |
--    +- i=1 | b='2' | used="2" | remaining="345"
--    |
--    +- i=2 | b='3' | used="3" | remaining="45"
--    |
--    +- i=3 | b='4' | used="4" | remaining="5"
--    |
--    `- i=4 | b='5' | used="5" | remaining=""
-- <BLANKLINE>
--
-- >>> pe2' (_PRegexN (These 3 5) (RLong, _d) 0 1) "123456"
-- <BLANKLINE>
-- TrueP  PRegexN {3,5} | matched all(5) | leftovers="6"
-- |
-- +- TrueP  PConst a=("12345","6")
-- |
-- `- matched all(5) | leftovers="6"
--    |
--    +- i=0 | b='1' | used="1" | remaining="23456"
--    |
--    +- i=1 | b='2' | used="2" | remaining="3456"
--    |
--    +- i=2 | b='3' | used="3" | remaining="456"
--    |
--    +- i=3 | b='4' | used="4" | remaining="56"
--    |
--    `- i=4 | b='5' | used="5" | remaining="6"
-- <BLANKLINE>
--
-- >>> pe2' (_PRegexN (These 3 5) (RLong, spaces *> _d) 0 1) "123456"
-- <BLANKLINE>
-- TrueP  PRegexN {3,5} | matched all(5) | leftovers="6"
-- |
-- +- TrueP  PConst a=("12345","6")
-- |
-- `- matched all(5) | leftovers="6"
--    |
--    +- i=0 | b='1' | used="1" | remaining="23456"
--    |
--    +- i=1 | b='2' | used="2" | remaining="3456"
--    |
--    +- i=2 | b='3' | used="3" | remaining="456"
--    |
--    +- i=3 | b='4' | used="4" | remaining="56"
--    |
--    `- i=4 | b='5' | used="5" | remaining="6"
-- <BLANKLINE>
--
-- >>> pe2' (_PRegexN (These 3 5) (RLong, spaces *> _d) 0 1) "12  34   56"
-- <BLANKLINE>
-- TrueP  PRegexN {3,5} | matched all(5) | leftovers="6"
-- |
-- +- TrueP  PConst a=("12345","6")
-- |
-- `- matched all(5) | leftovers="6"
--    |
--    +- i=0 | b='1' | used="1" | remaining="2  34   56"
--    |
--    +- i=1 | b='2' | used="2" | remaining="  34   56"
--    |
--    +- i=2 | b='3' | used="  3" | remaining="4   56"
--    |
--    +- i=3 | b='4' | used="4" | remaining="   56"
--    |
--    `- i=4 | b='5' | used="   5" | remaining="6"
-- <BLANKLINE>
--
_PRegexN  :: (Foldable t, Show a, Show b) =>
         These Int Int
      -> (RType, RE a b)
      -> Pred ((Int, Int), [a]) -- failure predicate
      -> Pred ([b], [a]) -- success predicate which has the result and the remaining input
      -> Pred (t a)
_PRegexN thij regex (Pred x e) (Pred x1 p) =
  Pred (Node nm [x,x1]) $
    \opts (toList -> as) ->
    let (rs,leftovers) = runRegexN thij regex as
        (lrmsgs, tt) = regexsToTT opts thij leftovers rs
        ii = these id (const 0) const thij
    in case lrmsgs of
         Left msgs ->
           let ll = e opts ((length rs, ii), leftovers)
           in mkNode (getBool ll, [nm] <> msgs) [ll,tt]
         Right msgs ->
           let ll = p opts (rs ^.. traverse . _1, leftovers)
           in mkNode (getBool ll, [nm] <> msgs) [ll,tt]
    where nm = "PRegexN " <> dispIJ thij

-- | matches i,j times with intersperse
--
-- >>> pe2' (_PRegexIP (These 4 4) RLong "." int 3 1) "444.123.3.4xxx"
-- <BLANKLINE>
-- TrueP  PRegexIP{4} | matched all(4) | leftovers="xxx"
-- |
-- +- TrueP  PConst a=([444,123,3,4],"xxx")
-- |
-- `- matched all(4) | leftovers="xxx"
--    |
--    +- i=0 | b=444 | used="444" | remaining=".123.3.4xxx"
--    |
--    +- i=1 | b=123 | used=".123" | remaining=".3.4xxx"
--    |
--    +- i=2 | b=3 | used=".3" | remaining=".4xxx"
--    |
--    `- i=3 | b=4 | used=".4" | remaining="xxx"
-- <BLANKLINE>
--
-- >>> pe2' (_PRegexIP (These 4 4) RLong "." int 3 1) "444.123.3.4xxx"
-- <BLANKLINE>
-- TrueP  PRegexIP{4} | matched all(4) | leftovers="xxx"
-- |
-- +- TrueP  PConst a=([444,123,3,4],"xxx")
-- |
-- `- matched all(4) | leftovers="xxx"
--    |
--    +- i=0 | b=444 | used="444" | remaining=".123.3.4xxx"
--    |
--    +- i=1 | b=123 | used=".123" | remaining=".3.4xxx"
--    |
--    +- i=2 | b=3 | used=".3" | remaining=".4xxx"
--    |
--    `- i=3 | b=4 | used=".4" | remaining="xxx"
-- <BLANKLINE>
--
-- >>> pe2' (_PRegexIP (These 4 4) RLong "." int 3 1) "444.123.3.4.789xxx"
-- <BLANKLINE>
-- TrueP  PRegexIP{4} | matched all(4) | leftovers=".789xxx"
-- |
-- +- TrueP  PConst a=([444,123,3,4],".789xxx")
-- |
-- `- matched all(4) | leftovers=".789xxx"
--    |
--    +- i=0 | b=444 | used="444" | remaining=".123.3.4.789xxx"
--    |
--    +- i=1 | b=123 | used=".123" | remaining=".3.4.789xxx"
--    |
--    +- i=2 | b=3 | used=".3" | remaining=".4.789xxx"
--    |
--    `- i=3 | b=4 | used=".4" | remaining=".789xxx"
-- <BLANKLINE>
--
-- >>> pe2' (_PRegexIP (These 4 4) RLong "." int 3 1) "444.123.3.xxx"
-- <BLANKLINE>
-- [Error fromInteger: n=3: use 0 or 1] PRegexIP{4} | only matched 3 of {4} | leftovers=".xxx"
-- |
-- +- [Error fromInteger: n=3: use 0 or 1] PConst a=((2,4),".xxx")
-- |
-- `- only matched 3 of {4} | leftovers=".xxx"
--    |
--    +- i=0 | b=444 | used="444" | remaining=".123.3.xxx"
--    |
--    +- i=1 | b=123 | used=".123" | remaining=".3.xxx"
--    |
--    `- i=2 | b=3 | used=".3" | remaining=".xxx"
-- <BLANKLINE>
--
-- >>> pe2' (_PRegexIP (These 4 5) RLong "." int 3 1) "444.123.3.xxx"
-- <BLANKLINE>
-- [Error fromInteger: n=3: use 0 or 1] PRegexIP{4,5} | only matched 3 of {4,5} | leftovers=".xxx"
-- |
-- +- [Error fromInteger: n=3: use 0 or 1] PConst a=((2,4),".xxx")
-- |
-- `- only matched 3 of {4,5} | leftovers=".xxx"
--    |
--    +- i=0 | b=444 | used="444" | remaining=".123.3.xxx"
--    |
--    +- i=1 | b=123 | used=".123" | remaining=".3.xxx"
--    |
--    `- i=2 | b=3 | used=".3" | remaining=".xxx"
-- <BLANKLINE>
--
-- >>> pe2' (_PRegexIP (These 4 5) RLong "." int 3 1) "444.123.3.5.6.xxx"
-- <BLANKLINE>
-- TrueP  PRegexIP{4,5} | matched all(5) | leftovers=".xxx"
-- |
-- +- TrueP  PConst a=([444,123,3,5,6],".xxx")
-- |
-- `- matched all(5) | leftovers=".xxx"
--    |
--    +- i=0 | b=444 | used="444" | remaining=".123.3.5.6.xxx"
--    |
--    +- i=1 | b=123 | used=".123" | remaining=".3.5.6.xxx"
--    |
--    +- i=2 | b=3 | used=".3" | remaining=".5.6.xxx"
--    |
--    +- i=3 | b=5 | used=".5" | remaining=".6.xxx"
--    |
--    `- i=4 | b=6 | used=".6" | remaining=".xxx"
-- <BLANKLINE>
--
_PRegexIP  :: (Foldable t, Show a, Show b) =>
         These Int Int
      -> RType
      -> RE a x
      -> RE a b
      -> Pred ((Int, Int), [a]) -- failure predicate
      -> Pred ([b], [a]) -- success predicate which has the result and the remaining input
      -> Pred (t a)
_PRegexIP thij t rdelim regex (Pred x e) (Pred x1 p) =
  Pred (Node nm [x,x1]) $
    \opts (toList -> as) ->
    let ii = these id (const 0) const thij
    in if theseRight (<=0) False thij then
          let ll = e opts ((0, ii), as)
          in mkNode (getBool ll, [nm,"noop as max <= 0"]) [ll]
       else case rprefix t regex as of
        Nothing ->
                   let ll = e opts ((0, ii), as)
                   in mkNode (getBool ll, [nm,"matched nothing"]) [ll]
        Just (b,as') ->
                          let newthij = bimapThese pred pred thij
                              (rs,leftovers) = runRegexN newthij (t, rdelim *> regex) as'
                              -- force in the first match into rs
                              (lrmsgs,tt) = regexsToTT opts thij leftovers ((b, take (length as - length as') as, as'):rs)
                          in case lrmsgs of
                               Left msgs ->
                                 let ll = e opts ((length rs, ii), leftovers)
                                 in mkNode (getBool ll, [nm] <> msgs) [ll,tt]
                               Right msgs ->
                                 let ll = p opts (b: rs ^.. traverse . _1, leftovers)
                                 in mkNode (getBool ll, [nm] <> msgs) [ll,tt]
    where nm = "PRegexIP" <> dispIJ thij



-- | matches on a range of values
--
-- first value is the lower bound and second is the upper bound
--
-- has nicer output than 'PElem'
--
-- >>> pe2' (_PRange 4 7) 5
-- <BLANKLINE>
-- TrueP  5 == [4..7]
-- <BLANKLINE>
--
-- >>> pe2' (_PRange 4 7) 3
-- <BLANKLINE>
-- FalseP 3 < 4 (Under)
-- <BLANKLINE>
--
-- >>> pe2' (_PRange 4 7) 8
-- <BLANKLINE>
-- FalseP 8 > 7 (Over)
-- <BLANKLINE>
--
_PRange :: (Show a, Ord a) => a -> a -> Pred a
_PRange a1 a2 =
  Pred (Node ("a " <> showRange a1 a2) []) $
    \opts a ->
      let (b,msg) = between' a1 a2 a
      in mkNode (_BoolP # (b == EQ), [showA opts 0 "" a <> showLit opts 0 " " msg]) []

-- | like 'Data.Foldable.length'
--
-- >>> pe1' (_PLen (pgt 1)) "abcd"
-- <BLANKLINE>
-- TrueP  PLen 4 as="abcd"
-- |
-- `- TrueP  4 > 1
-- <BLANKLINE>
--
_PElem :: (Eq a, Show a, Foldable t) => t a -> Pred a
_PElem as =
  Pred (Node ("a `elem` " <> showElem defOpts as) []) $
    \opts a ->
          mkNode (_BoolP # (a `elem` as), [showA opts 0 "" a <> " `elem` " <> showElem opts as]) []

_PLen :: Show a => Pred Int -> Pred [a]
_PLen (Pred x p) =
  Pred (Node nm [x])
  $ \opts as ->
    let ll = p opts (length as)
    in mkNode (getBool ll, [nm <> " " <> show (length as) <> showA opts 1 " as=" as]) [ll]
  where nm = "PLen"

-- works for monomorphic stuff as well as lists and maybes etc  ([],[]) is empty but not null!
-- | empty predicate which is sometimes different from 'PNull' eg ([],[]) is empty but not null
--
-- >>> pe2' _PEmpty [(),()]
-- <BLANKLINE>
-- FalseP PEmpty s=[(),()]
-- <BLANKLINE>
--
-- >>> pe2' _PEmpty ((),())
-- <BLANKLINE>
-- TrueP  PEmpty s=((),())
-- <BLANKLINE>
--
-- >>> pe2' _PEmpty [1..4]
-- <BLANKLINE>
-- FalseP PEmpty s=[1,2,3,4]
-- <BLANKLINE>
--
-- >>> pe2' _PEmpty []
-- <BLANKLINE>
-- TrueP  PEmpty s=[]
-- <BLANKLINE>
--
_PEmpty :: (Show a, AsEmpty a) => Pred a
_PEmpty =
  Pred (Node nm []) $
    \opts s ->
      mkNode (_BoolP # is _Empty s, ["PEmpty" <> showA opts 1 " s=" s]) []
  where nm = "PEmpty"

-- not as general cos doesnt work with monomorphic stuff
-- | like 'Data.Foldable.null'
--
-- >>> pe2' _PNull ((),())
-- <BLANKLINE>
-- FalseP PNull length=1 as=((),())
-- <BLANKLINE>
--
-- >>> pe2' _PNull [1..4]
-- <BLANKLINE>
-- FalseP PNull length=4 as=[1,2,3,4]
-- <BLANKLINE>
--
-- >>> pe2' _PNull []
-- <BLANKLINE>
-- TrueP  PNull length=0 as=[]
-- <BLANKLINE>
--
_PNull :: (Foldable t, Show (t a)) => Pred (t a)
_PNull =
  Pred (Node nm []) $
    \opts as ->
          mkNode (_BoolP # null as, [nm <> " length=" <> show (length as) <> showA opts 1 " as=" as]) []
  where nm = "PNull"

-- does PFst and PSnd: use 1 to emulate
-- | applies a different predicate to each side of a tuple. same as 'PFst' p * 'PSnd' q but has nicer output
--
-- >>> pe2' (_PBoth "abc" (pgt 'x')) ("AbC",'y')
-- <BLANKLINE>
-- TrueP  PBoth
-- |
-- +- TrueP  PStringCI "AbC" == "abc"
-- |
-- `- TrueP  'y' > 'x'
-- <BLANKLINE>
--
_PBoth :: Pred a1 -> Pred a2 -> Pred (a1, a2)
_PBoth (Pred x pa) (Pred x1 pb) =
  Pred (Node nm [x,x1]) $
    \opts (a,b) -> evalBinStrict "PBoth" (&&) (pa opts a) (pb opts b)
  where nm = "PBoth"

-- | applies a predicate to left hand side of a tuple and ignores the right
--
-- >>> pe' (_PFst (_PRange 4 8)) (9,'x')
-- <BLANKLINE>
-- FalseP PFst
-- |
-- `- FalseP 9 > 8 (Over)
-- <BLANKLINE>
--
_PFst :: (Show a, Show b) => Pred a -> Pred (a,b)
_PFst (Pred x p) =
  Pred (Node nm [x])
  $ \opts (a,w) ->
    let n = oHide opts
    in if n > 0 then p opts { oHide = n-1 } a
       else let ll = p opts a
            in mkNode (getBool ll, [nm <> showA opts 1 " a=" a <> showA opts 1 " snd=" w]) [ll]
  where nm = "PFst"

-- | applies a predicate to right hand side of a tuple and ignores the left
--
-- >>> pe' (_PSnd (_PRange 'm' 'y')) (9,'x')
-- <BLANKLINE>
-- TrueP  PSnd
-- |
-- `- TrueP  'x' == ['m'..'y']
-- <BLANKLINE>
--
_PSnd :: (Show a, Show b) => Pred b -> Pred (a,b)
_PSnd (Pred x p) =
  Pred (Node nm [x])
  $ \opts (w,a) ->
    let n = oHide opts
    in if n > 0 then p opts { oHide = n-1 } a
       else let ll = p opts a
            in mkNode (getBool ll, [nm <> showA opts 1 " a=" a <> showA opts 1 " fst=" w]) [ll]
  where nm = "PSnd"

-- | swap arguments in a tuple. useful when push everything good to the right
--
-- >>> pe2' (_PSwap $ _PBoth (peq 4) pid) (True,4)
-- <BLANKLINE>
-- TrueP  PSwap pab=(True,4)
-- |
-- `- TrueP  PBoth
--    |
--    +- TrueP  4 == 4
--    |
--    `- TrueP  PLift id | a=True
-- <BLANKLINE>
--
_PSwap :: (Swapped p, Show (p c d)) => Pred (p d c) -> Pred (p c d)
_PSwap (Pred x p) =
  Pred (Node nm [x])
  $ \opts pab ->
    let rr = p opts (pab ^. swapped)
    in mkNode (getBool rr, [nm <> showA opts 1 " pab=" pab]) [rr]
  where nm = "PSwap"

-- | reverse predicate
--
-- >>> pe' (_PReverse $ sinfix "zyx") ("pqrstuvwxyz" :: Text)
-- <BLANKLINE>
-- TrueP  PReverse
-- |
-- `- TrueP  PStringCI "zyx" `isInfixOf` "zyxwvutsrqp"
-- <BLANKLINE>
--
_PReverse :: (Reversing t, Show t) => Pred t -> Pred t
_PReverse (Pred x p) =
  Pred (Node nm [x])
  $ \opts t ->
    let rr = p opts (t ^. reversed)
    in mkNode (getBool rr, [nm <> showA opts 1 " a,b=" t]) [rr]
  where nm = "PReverse"

-- | like 'Data.List.splitAt', splits a foldable into two
--
-- >>> pe2' (_PSplitAt @[] 3 1) "abcdefg"
-- <BLANKLINE>
-- TrueP  PSplitAt 3 | lhs="abc" rhs="defg"
-- |
-- `- TrueP  PConst a=("abc","defg")
-- <BLANKLINE>
--
_PSplitAt :: (Foldable t, Show a) => Int -> Pred ([a], [a]) -> Pred (t a)
_PSplitAt i (Pred x p) =
  Pred (Node nm [x])
  $ \opts (toList -> as) ->
    let n = length as
        (as1,as2) = if i>=0 then splitAt i as
                    else splitAt (n+i) as ^. swapped
        msg1 = ["out of range(" <> show n <> ")" | abs i > n]
        ll = p opts (as1,as2)
    in mkNode (getBool ll, [nm] <> msg1 <> [showA opts 1 "lhs=" as1 <> showA opts 1 " rhs=" as2]) [ll]
  where nm = "PSplitAt " <> show i

-- boolean operators
-- | conjunction of two predicates
--
-- >>> pe' (_PAnd (pgt 4) (plt 10)) 7
-- <BLANKLINE>
-- TrueP  PAnd
-- |
-- +- TrueP  7 > 4
-- |
-- `- TrueP  7 < 10
-- <BLANKLINE>
--
_PAnd, _POr, _PXor, _PEquiv, _PImpl :: Pred a -> Pred a -> Pred a
_PAnd (Pred x p) (Pred x1 q) =
  Pred (Node nm [x, x1]) (\z a -> evalBinStrict nm (&&) (p z a) (q z a))
 where nm = "PAnd"

_POr (Pred x p) (Pred x1 q) =
  Pred (Node nm [x, x1]) (\z a -> evalBinStrict nm (||) (p z a) (q z a))
 where nm = "POr"

_PXor (Pred x p) (Pred x1 q) =
  Pred (Node nm [x, x1]) (\z a -> evalBinStrict nm (/=) (p z a) (q z a))
 where nm = "PXor"

_PEquiv (Pred x p) (Pred x1 q) =
  Pred (Node nm [x, x1]) (\z a -> evalBinStrict nm (==) (p z a) (q z a))
 where nm = "PEquiv"

-- | implication predicate
--
-- >>> pe' (_PImpl (pgt 4) (plt 10)) 3
-- <BLANKLINE>
-- TrueP  PImpl
-- |
-- +- FalseP 3 > 4
-- |
-- `- TrueP  3 < 10
-- <BLANKLINE>
--
_PImpl (Pred x p) (Pred x1 q) =
  Pred (Node nm [x, x1]) (\z a -> evalBinStrict nm impl (p z a) (q z a))
 where nm = "PImpl"

-- | negation predicate
--
-- >>> pe' (_PNot (_PMatch SInfix "xyz")) "abcxyzdef"
-- <BLANKLINE>
-- FalseP PNot
-- |
-- `- TrueP  PMatch "xyz" `isInfixOf` "abcxyzdef"
-- <BLANKLINE>
--
_PNot :: Pred a -> Pred a
_PNot (Pred px p) =
  Pred (Node nm [px])
   $ \opts a ->
       let ll = p opts a
       in mkNode (getBool ll & _BoolP %~ not, [nm]) [ll]
 where nm = "PNot"


-- generalises PAnds and POrs + more
-- cheating a bit by blending tacking the results of [Pred a] onto the end of the nodes of Pred [Bool]
-- | applies a list of predicates to a single value and then calls Pred [Bool] with the results
--
-- >>> pe2' (_POps [peq 2, peq 4, pgt 3,peven] $ plift and) 4
-- <BLANKLINE>
-- FalseP POps | (1,3)
-- |
-- `- FalseP PLift | a=[False,True,True,True]
--    |
--    +- FalseP i=0: 4 == 2
--    |
--    +- TrueP  i=1: 4 == 4
--    |
--    +- TrueP  i=2: 4 > 3
--    |
--    `- TrueP  i=3: PLift even | a=4
-- <BLANKLINE>
--
_POps :: Show x => [Pred x] -> Pred [Bool] -> Pred x
_POps ps (Pred y q) =
  Pred (Node nm (map _ppred ps ++ [y]))
   $ \opts a ->
    let ts = zipWith (\i p -> ((i, a),) $ _pfn p opts a) [0::Int ..] ps
    in case splitAndP opts [nm] ts of
      Left e -> e
      Right (bads,goods) ->
        let xs :: [Bool] = ts ^.. traverse . _2 . root . peBoolP . _BoolP
            ll = q opts xs
            ll' = ll & branches %~ (<> map fixit ts)
        in mkNode (getBool ll, [nm] <> [show (length bads, length goods)]) [ll']
 where nm = "POps"

-- deals with adjacent elements -- porder using pgroupBy (groupBy') is better
-- but this does give nicer tracing so good for demoing
-- | a predicate for checking that the list is the given order by checking adjacent elements
--
-- >>> pe2' (_POrder Le) [1,2,3,3,4]
-- <BLANKLINE>
-- TrueP  POrder (<=)
-- |
-- +- TrueP  i=0: 1
-- |
-- +- TrueP  i=1: 2
-- |
-- +- TrueP  i=2: 3
-- |
-- +- TrueP  i=3: 3
-- |
-- `- TrueP  i=4: 4
-- <BLANKLINE>
--
-- >>> pe2' (_POrder Le) [1,2,3,3,4,7,1]
-- <BLANKLINE>
-- FalseP POrder (<=) errs=1 (6,1)
-- |
-- +- TrueP  i=0: 1
-- |
-- +- TrueP  i=1: 2
-- |
-- +- TrueP  i=2: 3
-- |
-- +- TrueP  i=3: 3
-- |
-- +- TrueP  i=4: 4
-- |
-- +- TrueP  i=5: 7
-- |
-- `- FalseP i=6: 1
-- <BLANKLINE>
--
_POrder  :: (Foldable t, Ord a, Show a) => CmpOperator -> Pred (t a)
_POrder c =
  Pred (Node nm []) $
  \opts (toList -> as) ->
    let xs = isSorted c as
        (ts, (_je, msg1)) = orderImpl opts xs
    in mkNode (_BoolP # all fst xs, [nm <> " (" <> show c <> ")" <> msg1]) (map fixit ts)
    where nm = "POrder"

_POrderEq :: (Foldable t, Eq a, Show a) => Bool -> Pred (t a)
_POrderEq bb =
  Pred (Node nm []) $
  \opts (toList -> as) ->
    let xs = isSortedEq bb as
        (ts, (_je, msg1)) = orderImpl opts xs
    in mkNode (_BoolP # all fst xs, [nm <> " (" <> equalShow bb <> ")" <> msg1]) (map fixit ts)
    where nm = "POrderEq"


_PChangeOpts :: (POpts -> POpts) -> Pred a -> Pred a -- change opts on a predicate branch -- eg display less stuff or turn off debug for a subtree
_PChangeOpts f (Pred x p) =
  Pred (Node nm [x]) $
  \opts a ->
    let optsnew = f opts
        n = oHide optsnew
    in if n > 0 then p optsnew { oHide = n-1 } a
       else let ll = p optsnew a
                df2 = let dfs = diffOpts opts optsnew
                          ss = " diff(" <> show (length dfs) <> ") [" <> intercalate " | " dfs <> "]"
                      in if null dfs then " no diff" else ss
            in mkNode (getBool ll, [nm <> df2 <> showA optsnew 2 " new=" optsnew <> showA opts 2 " old=" opts]) [ll]
  where nm = "PChangeOpts"

_PShow1 :: Show a => Pred a -> Pred a
_PShow1 (Pred x p) =
  Pred (Node nm [x]) $
    \opts a ->
    let ll = p opts a
        n1 = mkNodeDebug (TrueP, [showA opts 0 "a=" a]) []
    in mkNode (getBool ll, [nm]) [ll, n1]
    where nm = "PShow1"

_PShowS1 :: SConv a => Pred a -> Pred a
_PShowS1 (Pred x p) =
  Pred (Node nm [x]) $
    \opts a ->
    let ll = p opts a
        n1 = mkNodeDebug (TrueP, [showA opts 0 "a=" (sstring a)]) []
    in mkNode (getBool ll, [nm]) [ll, n1]
    where nm = "PShowS1"

-- | passthrough predicate for debugging a foldable of values as a list
--
-- >>> pe' (_PShow @[] 1) "abcdef"
-- <BLANKLINE>
-- TrueP  PShow
-- |
-- +- TrueP
-- |
-- `- ===== PShow =====
--    |
--    +- i=0 a='a'
--    |
--    +- i=1 a='b'
--    |
--    +- i=2 a='c'
--    |
--    +- i=3 a='d'
--    |
--    +- i=4 a='e'
--    |
--    `- i=5 a='f'
-- <BLANKLINE>
--
-- >>> pe' (_PShow 1) ["hello","wor\nld","end"]
-- <BLANKLINE>
-- TrueP  PShow
-- |
-- +- TrueP
-- |
-- `- ===== PShow =====
--    |
--    +- i=0 a="hello"
--    |
--    +- i=1 a="wor\nld"
--    |
--    `- i=2 a="end"
-- <BLANKLINE>
--
_PShow :: (Foldable t, Show a) => Pred [a] -> Pred (t a)
_PShow (Pred x p) =
  Pred (Node nm [x]) $
    \opts (toList -> as) ->
          let ll = p opts as
              mm = mkNodeDebug (TrueP, ["===== " <> nm <> " ====="]) ns
              ns = zipWith (\i a -> mkNodeDebug (TrueP, ["i=" <> show i <> showA opts 0 " a=" a]) []) [0::Int ..] as
          in mkNode (getBool ll, [nm]) [ll, mm]
    where nm = "PShow"

-- | passthrough predicate for debugging a foldable of values as a Showable. Nicer output than 'PShow'
--
-- >>> pe' (_PShowS 1) ["hello","wor\nld","end"]
-- <BLANKLINE>
-- TrueP  PShowS
-- |
-- +- TrueP
-- |
-- `- ===== PShowS =====
--    |
--    +- i=0 a=hello
--    |
--    +- i=1 a=wor
--    |  ld
--    |
--    `- i=2 a=end
-- <BLANKLINE>
--
_PShowS :: (Foldable t, SConv a) => Pred [a] -> Pred (t a)
_PShowS (Pred x p) =
  Pred (Node nm [x]) $
    \opts (toList -> as) ->
          let ll = p opts as
              mm = mkNodeDebug (TrueP, ["===== " <> nm <> " ====="]) ns
              ns = zipWith (\i a -> mkNodeDebug (TrueP, ["i=" <> show i <> showLit opts 0 " a=" (sstring a)]) []) [0::Int ..] as
          in mkNode (getBool ll, [nm]) [ll, mm]
    where nm = "PShowS"

-- | if given predicate is false then fail with the given message string else let it continue
--
-- >>> pe' (_POrDie "oops" (pgt 4)) 5
-- <BLANKLINE>
-- TrueP  POrDie oops:ok
-- |
-- `- TrueP  5 > 4
-- <BLANKLINE>
--
-- >>> pe' (_POrDie "oops" (pgt 4)) 3
-- <BLANKLINE>
-- [Error oops] POrDie oops: found False
-- |
-- `- FalseP 3 > 4
-- <BLANKLINE>
--
_POrDie :: String -> Pred a -> Pred a
_POrDie s (Pred x p) =
  Pred (Node nm [x]) $
  \opts a ->
    let ll = p opts a
    in case getBool ll of
         TrueP -> mkNode (TrueP, [nm <> ":ok"]) [ll]
         FalseP -> mkNode (FailP (s :| []), [nm <> ": found False"]) [ll]
         FailP es -> mkNode (FailP (s N.<| es), [nm <> ": found Exception"]) [ll]
    where nm = "POrDie " <> s

-- | catch a failed predicate
--
-- >>> pe' (_PCatch 1 (_POrDie "xxx" (peq 4))) 5
-- <BLANKLINE>
-- TrueP  PCatch:Exception caught | xxx
-- |
-- +- TrueP
-- |
-- `- [Error xxx] POrDie xxx: found False
--    |
--    `- FalseP 5 == 4
-- <BLANKLINE>
--
_PCatch :: Pred () -> Pred a -> Pred a
_PCatch (Pred x e) (Pred x1 p) =
  Pred (Node nm [x,x1]) $
  \opts a ->
    let ll = p opts a
    in case getBool ll of
         FailP excs -> let ee = e opts ()
                      in mkNode (getBool ee, [nm <> ":Exception caught"] <> toList excs) [ee, ll]
         _ -> mkNode (getBool ll, [nm <> ":no exception"]) [ll]
    where nm = "PCatch"

-- | prepend an informational message either inline or nested
--
-- >>> pe' (_PMsg Nested "extra info" $ pgt 4) 5
-- <BLANKLINE>
-- TrueP  PMsg:extra info
-- |
-- `- TrueP  5 > 4
-- <BLANKLINE>
--
-- >>> pe' (_PMsg Nested "extra info" $ pgt 4) 4
-- <BLANKLINE>
-- FalseP PMsg:extra info
-- |
-- `- FalseP 4 > 4
-- <BLANKLINE>
--
-- >>> pe' (_PMsg Inline "extra info" $ pgt 4) 5
-- <BLANKLINE>
-- TrueP  extra info | 5 > 4
-- <BLANKLINE>
--
_PMsg :: Inline -> String -> Pred a -> Pred a
_PMsg hide s (Pred x p)=
  Pred (Node nm [x]) $
  \opts a ->
    let ll = p opts a
    in case hide of
         Inline -> addMessagePre s ll
         Nested -> mkNode (getBool ll, [nm <> ":" <> s]) [ll]
  where nm = "PMsg"

-- partial stuff
-- | depending on the result of Pred a calls the predicates matching 'BoolPE'.
--
-- Nothing means passthru else override: pexc pbad then pgood
--
-- >>> pe' (_PIf Nothing Nothing (Just $ pgt 45) 1) 44
-- <BLANKLINE>
-- FalseP PIf <True Branch>
-- |
-- +- FalseP 44 > 45
-- |
-- `- TrueP  <override with False>
-- <BLANKLINE>
--
-- >>> pe' (_PIf Nothing Nothing (Just $ pgt 45) 1) 44
-- <BLANKLINE>
-- FalseP PIf <True Branch>
-- |
-- +- FalseP 44 > 45
-- |
-- `- TrueP  <override with False>
-- <BLANKLINE>
--
_PIf :: Maybe (Pred a) -> Maybe (Pred a) -> Maybe (Pred a) -> Pred a -> Pred a
_PIf mpexc mpb mpg (Pred x p) =
  Pred (Node nm [x])
  $ \opts a ->
    let n = oHide opts
        ll = if n>0 then p opts { oHide = n-1 } a
             else p opts a
        mrr = (\z -> _pfn z opts a) <$> case getBool ll of
              FailP {} -> mpexc
              FalseP   -> mpb
              TrueP    -> mpg
        ss = nm <> " <" <> showBoolPSimple (getBool ll) <> " Branch>"
        b1 = getBool ll ^? _BoolP
    in case mrr of
         Nothing -> addMessagePre ("<passthrough " <> showBoolPSimple (getBool ll) <> ">") ll
         Just rr ->
           let b2 = getBool rr ^? _BoolP
               ll' = if b1 == b2 then ll
                     else addMessagePre ("<override with " <> showBoolPSimple (getBool rr) <> ">") ll
           in if n>0 then addMessagePre ss (rr & branches %~ (<>[ll']))
              else mkNode (getBool rr, [ss]) [rr,ll']
  where nm = "PIf"


-- | function application
--
-- >>> import Text.Show.Functions
-- >>> pe2' (_PFn "xx" (*) (_PApp 7 1)) 1012
-- <BLANKLINE>
-- TrueP  PFn xx | a=1012 | b=<function>
-- |
-- `- TrueP  PApp a=7 b=7084
--    |
--    `- TrueP  PConst a=7084
-- <BLANKLINE>
--
-- >>> pe2' (_PApp 5 1) (*)
-- <BLANKLINE>
-- TrueP  PApp a=5 b=<function>
-- |
-- `- TrueP  PConst a=<function>
-- <BLANKLINE>
--
-- >>> pe2' (_PApp 5 (_PApp 3 1)) (*)
-- <BLANKLINE>
-- TrueP  PApp a=5 b=<function>
-- |
-- `- TrueP  PApp a=3 b=15
--    |
--    `- TrueP  PConst a=15
-- <BLANKLINE>
--
-- >>> pe2' (_PApp 4 1) (*5)
-- <BLANKLINE>
-- TrueP  PApp a=4 b=20
-- |
-- `- TrueP  PConst a=20
-- <BLANKLINE>
--
_PApp :: (Show a, Show b) => a -> Pred b -> Pred (a -> b)
_PApp a (Pred x p) =
  Pred (Node (nm  <> " " <> show a) [x])
  $ \opts ab ->
    let b = ab a
        ll = p opts b
    in mkNode (getBool ll, [nm <> showA opts 0 " a=" a <> showA opts 1 " b=" b]) [ll]
  where nm = "PApp"

_PJoin :: Show a => a -> Pred (Pred a)
_PJoin a =
  Pred (Node (nm  <> " " <> show a) [])
  $ \opts (Pred _ pa) ->
    let ll = pa opts a
    in mkNode (getBool ll, [nm <> showA opts 0 " a=" a]) [ll]
  where nm = "PJoin"

-- if you want to just run a lens
-- | lift a 'Control.Lens.Type.Lens' or 'Control.Lens.Type.Prism' or 'Control.Lens.Type.Iso' etc into Pred
--
-- >>> pe1' (_PView (_1 . _2) $ _PLen $ pgt 3) (('x',"abcd"),True)
-- <BLANKLINE>
-- TrueP  PView s=(('x',"abcd"),True) a="abcd"
-- |
-- `- TrueP  PLen 4 as="abcd"
--    |
--    `- TrueP  4 > 3
-- <BLANKLINE>
--
_PView :: (Show a1, Show a2) => Getting a2 a1 a2 -> Pred a2 -> Pred a1
_PView g (Pred x p) =
  Pred (Node nm [x])
  $ \opts s ->
    let a = s ^. g
        ll = p opts a
    in mkNode (getBool ll, [nm <> showA opts 1 " s=" s <> showA opts 0 " a=" a]) [ll]
  where nm = "PView"

_PTree :: (TT -> TT) -> Pred a -> Pred a
_PTree f (Pred x p) =
  Pred (Node nm [x]) $
  \opts a -> f (p opts a)
  where nm = "PTree"

-- figured it out: just use the whole Pred b cos Pred b is a proxy b
-- todo: need to pull out a proxy of b
-- p opts is b->TT : somehow need to pull the 'b'
-- predeval didnt have that problem cos Pred
_PCoerce :: forall a b . (Coercible a b, Show a, Show b) => Pred b -> Pred a
_PCoerce pb@(Pred x p) =
  Pred (Node nm [x])
  $ \opts a ->
    let ll = p opts (coerce a)
        b = asProxyTypeOf (coerce a) pb
    in mkNode (getBool ll, [nm <> showA opts 0 " a=" a <> showA opts 0 " coerced=" b]) [ll]
  where nm = "PCoerce"

-- | monomorphic head predicate - 'PUncons' or 'phead' are more general
--
-- >>> pe' (_PHead 0 (peq 'x')) "xbc"
-- <BLANKLINE>
-- TrueP  PHead 'x'
-- |
-- `- TrueP  'x' == 'x'
-- <BLANKLINE>
--
-- >>> pe' (_PHead 0 (peq 'x')) "abc"
-- <BLANKLINE>
-- FalseP PHead 'a'
-- |
-- `- FalseP 'a' == 'x'
-- <BLANKLINE>
--
_PHead :: Show a => Pred () -> Pred a -> Pred [a]
_PHead (Pred x e) (Pred x1 p) =
  Pred (Node nm [x,x1])
  $ \opts as ->
     case uncons as of
       Nothing -> addMessagePre (nm <> " empty") (e opts ())
       Just (a, _) ->
         let ll = p opts a
         in mkNode (getBool ll, [nm <> showA opts 0 " " a]) [ll]
  where nm = "PHead"

_PLast :: Show a => Pred () -> Pred a -> Pred [a]
_PLast (Pred x e) (Pred x1 p) =
  Pred (Node nm [x,x1])
  $ \opts as ->
      case unsnoc as of
       Nothing -> addMessagePre (nm <> " empty") (e opts ())
       Just (_, a) ->
         let ll = p opts a
         in mkNode (getBool ll, [nm <> showA opts 0 " " a]) [ll]
  where nm = "PLast"

-- | runs a predicate on exactly one element
--
-- >>> pe' (_POne 0 (_PBoth (peq 'x') (_PLen $ plt 3)) $ peq 'x') "xyzw"
-- <BLANKLINE>
-- FalseP POne extra values! a='x' s'="yzw"
-- |
-- `- FalseP PBoth
--    |
--    +- TrueP  'x' == 'x'
--    |
--    `- FalseP PLen 3
--       |
--       `- FalseP 3 < 3
-- <BLANKLINE>
--
-- >>> pe' (_POne 0 (_PBoth (peq 'x') (_PLen $ plt 3)) $ peq 'x') "x"
-- <BLANKLINE>
-- TrueP  POne 'x'
-- |
-- `- TrueP  'x' == 'x'
-- <BLANKLINE>
--
-- >>> pe' (_POne 0 (_PBoth (peq 'x') (_PLen $ plt 3)) $ peq 'x') ""
-- <BLANKLINE>
-- FalseP POne empty!
-- <BLANKLINE>
--
_POne :: (Cons a1 a1 a2 a2, AsEmpty a1, Show a2, Show a1) => Pred () -> Pred (a2, a1) -> Pred a2 -> Pred a1
_POne (Pred x e) (Pred x1 e2) (Pred x2 p) =
  Pred (Node nm [x,x1,x2])
  $ \opts s ->
     case uncons s of
       Nothing -> addMessagePre (nm <> " empty!") (e opts ())
       Just (a, s') | is _Empty s' ->
         let ll = p opts a
         in mkNode (getBool ll, [nm <> showA opts 0 " " a]) [ll]
                   | otherwise ->
         let ll = e2 opts (a,s')
         in mkNode (getBool ll, [nm <> " extra values!" <> showA opts 0 " a=" a <> showA opts 0 " s'=" s']) [ll]
  where nm = "POne"

_POneT :: (Foldable t, Show a) => Pred () -> Pred (a, [a]) -> Pred a -> Pred (t a)
_POneT (Pred x e) (Pred x1 e2) (Pred x2 p) =
  Pred (Node nm [x,x1,x2])
  $ \opts (toList -> as) ->
     case as of
       [] -> addMessagePre (nm <> " empty!") $ e opts ()
       a:s' | null s' ->
         let ll = p opts a
         in mkNode (getBool ll, [nm <> showA opts 0 " " a]) [ll]
                   | otherwise ->
                         let ll = e2 opts (a,s')
                         in mkNode (getBool ll, [nm <> " extra values!" <> showA opts 0 " a=" a <> showA opts 0 " as=" s']) [ll]
  where nm = "POneT"

_PUnconsT :: (Foldable t, Show a) => Pred () -> Pred (a, [a]) -> Pred (t a)
_PUnconsT (Pred x e) (Pred x1 p) =
  Pred (Node nm [x,x1])
  $ \opts (toList -> as) ->
     case uncons as of
       Nothing -> addMessagePre (nm <> " empty") (e opts ())
       Just (a, s) ->
         let ll = p opts (a, s)
         in mkNode (getBool ll, [nm <> showA opts 0 " a=" a <> showA opts 1 " as=" s]) [ll]
  where nm = "PUnconsT"

-- | uncons
--
-- >>> pe1' (_PUnsnoc 0 (_PSnd (peq 'x'))) "xyz"
-- <BLANKLINE>
-- FalseP PUnsnoc a='z' s="xy"
-- |
-- `- FalseP PSnd a='z' fst="xy"
--    |
--    `- FalseP 'z' == 'x'
-- <BLANKLINE>
--
-- >>> pe' (_PUncons @String (pfalse' "dude") 1) ""
-- <BLANKLINE>
-- FalseP PUncons empty | dude
-- <BLANKLINE>
--
-- >>> pe1' (_PUncons @[_] (pfalse' "dude") 1) ""
-- <BLANKLINE>
-- FalseP PUncons empty | PConst a=() | dude
-- <BLANKLINE>
--
-- >>> pe1' (_PUncons @Text (pfalse' "dude") 1) "abc"
-- <BLANKLINE>
-- TrueP  PUncons a='a' s="bc"
-- |
-- `- TrueP  PConst a=('a',"bc")
-- <BLANKLINE>
--
-- >>> pe1' (_PUncons @Text (pfalse' "dude") 1) ""
-- <BLANKLINE>
-- FalseP PUncons empty | PConst a=() | dude
-- <BLANKLINE>
--
_PUncons :: (Cons a1 a1 a2 a2, Show a2, Show a1) => Pred () -> Pred (a2, a1) -> Pred a1
_PUncons (Pred x e) (Pred x1 p) =
  Pred (Node nm [x,x1])
  $ \opts s' ->
     case uncons s' of
       Nothing -> addMessagePre (nm <> " empty") (e opts ())
       Just (a, s) ->
         let ll = p opts (a, s)
         in mkNode (getBool ll, [nm <> showA opts 0 " a=" a <> showA opts 1 " s=" s]) [ll]
  where nm = "PUncons"

_PUnsnocT :: (Foldable t, Show a) => Pred () -> Pred ([a], a) -> Pred (t a)
_PUnsnocT (Pred x e) (Pred x1 p) =
  Pred (Node nm [x,x1])
  $ \opts (toList -> as) ->
     case unsnoc as of
         Nothing -> addMessagePre (nm <> " empty") (e opts ())
         Just (s, a) ->
           let ll = p opts (s, a)
           in mkNode (getBool ll, [nm <> showA opts 0 " a=" a <> showA opts 1 " as=" s]) [ll]
  where nm = "PUnsnocT"

-- | unsnoc
--
-- >>> pe1' (_PUnsnoc 0 (_PSnd (peq 'x'))) "xyz"
-- <BLANKLINE>
-- FalseP PUnsnoc a='z' s="xy"
-- |
-- `- FalseP PSnd a='z' fst="xy"
--    |
--    `- FalseP 'z' == 'x'
-- <BLANKLINE>
--
_PUnsnoc :: (Snoc a1 a1 a2 a2, Show a2, Show a1) => Pred () -> Pred (a1, a2) -> Pred a1
_PUnsnoc (Pred x e) (Pred x1 p) =
  Pred (Node nm [x,x1])
  $ \opts s' ->
     case unsnoc s' of
         Nothing -> addMessagePre (nm <> " empty") (e opts ())
         Just (s, a) ->
           let ll = p opts (s, a)
           in mkNode (getBool ll, [nm <> showA opts 0 " a=" a <> showA opts 1 " s=" s]) [ll]
  where nm = "PUnsnoc"

-- | index into a structure
--
-- >>> :set -XFlexibleContexts
-- >>> :set -XGADTs
-- >>> let zzz = _PIx "glossary" 0 . _PIx "GlossDiv" 0 . _PIx "GlossList" 0 . _PIx "GlossEntry" 0 . _PIx "GlossSee" 0
-- >>> pe' (zzz $ scs "mARkup") json1
-- <BLANKLINE>
-- FalseP PIx "glossary" Object (fromList [("GlossDiv",Object (fromLi...
-- |
-- `- FalseP PIx "GlossDiv" Object (fromList [("title",String "S"),("...
--    |
--    `- FalseP PIx "GlossList" Object (fromList [("GlossEntry",Objec...
--       |
--       `- FalseP PIx "GlossEntry" Object (fromList [("GlossSee",Str...
--          |
--          `- FalseP PIx "GlossSee" String "markup"
--             |
--             `- FalseP PStringCS String "markup" == String "mARkup"
-- <BLANKLINE>
--
_PIx :: (Ixed s, Show (Index s), Show (IxValue s)) => Index s -> Pred () -> Pred (IxValue s) -> Pred s
_PIx i (Pred ee e) (Pred px p) =
  Pred (Node nm [ee,px])
  $ \opts as -> case as ^? ix i of
               Nothing -> addMessagePre (nm <> " not found") (e opts ())
               Just a ->
                 let ll = p opts a
                 in mkNode (getBool ll, [nm <> showA opts 0 " " a]) [ll]
  where nm = "PIx " ++ show i

-- | intersection of two lists:
--
-- calls a predicate with lists for left only, both and right only
--
-- >>> pe1' (_PISect 1) ("abc","daaef":: String)
-- <BLANKLINE>
-- TrueP  PISect left="bc" isect="a" right="adef"
-- |
-- `- TrueP  PConst a=("bc","a","adef")
-- <BLANKLINE>
--
-- >>> pe1' (_PISect 1) ("abc","daaaef":: String)
-- <BLANKLINE>
-- TrueP  PISect left="bc" isect="a" right="aadef"
-- |
-- `- TrueP  PConst a=("bc","a","aadef")
-- <BLANKLINE>
--
_PISect :: (Foldable t, Ord a, Show a) => Pred ([a], [a], [a]) -> Pred (t a, t a)
_PISect (Pred w p) =
  Pred (Node nm [w])
  $ \opts (toList *** toList -> (as,bs)) ->
      let (x,y,z) = isect (as, bs)
          ll = p opts (x,y,z)
      in mkNode (getBool ll, [nm
                             <> showA opts 2 " as=" as
                             <> showA opts 2 " bs=" bs
                             <> showA opts 1 " left=" x
                             <> showA opts 1 " isect=" y
                             <> showA opts 1 " right=" z
                             ]) [ll]
  where nm = "PISect"

-- | intersection of a list. use 'PISect' if only using two values
--
-- 'PISect' will give you stuff in left both and right
--
-- >>> pe1' (_PISectList @[] 1) $ reverse ["abdbc","defbba","bbbbd"]
-- <BLANKLINE>
-- TrueP  PISectList unmatched="bbaefc" matched="bbd"
-- |
-- `- TrueP  PConst a=("bbaefc","bbd")
-- <BLANKLINE>
--
-- >>> pe1' (_PISectList @[] 1) $ reverse ["abdc","defba","bd"]
-- <BLANKLINE>
-- TrueP  PISectList unmatched="aefc" matched="bd"
-- |
-- `- TrueP  PConst a=("aefc","bd")
-- <BLANKLINE>
--
-- >>> pe1' (_PISectList @[] 1) ["abdc","defba","bd"]
-- <BLANKLINE>
-- TrueP  PISectList unmatched="acaef" matched="bd"
-- |
-- `- TrueP  PConst a=("acaef","bd")
-- <BLANKLINE>
--
-- >>> pe1' (_PISectList @[] 1) ["abdc","defa","bd"]
-- <BLANKLINE>
-- TrueP  PISectList unmatched="abcaefb" matched="d"
-- |
-- `- TrueP  PConst a=("abcaefb","d")
-- <BLANKLINE>
--
_PISectList :: (Foldable t, Foldable u, Ord a, Show a) => Pred ([a], [a]) -> Pred (u (t a))
_PISectList (Pred x p) =
  Pred (Node nm [x])
  $ \opts (fmap toList . toList -> aas) ->
    let (bs,gs) = isectList aas
        ll = p opts (bs,gs)
    in mkNode (getBool ll, [nm
                               <> showA opts 2 " aas=" aas
                               <> showA opts 1 " unmatched=" bs
                               <> showA opts 1 " matched=" gs
                               ]) [ll]
  where nm = "PISectList"

-- | divides a list into two with not matching on the left and transformed on the right
--
-- >>> pe1' (_PMorph (^? _Left . to show) 1) [Left 1,Left 10,Left 12]
-- <BLANKLINE>
-- TrueP  PMorph bad=[] good=["1","10","12"]
-- |
-- `- TrueP  PConst a=([],["1","10","12"])
-- <BLANKLINE>
--
-- >>> pe1' (_PMorph (^? _Left . to show) 1) [Left 1,Left 10,Left 12,Right 'a']
-- <BLANKLINE>
-- TrueP  PMorph bad=[Right 'a'] good=["1","10","12"]
-- |
-- `- TrueP  PConst a=([Right 'a'],["1","10","12"])
-- <BLANKLINE>
--
_PMorph :: (Foldable t, Show a, Show b) => (a -> Maybe b) -> Pred ([a], [b]) -> Pred (t a)
_PMorph amb (Pred x p) =
  Pred (Node nm [x])
  $ \opts (toList -> as) ->
      let (bs,gs) = partitionEithers (map (maybeToEither amb) as)
          ll = p opts (bs,gs)
      in mkNode (getBool ll, [nm <> showA opts 2 " " as <> showA opts 1 " bad=" bs <> showA opts 1 " good=" gs]) [ll]
  where nm = "PMorph"

-- PEither and PMaybe can replace a lot if not all of the PFnPartial stuff: can use PFn to bust it down into PEither
-- | deconstructs 'Maybe'
--
-- >>> pe' (_PMaybe 0 (peq 'x')) Nothing
-- <BLANKLINE>
-- FalseP PMaybe (Nothing)
-- <BLANKLINE>
--
-- >>> pe' (_PMaybe 0 (peq 'x')) (Just 'y')
-- <BLANKLINE>
-- FalseP PMaybe (Just) 'y'
-- |
-- `- FalseP 'y' == 'x'
-- <BLANKLINE>
--
-- >>> pe' (_PMaybe 0 (peq 'x')) (Just 'x')
-- <BLANKLINE>
-- TrueP  PMaybe (Just) 'x'
-- |
-- `- TrueP  'x' == 'x'
-- <BLANKLINE>
--
_PMaybe :: Show a => Pred () -> Pred a -> Pred (Maybe a)
_PMaybe (Pred px p) (Pred qq q) =
  Pred (Node nm [px, qq])
  $ \opts ->
      \case
        Nothing -> addMessagePre (nm <> " (Nothing)") (p opts ())
        Just b -> let rr = q opts b
                  in mkNode (getBool rr, [nm <> " (Just)" <> showA opts 0 " " b]) [rr]
 where nm = "PMaybe"

-- prism1 == pfalse prism2 == pfail msg
-- | deconstructs 'Either'
--
-- >>> pe' (_PEither (peq 'x') (-pid)) (Left 'x')
-- <BLANKLINE>
-- TrueP  PEither (Left) 'x'
-- |
-- `- TrueP  'x' == 'x'
-- <BLANKLINE>
--
-- >>> pe' (_PEither (peq 'x') (-pid)) (Right False)
-- <BLANKLINE>
-- TrueP  PEither (Right) False
-- |
-- `- TrueP  PNot
--    |
--    `- FalseP PLift id
-- <BLANKLINE>
--
_PEither :: (Show a, Show b) => Pred a -> Pred b -> Pred (Either a b)
_PEither (Pred x p) (Pred x1 q) =
  Pred (Node nm [x,x1]) $
  \opts ->
    \case
      Left a -> let ll = p opts a
                in mkNode (getBool ll, [nm <> " (Left)" <> showA opts 0 " " a]) [ll]
      Right b -> let rr = q opts b
                 in mkNode (getBool rr, [nm <> " (Right)" <> showA opts 0 " " b]) [rr]
 where nm = "PEither"

-- | deconstructs 'Data.These.These'
--
-- >>> pe' (_PThese (peq 'x') (pgt 4) $ pfn (first $ \a -> ord 'z' - ord a) pgt2) (These 'x' 4)
-- <BLANKLINE>
-- FalseP PThese (These) a='x' b=4
-- |
-- `- FalseP PFn | a=('x',4) | b=(2,4)
--    |
--    `- FalseP PCmp2 2 > 4
-- <BLANKLINE>
--
_PThese :: (Show a1, Show a2) => Pred a1 -> Pred a2 -> Pred (a1, a2) -> Pred (These a1 a2)
_PThese (Pred x p) (Pred x1 q) (Pred x2 pq) =
  Pred (Node nm [x,x1,x2]) $
  \opts ->
    \case
      This a -> let ll = p opts a
                in mkNode (getBool ll, [nm <> " (This)" <> showA opts 0 " a=" a]) [ll]
      That b -> let rr = q opts b
                 in mkNode (getBool rr, [nm <> " (That)" <> showA opts 0 " b=" b]) [rr]
      These a b -> let ll = pq opts (a, b)
                 in mkNode (getBool ll, [nm <> " (These)" <> showA opts 0 " a=" a <> showA opts 0 " b=" b]) [ll]
  where nm = "PThese"


_PPrism :: Show b => String -> (a -> Maybe b) -> Pred () -> Pred b -> Pred a
_PPrism s f (Pred ee e) (Pred px p) =
  Pred (Node (nm <> " " <> s) [ee,px])
  $ \opts a ->
    case f a of
      Nothing -> addMessagePre (nm <> " (Nothing) [" <> s <> "]") (e opts ())
      Just b -> let rr = p opts b
                in mkNode (getBool rr, [nm <> " (Just) [" <> s <> "]" <> showA opts 1 " " b]) [rr]
 where nm = "PPrism"

-- | lift a maybe over a tuple on lhs
--
-- >>> pe1' (_PPrismL "dude" (^? _Left) 0 (_PFn "zz" (first (succ.succ)) 1)) (Left 'x',True)
-- <BLANKLINE>
-- TrueP  PPrismL (Just) [dude] 'x'
-- |
-- `- TrueP  PFn zz | a=('x',True) | b=('z',True)
--    |
--    `- TrueP  PConst a=('z',True)
-- <BLANKLINE>
--
_PPrismL     :: Show b => String -> (a -> Maybe b) -> Pred x -> Pred (b, x) -> Pred (a, x)
_PPrismL s f (Pred ee e) (Pred px p) =
  Pred (Node (nm <> " " <> s) [ee,px])
  $ \opts (a,x) ->
    case f a of
      Nothing -> addMessagePre (nm <> " (Nothing) [" <> s <> "]") (e opts x)
      Just b -> let rr = p opts (b, x)
                in mkNode (getBool rr, [nm <> " (Just) [" <> s <> "]" <> showA opts 1 " " b]) [rr]
  where nm = "PPrismL"

_PPrismR     :: Show b => String -> (a -> Maybe b) -> Pred x -> Pred (x, b) -> Pred (x, a)
_PPrismR s f (Pred ee e) (Pred px p) =
  Pred (Node (nm <> " " <> s) [ee,px])
  $ \opts (x,a) ->
    case f a of
      Nothing -> addMessagePre (nm <> " (Nothing) [" <> s <> "]") (e opts x)
      Just b -> let rr = p opts (x, b)
                in mkNode (getBool rr, [nm <> " (Just) [" <> s <> "]" <> showA opts 1 " " b]) [rr]
  where nm = "PPrismR"

_PPrismLE    :: (Show c, Show b) => String -> (a -> Either b c) -> Pred (b, x) -> Pred (c, x) -> Pred (a, x)
_PPrismLE s f (Pred ee p) (Pred px q) =
  Pred (Node (nm <> " " <> s) [ee,px])
  $ \opts (a,x) ->
    case f a of
      Left b -> let rr = p opts (b, x)
                in mkNode (getBool rr, [nm <> " (Left) [" <> s <> "]" <> showA opts 1 " " b]) [rr]
      Right c -> let rr = q opts (c, x)
                in mkNode (getBool rr, [nm <> " (Right) [" <> s <> "]" <> showA opts 1 " " c]) [rr]
  where nm = "PPrismLE"

_PPrismRE    :: (Show c, Show b) => String -> (a -> Either b c) -> Pred (x, b) -> Pred (x, c) -> Pred (x, a)
_PPrismRE s f (Pred ee p) (Pred px q) =
  Pred (Node (nm <> " " <> s) [ee,px])
  $ \opts (x,a) ->
    case f a of
      Left b -> let rr = p opts (x, b)
                in mkNode (getBool rr, [nm <> " (Left) [" <> s <> "]" <> showA opts 1 " " b]) [rr]
      Right c -> let rr = q opts (x, c)
                in mkNode (getBool rr, [nm <> " (Right) [" <> s <> "]" <> showA opts 1 " " c]) [rr]
  where nm = "PPrismRE"

-- | matches predicates to values (order is not important)
--
-- a value is not allowed to be matched by more than one predicate
--
-- see 'preq' 'popt' etc
--
-- >>> pe1' (_PLinear Rigid [preq (peq 'x'), preq (peq 'y'),preq (peq 'w')]) "yxxxxo"
-- <BLANKLINE>
-- FalseP PLinear Failed Pred [Int] | errors(1): NoMatch 5
-- |
-- +- FalseP Predicates | PZipAnd | PZipExact | (bad,good)=(2,1)
-- |  |
-- |  `- FalseP PLift and | a=[False,True,False]
-- |     |
-- |     +- FalseP i=0
-- |     |  |
-- |     |  +- FalseP 4 > 1 (Over)
-- |     |  |
-- |     |  `- a == 'x'
-- |     |
-- |     +- TrueP  i=1
-- |     |  |
-- |     |  +- TrueP  1 == 1
-- |     |  |
-- |     |  `- a == 'y'
-- |     |
-- |     `- FalseP i=2
-- |        |
-- |        +- FalseP 0 < 1 (Under)
-- |        |
-- |        `- a == 'w'
-- |
-- +- TrueP  PLinear | OneMatch 0 a='y' cnt=1 (i=1, a='y')
-- |  |
-- |  +- FalseP i=0: 'y' == 'x'
-- |  |
-- |  +- TrueP  i=1: 'y' == 'y'
-- |  |
-- |  `- FalseP i=2: 'y' == 'w'
-- |
-- +- TrueP  PLinear | OneMatch 1 a='x' cnt=1 (i=0, a='x')
-- |  |
-- |  +- TrueP  i=0: 'x' == 'x'
-- |  |
-- |  +- FalseP i=1: 'x' == 'y'
-- |  |
-- |  `- FalseP i=2: 'x' == 'w'
-- |
-- +- TrueP  PLinear | OneMatch 2 a='x' cnt=1 (i=0, a='x')
-- |  |
-- |  +- TrueP  i=0: 'x' == 'x'
-- |  |
-- |  +- FalseP i=1: 'x' == 'y'
-- |  |
-- |  `- FalseP i=2: 'x' == 'w'
-- |
-- +- TrueP  PLinear | OneMatch 3 a='x' cnt=1 (i=0, a='x')
-- |  |
-- |  +- TrueP  i=0: 'x' == 'x'
-- |  |
-- |  +- FalseP i=1: 'x' == 'y'
-- |  |
-- |  `- FalseP i=2: 'x' == 'w'
-- |
-- +- TrueP  PLinear | OneMatch 4 a='x' cnt=1 (i=0, a='x')
-- |  |
-- |  +- TrueP  i=0: 'x' == 'x'
-- |  |
-- |  +- FalseP i=1: 'x' == 'y'
-- |  |
-- |  `- FalseP i=2: 'x' == 'w'
-- |
-- `- FalseP PLinear NoMatch 5 a='o'
--    |
--    +- FalseP i=0: 'o' == 'x'
--    |
--    +- FalseP i=1: 'o' == 'y'
--    |
--    `- FalseP i=2: 'o' == 'w'
-- <BLANKLINE>
--
-- >>> let m = M.fromList $ zip ['a'..] [12..15]
-- >>> pe1' (pilist $ _PLinear Rigid [preq (_PFst (peq 'a')),preq (_PFst (peq 'b'))]) m
-- <BLANKLINE>
-- FalseP PLinear | errors(2): NoMatch 2 | NoMatch 3
-- |
-- +- TrueP  Predicates | PZipAnd | PZipExact | (bad,good)=(0,2)
-- |  |
-- |  `- TrueP  PLift and | a=[True,True]
-- |     |
-- |     +- TrueP  i=0
-- |     |  |
-- |     |  +- TrueP  1 == 1
-- |     |  |
-- |     |  `- PFst
-- |     |     |
-- |     |     `- a == 'a'
-- |     |
-- |     `- TrueP  i=1
-- |        |
-- |        +- TrueP  1 == 1
-- |        |
-- |        `- PFst
-- |           |
-- |           `- a == 'b'
-- |
-- +- TrueP  PLinear | OneMatch 0 a=('a',12) cnt=1 (i=0, a=('a',12))
-- |  |
-- |  +- TrueP  i=0: PFst a='a' snd=12
-- |  |  |
-- |  |  `- TrueP  'a' == 'a'
-- |  |
-- |  `- FalseP i=1: PFst a='a' snd=12
-- |     |
-- |     `- FalseP 'a' == 'b'
-- |
-- +- TrueP  PLinear | OneMatch 1 a=('b',13) cnt=1 (i=1, a=('b',13))
-- |  |
-- |  +- FalseP i=0: PFst a='b' snd=13
-- |  |  |
-- |  |  `- FalseP 'b' == 'a'
-- |  |
-- |  `- TrueP  i=1: PFst a='b' snd=13
-- |     |
-- |     `- TrueP  'b' == 'b'
-- |
-- +- FalseP PLinear NoMatch 2 a=('c',14)
-- |  |
-- |  +- FalseP i=0: PFst a='c' snd=14
-- |  |  |
-- |  |  `- FalseP 'c' == 'a'
-- |  |
-- |  `- FalseP i=1: PFst a='c' snd=14
-- |     |
-- |     `- FalseP 'c' == 'b'
-- |
-- `- FalseP PLinear NoMatch 3 a=('d',15)
--    |
--    +- FalseP i=0: PFst a='d' snd=15
--    |  |
--    |  `- FalseP 'd' == 'a'
--    |
--    `- FalseP i=1: PFst a='d' snd=15
--       |
--       `- FalseP 'd' == 'b'
-- <BLANKLINE>
--
_PLinear :: (Show a, Foldable t) => Rigid -> [(Pred Int, Pred a)] -> Pred (t a)
_PLinear noextravalues qps =
  Pred (Node (nm <> " " <> show noextravalues) (concatMap (\(x,y) -> [_ppred x,_ppred y]) qps))
  $ \opts (toList -> as) -> linearImpl opts nm noextravalues qps as
  where nm = "PLinear"

-- | runs the predicate against all the values and expects all to succeed. see 'pquantifier' and 'PPartition'
--
-- >>> pe1' (_PForAll (_PLen (peq 3) * _PHead 0 (peq 'f'))) ["foo","ab","fghi","fxx",""]
-- <BLANKLINE>
-- FalseP PForAll | cnt=3 (i=1, a="ab")
-- |
-- +- TrueP  i=0: PAnd
-- |  |
-- |  +- TrueP  PLen 3 as="foo"
-- |  |  |
-- |  |  `- TrueP  3 == 3
-- |  |
-- |  `- TrueP  PHead 'f'
-- |     |
-- |     `- TrueP  'f' == 'f'
-- |
-- +- FalseP i=1: PAnd
-- |  |
-- |  +- FalseP PLen 2 as="ab"
-- |  |  |
-- |  |  `- FalseP 2 == 3
-- |  |
-- |  `- FalseP PHead 'a'
-- |     |
-- |     `- FalseP 'a' == 'f'
-- |
-- +- FalseP i=2: PAnd
-- |  |
-- |  +- FalseP PLen 4 as="fghi"
-- |  |  |
-- |  |  `- FalseP 4 == 3
-- |  |
-- |  `- TrueP  PHead 'f'
-- |     |
-- |     `- TrueP  'f' == 'f'
-- |
-- +- TrueP  i=3: PAnd
-- |  |
-- |  +- TrueP  PLen 3 as="fxx"
-- |  |  |
-- |  |  `- TrueP  3 == 3
-- |  |
-- |  `- TrueP  PHead 'f'
-- |     |
-- |     `- TrueP  'f' == 'f'
-- |
-- `- FalseP i=4: PAnd
--    |
--    +- FalseP PLen 0 as=""
--    |  |
--    |  `- FalseP 0 == 3
--    |
--    `- FalseP PHead empty | PConst a=()
-- <BLANKLINE>
--
_PForAll :: Show a => Pred a -> Pred [a]
_PForAll (Pred x p) =
  Pred (Node nm [x]) $ \opts as ->
          let ts = zipWith (\i a -> ((i, a), p opts a)) [0::Int ..] as
          in case splitAndP opts [nm] ts of
               Left e -> e
               Right ([], _) -> mkNode (TrueP, [nm]) (map fixit ts)
               Right (bads@(b:_), _) -> mkNode (FalseP, [nm] <> ["cnt=" <> show (length bads) <> " " <> formatList opts [b]]) (map fixit ts)
  where nm = "PForAll"

-- | runs the predicate against all the values and expects at least one to succeed. see 'pquantifier' and 'PPartition'
--
-- >>> pe' (_PExists (peq 4)) [1..7]
-- <BLANKLINE>
-- TrueP  PExists | cnt=1 (i=3, a=4)
-- |
-- +- FalseP i=0: 1 == 4
-- |
-- +- FalseP i=1: 2 == 4
-- |
-- +- FalseP i=2: 3 == 4
-- |
-- +- TrueP  i=3: 4 == 4
-- |
-- +- FalseP i=4: 5 == 4
-- |
-- +- FalseP i=5: 6 == 4
-- |
-- `- FalseP i=6: 7 == 4
-- <BLANKLINE>
--
_PExists :: (Show a, Foldable t) => Pred a -> Pred (t a)
_PExists (Pred x p) =
  Pred (Node nm [x]) $ \opts (toList -> as) ->
          let ts = zipWith (\i a -> ((i, a), p opts a)) [0::Int ..] as
          in case splitAndP opts [nm] ts of
               Left e -> e
               Right (_, goods@(g:_)) -> mkNode (TrueP, [nm] <> ["cnt="<> show (length goods) <> " " <> formatList opts [g]]) (map fixit ts)
               Right _ -> mkNode (FalseP, [nm]) (map fixit ts) -- in this case all are bad!
  where nm = "PExists"

-- if too many 'ts' then show first n and last n and then 1 bad one if not already shown
-- better be real sure that the good one or bad one gets included else we change the result of eval!

-- | matches exact number of predicates with values. see 'PSeq'
--
-- >>> pe2' (_PZipExact [plift isDigit,plift isAlpha,plift isDigit] 0 1) "9b8"
-- <BLANKLINE>
-- TrueP  PZipExact | as="9b8" | (bad,good)=(0,3)
-- |
-- `- TrueP  PConst a=[True,True,True]
--    |
--    +- TrueP  i=0: PLift | a='9'
--    |
--    +- TrueP  i=1: PLift | a='b'
--    |
--    `- TrueP  i=2: PLift | a='8'
-- <BLANKLINE>
--
-- >>> pe2' (_PZipExact [plift isDigit,plift isAlpha,plift isDigit] 0 1) "9bb"
-- <BLANKLINE>
-- TrueP  PZipExact | as="9bb" | (bad,good)=(1,2)
-- |
-- `- TrueP  PConst a=[True,True,False]
--    |
--    +- TrueP  i=0: PLift | a='9'
--    |
--    +- TrueP  i=1: PLift | a='b'
--    |
--    `- FalseP i=2: PLift | a='b'
-- <BLANKLINE>
--
-- >>> pe2' (_PZipExact [plift isDigit,plift isAlpha,plift isDigit] 0 1) "9b"
-- <BLANKLINE>
-- FalseP PZipExact |  length ps 3 /= length as 2
-- |
-- `- FalseP PConst a=(3,2)
-- <BLANKLINE>
--
-- >>> pe2' (_PZipExact ["abc",sinfix "xyz"] 0 1) ["AbC", "aaaaxyzbbb"]
-- <BLANKLINE>
-- TrueP  PZipExact | as=["AbC","aaaaxyzbbb"] | (bad,good)=(0,2)
-- |
-- `- TrueP  PConst a=[True,True]
--    |
--    +- TrueP  i=0: PStringCI "AbC" == "abc"
--    |
--    `- TrueP  i=1: PStringCI "xyz" `isInfixOf` "aaaaxyzbbb"
-- <BLANKLINE>
--
_PZipExact :: (Foldable t, Show x) =>
  [Pred x] -> Pred (Int,Int) -> Pred [Bool] -> Pred (t x)
_PZipExact ps e (Pred x q) =
  Pred (Node nm (map _ppred ps ++ [x])) $
    \opts (toList -> as) ->
    let mmsg1 = if length ps /= length as
                then Just (" length ps " <> show (length ps) <> " /= length as " <> show (length as) <> " ")
                else Nothing
    in case mmsg1 of
         Just msg1 -> let ll = _pfn e opts (length ps,length as)
                      in mkNode (getBool ll, [nm,msg1]) [ll]
         _ -> let ts = zipWith (\(i, p) a -> ((i, a),) $ _pfn p opts a) (zip [0::Int ..] ps) as
                  msgs = nm : ["truncated" | isTruncated opts ts] <> maybeToList mmsg1 <> [showA opts 2 "as=" as]
              in case splitAndP opts msgs ts of
                      Left ex -> ex
                      Right (bads,goods) ->
                        let xs = ts ^.. traverse . _2 . root . peBoolP . _BoolP
                            ll = q opts xs
                            ll' = ll & branches %~ (<> map fixit ts)
                        in mkNode (getBool ll, msgs <> ["(bad,good)=" <> show (length bads, length goods)]) [ll']
  where nm = "PZipExact"

-- | run all the predicates against the values and retain the leftovers
-- | for a stricter version see 'PZipExact'
--
-- >>> pe2' (_PSeq [pregex _d 1] $ _PSnd $ _PSeq ["DudE","xx"] 1) ["9","dude"]
-- <BLANKLINE>
-- TrueP  PSeq | length ps 1 /= length as 2  | as=["9","dude"] | (0,1)
-- |
-- `- TrueP  PSnd a=["dude"] fst=[True]
--    |
--    +- TrueP  i=0: PRegex RLong as="9" b='9' rs=""
--    |  |
--    |  `- TrueP  PConst a=('9',"")
--    |
--    `- TrueP  PSeq | length ps 2 /= length as 1  | as=["dude"] | (0,1)
--       |
--       `- TrueP  PConst a=([True],[])
--          |
--          `- TrueP  i=0: PStringCI "dude" == "DudE"
-- <BLANKLINE>
--
-- >>> pe2' (_PSeq [peq 1,peq 4] $ _PBoth (plift or) $ _PSeq [peq 111,peq 2] $ _PBoth (plift or) $ _PSeq [peq 11] 1) [2,4,21,111]
-- <BLANKLINE>
-- FalseP PSeq | length ps 2 /= length as 4  | as=[2,4,21,111] | (1,1)
-- |
-- `- FalseP PBoth
--    |
--    +- FalseP i=0: 2 == 1
--    |
--    +- TrueP  i=1: 4 == 4
--    |
--    +- TrueP  PLift | a=[False,True]
--    |
--    `- FalseP PSeq | as=[21,111] | (2,0)
--       |
--       `- FalseP PBoth
--          |
--          +- FalseP i=0: 21 == 111
--          |
--          +- FalseP i=1: 111 == 2
--          |
--          +- FalseP PLift | a=[False,False]
--          |
--          `- TrueP  PSeq | length ps 1 /= length as 0  | as=[] | (0,0)
--             |
--             `- TrueP  PConst a=([],[])
-- <BLANKLINE>
--
_PSeq :: (Foldable t, Show a) => [Pred a] -> Pred ([Bool], [a]) -> Pred (t a)
_PSeq ps (Pred x q) =
  Pred (Node nm (map _ppred ps ++ [x])) $
    \opts (toList -> as) ->
    let mmsg1 = if length ps /= length as
                then Just ("length ps " <> show (length ps) <> " /= length as " <> show (length as) <> " ")
                else Nothing
        ts = zipWith (\(i, p) a -> ((i, a),) $ _pfn p opts a) (zip [0::Int ..] ps) as
        msgs = nm : ["truncated" | isTruncated opts ts] <> maybeToList mmsg1 <> [showA opts 2 "as=" as]
    in case splitAndP opts msgs ts of
          Left e -> e
          Right (bads,goods) ->
            let xs = ts ^.. traverse . _2 . root . peBoolP . _BoolP
                ll = q opts (xs,drop (length ps) as)
                ll' = ll & branches %~ (map fixit ts <>)
            in mkNode (getBool ll, msgs <> [show (length bads, length goods)]) [ll']

  where nm = "PSeq"

-- | 'Data.List.partition' except failures are on the left and successes on the right
--
-- >>> pe2' (_PPartition peven $ (_PFn "***" (sum *** sum)) pgt2) [1..10]
-- <BLANKLINE>
-- FalseP PPartition | lefts=5 (0,1) | rights=5 (1,2)
-- |
-- +- FalseP PPartition Predicate
-- |  |
-- |  `- FalseP PFn *** | a=([1,3,5,7,9],[2,4,6,8,10]) | b=(25,30)
-- |     |
-- |     `- FalseP PCmp2 25 > 30
-- |
-- `- PPartition debugging info
--    |
--    +- FalseP i=0: PLift even | a=1
--    |
--    +- TrueP  i=1: PLift even | a=2
--    |
--    +- FalseP i=2: PLift even | a=3
--    |
--    +- TrueP  i=3: PLift even | a=4
--    |
--    +- FalseP i=4: PLift even | a=5
--    |
--    +- TrueP  i=5: PLift even | a=6
--    |
--    +- FalseP i=6: PLift even | a=7
--    |
--    +- TrueP  i=7: PLift even | a=8
--    |
--    +- FalseP i=8: PLift even | a=9
--    |
--    `- TrueP  i=9: PLift even | a=10
-- <BLANKLINE>
--
-- >>> let xs = [10,3,4,8,7,1,2,3,4,5,6,7,100,220,22]
-- >>> pe1' (_PPartition (pgt 7) $ _PBoth (_PLen (pgt 3)) (_PShow 1 * _PIx 4 0 (peq 999))) xs
-- <BLANKLINE>
-- FalseP PPartition | lefts=10 (1,3) | rights=5 (0,10)
-- |
-- `- FalseP PPartition Predicate
--    |
--    `- FalseP PBoth
--       |
--       +- TrueP  PLen 10 as=[3,4,7,1,2,3,4,5,6,7]
--       |  |
--       |  `- TrueP  10 > 3
--       |
--       `- FalseP PAnd
--          |
--          +- TrueP  PShow
--          |  |
--          |  +- TrueP  PConst a=[10,8,100,220,22]
--          |  |
--          |  `- ===== PShow =====
--          |     |
--          |     +- i=0 a=10
--          |     |
--          |     +- i=1 a=8
--          |     |
--          |     +- i=2 a=100
--          |     |
--          |     +- i=3 a=220
--          |     |
--          |     `- i=4 a=22
--          |
--          `- FalseP PIx 4 22
--             |
--             `- FalseP 22 == 999
-- <BLANKLINE>
--
-- >>> pe1' (_PPartition (pgt 7) 1) [10,3,4,8,7,1,2,3,4,5,6,7,100,220,22]
-- <BLANKLINE>
-- TrueP  PPartition | lefts=10 (1,3) | rights=5 (0,10)
-- |
-- `- TrueP  PPartition Predicate
--    |
--    `- TrueP  PConst a=([3,4,7,1,2,3,4,5,6,7],[10,8,100,220,22])
-- <BLANKLINE>
--
_PPartition :: (Foldable t, Show a) => Pred a -> Pred ([a],[a]) -> Pred (t a)
_PPartition (Pred x p) (Pred x1 pgb)  =
  Pred (Node nm [x,x1]) $
  \opts (toList -> as) ->
    let ts = zipWith (\i a -> ((i, a), p opts a)) [0::Int ..] as
    in case splitAndP opts [nm] ts of
         Left e -> e
         -- means there are no errors so we can filter
         -- we already have the index so dont add it again!
         Right z ->
              let ll = pgb opts $ (map (snd.fst) *** map (snd.fst)) z
              in partitionImpl2 opts nm ts z ll
    where nm = "PPartition"

-- | see 'Data.List.break'
--
-- >>> pe1' (pilist $ _PBreak (_PSnd (peq 'e')) 1) ['c'..'h']
-- <BLANKLINE>
-- TrueP  PBreak | lefts=2 | rights=4 pivot=(2,(2,'e'))
-- |
-- `- TrueP  PBreak Predicate
--    |
--    `- TrueP  PConst a=([(0,'c'),(1,'d')],[(2,'e'),(3,'f'),(4,'g'),(5,'h')])
-- <BLANKLINE>
--
-- >>> pe2' (_PBreak (pgt 4) (_PFn "x" (join (***) length) pgt2)) [-1..8]
-- <BLANKLINE>
-- TrueP  PBreak | lefts=6 | rights=4 pivot=(6,5)
-- |
-- +- TrueP  PBreak Predicate
-- |  |
-- |  `- TrueP  PFn x | a=([-1,0,1,2,3,4],[5,6,7,8]) | b=(6,4)
-- |     |
-- |     `- TrueP  PCmp2 6 > 4
-- |
-- `- PBreak debugging info
--    |
--    +- FalseP i=0: -1 > 4
--    |
--    +- FalseP i=1: 0 > 4
--    |
--    +- FalseP i=2: 1 > 4
--    |
--    +- FalseP i=3: 2 > 4
--    |
--    +- FalseP i=4: 3 > 4
--    |
--    +- FalseP i=5: 4 > 4
--    |
--    `- TrueP  i=6: 5 > 4
-- <BLANKLINE>
--
_PBreak :: (Foldable t, Show a) => Pred a -> Pred ([a],[a]) -> Pred (t a)
_PBreak (Pred x p) (Pred x1 p1) =
  Pred (Node nm [x,x1]) $
  \opts (toList -> as) ->
    -- only process as many as you need: so if we get an exception we stop!
    -- if we get a True then we stop
    -- this is unlike any of the other predicates
    let (ts,ts') = break (isn't _FalseP . view (_2 . boolP)) $ zipWith (\i a -> ((i, a), p opts a)) [0::Int ..] as
    in case splitAndP opts [nm] (ts <> take 1 ts') of
         Left e -> e
         Right (bads, _) ->
              let ll = p1 opts (take (length ts) as, drop (length ts) as)
              in breakImpl2 opts nm (ts<>take 1 ts') (bads, ts') ll
    where nm = "PBreak"

_PSpan :: (Foldable t, Show a) => Pred a -> Pred ([a],[a]) -> Pred (t a)
_PSpan (Pred x p) (Pred x1 p1) =
  Pred (Node nm [x,x1]) $
  \opts (toList -> as) ->
    -- only process as many as you need: so if we get an exception we stop!
    -- if we get a True then we stop
    -- this is unlike any of the other predicates
    let (ts,ts') = span (isn't _FalseP . view (_2 . boolP)) $ zipWith (\i a -> ((i, a), p opts a)) [0::Int ..] as
    in case splitAndP opts [nm] (ts <> take 1 ts') of
         Left e -> e
         Right (bads, _) ->
              let ll = p1 opts (take (length ts) as, drop (length ts) as)
              in breakImpl2 opts nm (ts<>take 1 ts') (bads, ts') ll
    where nm = "PSpan"

-- todo: need to show index where the break occurs!
-- | json visitor where you determine the targets
--
-- see 'matchArrays' 'matchIndex' 'matchNumber' etc
--
-- or 'PJsonKey' if matching on key
--
-- >>> pe1' (_PJson (matchStringP (sinfix "a")) $ psnds $ _PShow 1) json1
-- <BLANKLINE>
-- TrueP  PJson
-- |
-- +- TrueP  PShow
-- |  |
-- |  +- TrueP  PConst a=["markup","Standard Generalized Markup Language",...
-- |  |
-- |  `- ===== PShow =====
-- |     |
-- |     +- i=0 a="markup"
-- |     |
-- |     +- i=1 a="Standard Generalized Markup Language"
-- |     |
-- |     +- i=2 a="A meta-markup language, used to create markup languages such as DocBook."
-- |     |
-- |     `- i=3 a="example glossary"
-- |
-- `- Debugging jpaths
--    |
--    +- i=0 | [JPKey "glossary",JPKey "GlossDiv",JPKey "GlossList"...
--    |
--    +- i=1 | [JPKey "glossary",JPKey "GlossDiv",JPKey "GlossList"...
--    |
--    +- i=2 | [JPKey "glossary",JPKey "GlossDiv",JPKey "GlossList"...
--    |
--    `- i=3 | [JPKey "glossary",JPKey "title",JPValue (String "example glossary")]
-- <BLANKLINE>
--
_PJson :: Show a => ((NonEmpty JPath, Value) -> Maybe a) -> Pred [(NonEmpty JPath, a)] -> Pred Value
_PJson p (Pred qq q) =
  Pred (Node nm [qq])
  $ \opts v ->
          let xs = jvisitor p v -- es are any failures [TT] cos of a crap Pred for searching json!
            -- need to handle the zero case so the user has a clue: else just returns True
            -- then also need to make sure 'q' gets called
              ll = q opts xs
              msgs = nm : ["json search failed" | null xs]
              ns' = flip imap xs $ \i (jp,a) -> mkNodeDebug (TrueP, ["i=" <> show i, showA opts 1 "" (reverse $ toList jp), showA opts 2 "a=" a]) []
              ns = [ll,mkNodeDebug (TrueP, ["Debugging jpaths"]) ns']
          in case getBool ll of
                      FailP e -> mkNode (FailP e, msgs) ns
                      b -> mkNode (b, msgs) ns
  where nm = "PJson"

-- | matches on the key using the string predicate
--
-- >>> pe1' (_PJsonKey "abbrev" (-_PNull)) json1
-- <BLANKLINE>
-- TrueP  PJsonKey
-- |
-- +- TrueP  PNot
-- |  |
-- |  `- FalseP PNull length=1 as=[(JPKey "Abbrev" :| [JPKey "GlossEntry",JPKey "Gloss...
-- |
-- `- Debugging jpaths
--    |
--    `- i=0 | key=Abbrev | [JPKey "glossary",JPKey "GlossDiv",JPKey "GlossList",JPKey...
-- <BLANKLINE>
--
-- >>> let fn = _PSnd $ jarray 0 $ _PLinear Rigid [preq "c#",preq "haskell", preq "rust"]
-- >>> pe1' (_PJsonKey "langs" (_PLen (peq 1) * _PHead 0 fn * (psnds $ pone $ jarray 3 $ _PShow 1))) json0
-- <BLANKLINE>
-- FalseP PJsonKey
-- |
-- +- FalseP PAnd
-- |  |
-- |  +- FalseP PAnd
-- |  |  |
-- |  |  +- TrueP  PLen 1 as=[(JPKey "langs" :| [],Array [String "c#",String "rusxt",String "haskell"])]
-- |  |  |  |
-- |  |  |  `- TrueP  1 == 1
-- |  |  |
-- |  |  `- FalseP PHead (JPKey "langs" :| [],Array [String "c#",String "rusxt",String "haskell"])
-- |  |     |
-- |  |     `- FalseP PSnd a=Array [String "c#",String "rusxt",String "haskell"] fst=JPKey "langs" :| []
-- |  |        |
-- |  |        `- FalseP PPrism (Just) [jarray] [String "c#",String "rusxt",String "haskell"]
-- |  |           |
-- |  |           `- FalseP PLinear Failed Pred [Int] | errors(1): NoMatch 1
-- |  |              |
-- |  |              +- FalseP Predicates | PZipAnd | PZipExact | (bad,good)=(1,2)
-- |  |              |  |
-- |  |              |  `- FalseP PLift and | a=[True,True,False]
-- |  |              |     |
-- |  |              |     +- TrueP  i=0
-- |  |              |     |  |
-- |  |              |     |  +- TrueP  1 == 1
-- |  |              |     |  |
-- |  |              |     |  `- PStringCI a == String "c#"
-- |  |              |     |
-- |  |              |     +- TrueP  i=1
-- |  |              |     |  |
-- |  |              |     |  +- TrueP  1 == 1
-- |  |              |     |  |
-- |  |              |     |  `- PStringCI a == String "haskell"
-- |  |              |     |
-- |  |              |     `- FalseP i=2
-- |  |              |        |
-- |  |              |        +- FalseP 0 < 1 (Under)
-- |  |              |        |
-- |  |              |        `- PStringCI a == String "rust"
-- |  |              |
-- |  |              +- TrueP  PLinear | OneMatch 0 a=String "c#" cnt=1 (i=0, a=String "c#")
-- |  |              |  |
-- |  |              |  +- TrueP  i=0: PStringCI String "c#" == String "c#"
-- |  |              |  |
-- |  |              |  +- FalseP i=1: PStringCI String "c#" == String "haskell"
-- |  |              |  |
-- |  |              |  `- FalseP i=2: PStringCI String "c#" == String "rust"
-- |  |              |
-- |  |              +- FalseP PLinear NoMatch 1 a=String "rusxt"
-- |  |              |  |
-- |  |              |  +- FalseP i=0: PStringCI String "rusxt" == String "c#"
-- |  |              |  |
-- |  |              |  +- FalseP i=1: PStringCI String "rusxt" == String "haskell"
-- |  |              |  |
-- |  |              |  `- FalseP i=2: PStringCI String "rusxt" == String "rust"
-- |  |              |
-- |  |              `- TrueP  PLinear | OneMatch 2 a=String "haskell" cnt=1 (i=1, a=String "haskell")
-- |  |                 |
-- |  |                 +- FalseP i=0: PStringCI String "haskell" == String "c#"
-- |  |                 |
-- |  |                 +- TrueP  i=1: PStringCI String "haskell" == String "haskell"
-- |  |                 |
-- |  |                 `- FalseP i=2: PStringCI String "haskell" == String "rust"
-- |  |
-- |  `- TrueP  POne Array [String "c#",String "rusxt",String "haskell"]
-- |     |
-- |     `- TrueP  PPrism (Just) [jarray] [String "c#",String "rusxt",String "haskell"]
-- |        |
-- |        `- TrueP  PShow
-- |           |
-- |           +- TrueP  PConst a=[String "c#",String "rusxt",String "haskell"]
-- |           |
-- |           `- ===== PShow =====
-- |              |
-- |              +- i=0 a=String "c#"
-- |              |
-- |              +- i=1 a=String "rusxt"
-- |              |
-- |              `- i=2 a=String "haskell"
-- |
-- `- Debugging jpaths
--    |
--    `- i=0 | key=langs | [JPKey "langs"]
-- <BLANKLINE>
--
-- >>> let xx = jarray 0 $ _PLinear Rigid [preq "xml",preq "gml",preq "abc"]
-- >>> pe1' (_PJsonKey (sinfix "seealso") $ psnds $ _PHead 0 xx) json1
-- <BLANKLINE>
-- FalseP PJsonKey
-- |
-- +- FalseP PHead Array [String "GML",String "XML"]
-- |  |
-- |  `- FalseP PPrism (Just) [jarray] [String "GML",String "XML"]
-- |     |
-- |     `- FalseP PLinear Failed Pred [Int]
-- |        |
-- |        +- FalseP Predicates | PZipAnd | PZipExact | (bad,good)=(1,2)
-- |        |  |
-- |        |  `- FalseP PLift and | a=[True,True,False]
-- |        |     |
-- |        |     +- TrueP  i=0
-- |        |     |  |
-- |        |     |  +- TrueP  1 == 1
-- |        |     |  |
-- |        |     |  `- PStringCI a == String "xml"
-- |        |     |
-- |        |     +- TrueP  i=1
-- |        |     |  |
-- |        |     |  +- TrueP  1 == 1
-- |        |     |  |
-- |        |     |  `- PStringCI a == String "gml"
-- |        |     |
-- |        |     `- FalseP i=2
-- |        |        |
-- |        |        +- FalseP 0 < 1 (Under)
-- |        |        |
-- |        |        `- PStringCI a == String "abc"
-- |        |
-- |        +- TrueP  PLinear | OneMatch 0 a=String "GML" cnt=1 (i=1, a=String "GML")
-- |        |  |
-- |        |  +- FalseP i=0: PStringCI String "GML" == String "xml"
-- |        |  |
-- |        |  +- TrueP  i=1: PStringCI String "GML" == String "gml"
-- |        |  |
-- |        |  `- FalseP i=2: PStringCI String "GML" == String "abc"
-- |        |
-- |        `- TrueP  PLinear | OneMatch 1 a=String "XML" cnt=1 (i=0, a=String "XML")
-- |           |
-- |           +- TrueP  i=0: PStringCI String "XML" == String "xml"
-- |           |
-- |           +- FalseP i=1: PStringCI String "XML" == String "gml"
-- |           |
-- |           `- FalseP i=2: PStringCI String "XML" == String "abc"
-- |
-- `- Debugging jpaths
--    |
--    `- i=0 | key=GlossSeeAlso | [JPKey "glossary",JPKey "GlossDiv",JPKey "GlossList"...
-- <BLANKLINE>
--
_PJsonKey :: Pred String -> Pred [(NonEmpty JPath, Value)] -> Pred Value
_PJsonKey p (Pred qq q) =
  Pred (Node nm [_ppred p,qq])
  $ \opts v ->
          let xs = jvisitor (matchKeyP p) v
              ll = q opts (xs & traverse . _2 %~ snd)
              msgs = nm : ["json search failed" | null xs]
              ns' = flip imap xs $ \i (jp,(k,val)) -> mkNodeDebug (TrueP, ["i=" <> show i, "key=" <> k, showA opts 1 "" (reverse $ toList jp), showA opts 2 "value=" val]) []
              ns = [ll,mkNodeDebug (TrueP, ["Debugging jpaths"]) ns']
          in case getBool ll of
               FailP e -> mkNode (FailP e, msgs) ns
               b -> mkNode (b, msgs) ns
  where nm = "PJsonKey"

-- PJsonP creates a nested tree until it stops or is successful with 'Value' at then end
-- | given a json path will get the json value at that path
--
-- >>> pe1' (_PJsonP [JPIndex 2,JPKey "age",JPValue (Number 33),JPValue ""] 0 1) json2
-- <BLANKLINE>
-- FalseP PJsonP path=nth 2.key "age"._Number._String
-- |
-- +- FalseP no match on Number 33.0 /= Number 45.0 | matched up to=nth 2.key "age" | PConst a=()
-- |
-- `- nth 2 | value=Object (fromList [("lastName",String "Doe"),("age",Number 45.0),("firstName"...
--    |
--    `- key "age" | value=Number 45.0
--       |
--       `- match failed on _Number | Number 33.0 /= Number 45.0 | partial match=nth 2.key "age"
-- <BLANKLINE>
--
-- >>> let zzz = map JPKey ["glossary","GlossDiv","GlossList","GlossEntry","GlossDef","para"]
-- >>> pe' (_PJsonP zzz 0 $ _PString CI SInfix "docbook") json1
-- <BLANKLINE>
-- TrueP  PJsonP
-- |
-- +- TrueP  matched | PStringCI String "docbook" `isInfixOf` String "A meta-markup...
-- |
-- `- key "glossary"
--    |
--    `- key "GlossDiv"
--       |
--       `- key "GlossList"
--          |
--          `- key "GlossEntry"
--             |
--             `- key "GlossDef"
--                |
--                `- key "para"
--                   |
--                   `- TrueP  matched complete path
-- <BLANKLINE>
--
-- >>> let zzz = map JPKey ["glossary","GlossDiv","GlossList","GlossEntry","GlossTerm"]
-- >>> pe' (_PJsonP zzz 0 $ _PShow1 $ sinfix "marku" * ssuffix "uaxge") json1
-- <BLANKLINE>
-- FalseP PJsonP
-- |
-- +- FalseP matched | PShow1
-- |  |
-- |  +- FalseP PAnd
-- |  |  |
-- |  |  +- TrueP  PStringCI String "marku" `isInfixOf` String "Standard Generalized Markup Language"
-- |  |  |
-- |  |  `- FalseP PStringCI String "uaxge" `isSuffixOf` String "Standard Generalized Markup Language"
-- |  |
-- |  `- a=String "Standard Generalized Markup Language"
-- |
-- `- key "glossary"
--    |
--    `- key "GlossDiv"
--       |
--       `- key "GlossList"
--          |
--          `- key "GlossEntry"
--             |
--             `- key "GlossTerm"
--                |
--                `- TrueP  matched complete path
-- <BLANKLINE>
--
-- >>> pe' (_PJsonP [JPIndex 2] 0 $ jobjectList 0 $ _PShow 1) json2
-- <BLANKLINE>
-- TrueP  PJsonP
-- |
-- +- TrueP  matched | PPrism (Just) [jobjectList]
-- |  |
-- |  `- TrueP  PShow
-- |     |
-- |     +- TrueP
-- |     |
-- |     `- ===== PShow =====
-- |        |
-- |        +- i=0 a=("lastName",String "Doe")
-- |        |
-- |        +- i=1 a=("age",Number 45.0)
-- |        |
-- |        +- i=2 a=("firstName",String "John")
-- |        |
-- |        `- i=3 a=("likesPizza",Bool False)
-- |
-- `- nth 2
--    |
--    `- TrueP  matched complete path
-- <BLANKLINE>
--
_PJsonP :: [JPath] -> Pred () -> Pred Value -> Pred Value
_PJsonP jps (Pred px p) (Pred qq q) =
  Pred (Node (nm <> " path=" <> showJPaths jps) [px,qq])
  $ \opts v ->
          let (tt, mv, jps') = jpath [] opts jps v
              ll = case mv of
                     Left e -> addMessagesPre ["no match on " ++ e, showLit opts 1 "matched up to=" (showJPaths jps')] (p opts ())
                     Right v' -> addMessagePre "matched" (q opts v')
              -- need to handle the zero case so the user has a clue: else just returns True
              -- then also need to make sure 'q' gets called
              msgs = [nm <> showLit opts 1 " path=" (showJPaths jps)]
          in case getBool ll of
               FailP e -> mkNode (FailP e, msgs) [ll,tt]
               b -> mkNode (b, msgs) [ll,tt]
    where nm = "PJsonP"

-- | equivalent to take using 'PSplitAt' but using one side of the tuple
ptake, pdrop :: (Foldable t, Show a) => Int -> Pred [a] -> Pred (t a)
ptake i = _PMsg Inline "PTake" . _PSplitAt i . phide . _PFst
pdrop i = _PMsg Inline "PDrop" . _PSplitAt i . phide . _PSnd

-- not sure how useful this is? can use PIx to get at particular keyvalues or can just pilist to get it as a big list of tuples
-- | convert a predicate on a foldable to predicate on a map grouped by key
--
-- >>> pe2' (pgroup (between 3 7) $ _PIx GT 0 1) [11,5,2,4,12]
-- <BLANKLINE>
-- TrueP  PFn pgroup | a=[11,5,2,4,12] | b=fromList [(LT,[2]),(EQ,[5,4]),(GT,[11,12])]
-- |
-- `- TrueP  PIx GT [11,12]
--    |
--    `- TrueP  PConst a=[11,12]
-- <BLANKLINE>
--
-- >>> pe2' (pgroup (between 3 7) $ _PIx EQ 0 $ _PLen (peq 2)) [11,5,2,4,12,14,11,11,12]
-- <BLANKLINE>
-- TrueP  PFn pgroup | a=[11,5,2,4,12,14,11,11,12] | b=fromList [(LT,[2]),(EQ,[5,4]),(GT,[11,12,14,11,11,12])]
-- |
-- `- TrueP  PIx EQ [5,4]
--    |
--    `- TrueP  PLen 2 as=[5,4]
--       |
--       `- TrueP  2 == 2
-- <BLANKLINE>
--
-- >>> pe2' (pgroup (between 3 7) $ _PIx GT 0 $ _PLen (peq 2)) [11,5,2,4,12,14,11,11,12]
-- <BLANKLINE>
-- FalseP PFn pgroup | a=[11,5,2,4,12,14,11,11,12] | b=fromList [(LT,[2]),(EQ,[5,4])...
-- |
-- `- FalseP PIx GT [11,12,14,11,11,12]
--    |
--    `- FalseP PLen 6 as=[11,12,14,11,11,12]
--       |
--       `- FalseP 6 == 2
-- <BLANKLINE>
--
-- >>> pe2' (pgroup (compare 'd') (_PIx GT 0 (_PLen (peq 4)))) ("adcxdza"::String)
-- <BLANKLINE>
-- FalseP PFn pgroup | a="adcxdza" | b=fromList [(LT,"xz"),(EQ,"dd"),(GT,"aca")]
-- |
-- `- FalseP PIx GT "aca"
--    |
--    `- FalseP PLen 3 as="aca"
--       |
--       `- FalseP 3 == 4
-- <BLANKLINE>
--
-- >>> pe2' (pgroup (compare 'd') (_PIx EQ 0 (_PLen (peq 4)))) ("adcxdza"::String)
-- <BLANKLINE>
-- FalseP PFn pgroup | a="adcxdza" | b=fromList [(LT,"xz"),(EQ,"dd"),(GT,"aca")]
-- |
-- `- FalseP PIx EQ "dd"
--    |
--    `- FalseP PLen 2 as="dd"
--       |
--       `- FalseP 2 == 4
-- <BLANKLINE>
--
-- >>> pe2' (pgroup (compare 'd') (_PIx EQ 0 (_PLen (peq 2)))) ("adcxdza"::String)
-- <BLANKLINE>
-- TrueP  PFn pgroup | a="adcxdza" | b=fromList [(LT,"xz"),(EQ,"dd"),(GT,"aca")]
-- |
-- `- TrueP  PIx EQ "dd"
--    |
--    `- TrueP  PLen 2 as="dd"
--       |
--       `- TrueP  2 == 2
-- <BLANKLINE>
--
pgroup :: (Show (t a), Foldable t, Show k, Ord k, Show a) => (a -> k) -> Pred (Map k [a]) -> Pred (t a)
pgroup ak = _PFn "pgroup" (M.fromListWith (flip (<>)) . map (ak &&& (:[])) . toList)

pgroupBetween :: (Foldable t, Show a, Ord a, Show (t a)) => a -> a -> Pred (Map Ordering [a]) -> Pred (t a)
pgroupBetween a b = pgroup (between a b)

pgroupEq :: (Show (t a), Foldable t, Show k, Eq k, Hashable k, Show a) => (a -> k) -> Pred (HashMap k [a]) -> Pred (t a)
pgroupEq ak = _PFn "pgroupEq" (H.fromListWith (flip (<>)) . map (ak &&& (:[])) . toList)

-- this is useful can emulate POrder and more eg pgroupBy ((==) . succ) off by exactly one or pgroupBy (on (==) even odd) xor on evenness
-- | a better 'groupBy' that checks adjacent elements. good replacement and more powerful version of 'POrder'
--
-- >>> pe2' (pgroupBy (<=) $ _PLen $ plt 3) [1,4,5,7,11,3,4]
-- <BLANKLINE>
-- TrueP  PFn pgroupBy | a=[1,4,5,7,11,3,4] | b=[[1,4,5,7,11],[3,4]]
-- |
-- `- TrueP  PLen 2 as=[[1,4,5,7,11],[3,4]]
--    |
--    `- TrueP  2 < 3
-- <BLANKLINE>
--
-- >>> pe2' (pgroupBy (on (/=) even) 1) [1,4,5,10,11,9]
-- <BLANKLINE>
-- TrueP  PFn pgroupBy | a=[1,4,5,10,11,9] | b=[[1,4,5,10,11],[9]]
-- |
-- `- TrueP  PConst a=[[1,4,5,10,11],[9]]
-- <BLANKLINE>
--
-- >>> pe2' (pgroupBy ((((<=2) . abs) .) . subtract) 1) [1,4,5,7,11,9]
-- <BLANKLINE>
-- TrueP  PFn pgroupBy | a=[1,4,5,7,11,9] | b=[[1],[4,5,7],[11,9]]
-- |
-- `- TrueP  PConst a=[[1],[4,5,7],[11,9]]
-- <BLANKLINE>
--
-- >>> pe2' (pgroupBy (<) $ _PLen (pgt 2) * _PHead 0 (_PLen $ pgt 6)) [1,3,4,6,6,9,3,4]
-- <BLANKLINE>
-- FalseP PFn pgroupBy | a=[1,3,4,6,6,9,3,4] | b=[[1,3,4,6],[6,9],[3,4]]
-- |
-- `- FalseP PAnd
--    |
--    +- TrueP  PLen 3 as=[[1,3,4,6],[6,9],[3,4]]
--    |  |
--    |  `- TrueP  3 > 2
--    |
--    `- FalseP PHead [1,3,4,6]
--       |
--       `- FalseP PLen 4 as=[1,3,4,6]
--          |
--          `- FalseP 4 > 6
-- <BLANKLINE>
--
-- >>> pe1' (pgroupBy (<=) 1) ([1..10] ++ [1..4] ++ [1..6])
-- <BLANKLINE>
-- TrueP  PFn pgroupBy | a=[1,2,3,4,5,6,7,8,9,10,1,2,3,4,1,2,3,4,5,6] | b=[[1,2,3,4,5,6,7,8,9,10],[1,2,3,4],[1,2,3,4,5,6]]
-- |
-- `- TrueP  PConst a=[[1,2,3,4,5,6,7,8,9,10],[1,2,3,4],[1,2,3,4,5,6]]
-- <BLANKLINE>
--
pgroupBy :: (Show (t a), Foldable t, Show a) => (a -> a -> Bool) -> Pred [[a]] -> Pred (t a)
pgroupBy f = _PFn "pgroupBy" (groupBy' f . toList)

porder :: (Foldable t, Show (t a), Show a) => (a -> a -> Bool) -> Pred (t a)
porder cmp = pgroupBy cmp $ _POne 0 0 1

pilist :: (FoldableWithIndex i f, Show (f a), Show a, Show i) => Pred [(i, a)] -> Pred (f a)
pilist = phide . _PFn "itoList" itoList

-- | roughly equivalent to 'divide' in 'Divisible'
--
-- >>> pe2' (pdivide id (_PLen (pgt 4)) (pgt 10)) (['a'..'h'],9)
-- <BLANKLINE>
-- FalseP PFn divide | a=("abcdefgh",9) | b=("abcdefgh",9)
-- |
-- `- FalseP PBoth
--    |
--    +- TrueP  PLen 8 as="abcdefgh"
--    |  |
--    |  `- TrueP  8 > 4
--    |
--    `- FalseP 9 > 10
-- <BLANKLINE>
--
pdivide :: (Show b, Show c, Show a) => (a -> (b, c)) -> Pred b -> Pred c -> Pred a
pdivide abc pb pc = _PFn "divide" abc (_PBoth pb pc)


-- | roughly equivalent to 'choose' in 'Decidable'
--
-- >>> pe2' (pchoose id (_PLen (pgt 4)) (pgt 10)) (Left ['a'..'h'])
-- <BLANKLINE>
-- TrueP  PFn choose | a=Left "abcdefgh" | b=Left "abcdefgh"
-- |
-- `- TrueP  PEither (Left) "abcdefgh"
--    |
--    `- TrueP  PLen 8 as="abcdefgh"
--       |
--       `- TrueP  8 > 4
-- <BLANKLINE>
--
-- >>> pe2' (pchoose id (_PLen (pgt 4)) (pgt 10)) (Right 9)
-- <BLANKLINE>
-- FalseP PFn choose | a=Right 9 | b=Right 9
-- |
-- `- FalseP PEither (Right) 9
--    |
--    `- FalseP 9 > 10
-- <BLANKLINE>
--
pchoose :: (Show b, Show c, Show a) => (a -> Either b c) -> Pred b -> Pred c -> Pred a
pchoose abc pb pc = _PFn "choose" abc (_PEither pb pc)

-- | unzip a list
--
-- >>> pe1' (_PJsonKey "aGE" $ punzip (pfn (map showJPathsNE) $ _PShowS 1) (jnumbers' $ _PShow 1)) json2
-- <BLANKLINE>
-- TrueP  PJsonKey
-- |
-- +- TrueP  PFn punzip | a=[(JPKey "age" :| [JPIndex 0],Number 24.0),(JPKey "age" :| [JPIndex 1],Number 39.0),(JPKey "age" :| [JPIndex 2],Number 45 ... | b=([JPKey "age" :| [JPIndex 0],JPKey "age" :| [JPIndex 1],JPKey "age" :| [JPIndex 2],JPKey "age" :| [JPIndex 3]],[Number 2 ...
-- |  |
-- |  `- TrueP  PBoth
-- |     |
-- |     +- TrueP  PFn | a=[JPKey "age" :| [JPIndex 0],JPKey "age" :| [JPIndex 1],JPKey "age" :| [JPIndex 2],JPKey "age" :| [JPIndex 3]] | b=["nth 0.key \"age\"","nth 1.key \"age\"","nth 2.key \"age\"","nth 3.key \"age\""]
-- |     |  |
-- |     |  `- TrueP  PShowS
-- |     |     |
-- |     |     +- TrueP  PConst a=["nth 0.key \"age\"","nth 1.key \"age\"","nth 2.key \"age\"","nth 3.key \"age\""]
-- |     |     |
-- |     |     `- ===== PShowS =====
-- |     |        |
-- |     |        +- i=0 a=nth 0.key "age"
-- |     |        |
-- |     |        +- i=1 a=nth 1.key "age"
-- |     |        |
-- |     |        +- i=2 a=nth 2.key "age"
-- |     |        |
-- |     |        `- i=3 a=nth 3.key "age"
-- |     |
-- |     `- TrueP  PMorph bad=[] good=[24.0,39.0,45.0,27.0]
-- |        |
-- |        `- TrueP  PBoth
-- |           |
-- |           +- TrueP  PNull length=0 as=[]
-- |           |
-- |           `- TrueP  PShow
-- |              |
-- |              +- TrueP  PConst a=[24.0,39.0,45.0,27.0]
-- |              |
-- |              `- ===== PShow =====
-- |                 |
-- |                 +- i=0 a=24.0
-- |                 |
-- |                 +- i=1 a=39.0
-- |                 |
-- |                 +- i=2 a=45.0
-- |                 |
-- |                 `- i=3 a=27.0
-- |
-- `- Debugging jpaths
--    |
--    +- i=0 | key=age | [JPIndex 0,JPKey "age"]
--    |
--    +- i=1 | key=age | [JPIndex 1,JPKey "age"]
--    |
--    +- i=2 | key=age | [JPIndex 2,JPKey "age"]
--    |
--    `- i=3 | key=age | [JPIndex 3,JPKey "age"]
-- <BLANKLINE>
--
punzip :: (Foldable t, Show (t (a, b)), Show a, Show b) => Pred [a] -> Pred [b] -> Pred (t (a, b))
punzip = (_PFn "punzip" (unzip . toList) .) . _PBoth

-- these are contravariant sort of curry uncurry
puncurry :: (Show c, Show a, Show b) => (a -> b -> c) -> Pred c -> Pred (a, b)
puncurry = _PFn "uncurry" . uncurry

-- just locks down the signature is all
pcurry :: (Show a, Show b, Show c) => (c -> (a, b)) -> Pred (a, b) -> Pred c
pcurry = _PFn "curry"

-- curry . uncurry but has tracing
-- | adds tracing to 'curry' . 'uncurry'
--
-- >>> pe' (pcu (fst &&& fst.snd) (-) (pgt 3)) (7,(12,'x'))
-- <BLANKLINE>
-- FalseP PFn uncurry | a=(7,12) | b=-5
-- |
-- `- FalseP -5 > 3
-- <BLANKLINE>
--
pcu :: (Show a, Show b, Show y, Show x) => (x -> (a, b)) -> (a -> b -> y) -> Pred y -> Pred x
pcu f g = phide . pcurry f . puncurry g

-- | adds tracing to composed functions
--
-- >>> pe' (pcomp (first fst) (uncurry (-)) (pgt 3)) ((12,'x'),7)
-- <BLANKLINE>
-- TrueP  PFn PComp a->x | a=((12,'x'),7) | b=(12,7)
-- |
-- `- TrueP  PFn PComp x->b | a=(12,7) | b=5
--    |
--    `- TrueP  5 > 3
-- <BLANKLINE>
--
pcomp :: (Show x, Show b, Show a) => (a -> x) -> (x -> b) -> Pred b -> Pred a
pcomp ax xb = _PFn "PComp a->x" ax . _PFn "PComp x->b" xb

pid :: Pred Bool
pid = _PLift "id" id

-- | infix match on a list
--
-- >>> pe2' (minfix "abc") "<<<abc>>>"
-- <BLANKLINE>
-- TrueP  PMatch "abc" `isInfixOf` "<<<abc>>>"
-- <BLANKLINE>
--
minfix, mprefix, msuffix :: (Show a, Eq a) => [a] -> Pred [a]
minfix = _PMatch SInfix
mprefix = _PMatch SPrefix
msuffix = _PMatch SSuffix

sinfix, sprefix, ssuffix, sci, scs :: SConv s => s -> Pred s
sinfix = _PString CI SInfix
sprefix = _PString CI SPrefix
ssuffix = _PString CI SSuffix
sci = _PString CI SNone
scs = _PString CS SNone

pfanin :: (Show b, Show c, Show d) => String -> (b -> d) -> (c -> d) -> Pred d -> Pred (Either b c)
pfanin s f g = _PFn ("(|||)" `stringAp` s) (either f g)

(|||!) :: (Show b, Show c, Show d) => (b -> d) -> (c -> d) -> Pred d -> Pred (Either b c)
(|||!) = pfanin ""

pplus :: (Show b', Show c', Show b, Show c) => String -> (b -> b') -> (c -> c') -> Pred (Either b' c') -> Pred (Either b c)
pplus s f g = _PFn ("(+++)" `stringAp` s) (f +++ g)

(+++!) :: (Show b', Show c', Show b, Show c) => (b -> b') -> (c -> c') -> Pred (Either b' c') -> Pred (Either b c)
(+++!) = pplus ""

pfn :: (Show a, Show b) => (a -> b) -> Pred b -> Pred a
pfn = _PFn ""

p_1 :: (Field1 s s b b, Show b, Show s) => Pred b -> Pred s
p_1 = _PFn "_1" (view _1)

p_2 :: (Field2 s s b b, Show b, Show s) => Pred b -> Pred s
p_2 = _PFn "_2" (view _2)

p_3 :: (Field3 s s b b, Show b, Show s) => Pred b -> Pred s
p_3 = _PFn "_3" (view _3)

p_4 :: (Field4 s s b b, Show b, Show s) => Pred b -> Pred s
p_4 = _PFn "_4" (view _4)

phide :: Pred a -> Pred a
phide = _PChangeOpts (\o -> o { oHide = max 2 (oHide o + 2) })

plift :: Show a => (a -> Bool) -> Pred a
plift = _PLift ""

picmp :: (Show i, Show a) => (i -> a -> Bool) -> Pred (i, a)
picmp = _PLift "picmp" . uncurry

peven, podd :: (Show a, Integral a) => Pred a
peven = _PLift "even" even
podd = _PLift "odd" odd

pfind :: (Foldable t, Show a) => Pred a -> Pred () -> Pred a -> Pred (t a)
pfind p e = _PPartition p . _PSnd . _PHead e

pfilter :: (Show a, Foldable t) => Pred a -> Pred [a] -> Pred (t a)
pfilter p = _PPartition p . phide . _PSnd

pspan :: (Foldable t, Show a) => Pred a -> Pred ([a],[a]) -> Pred (t a)
pspan p = _PBreak (-p)

pspan2 :: (Foldable t, Show a) => Pred a -> Pred [a] -> Pred [a] -> Pred (t a)
pspan2 p p0 p1 = _PBreak (-p) (_PBoth (_PMsg Inline "Left Predicate" p0) (_PMsg Inline "Right Predicate" p1))

-- old school way where we split out the predicates for left and right instead of tupling
-- easier to work with but we have to introduce PBoth=AND
-- also not as flexible cos cannot compare results of left and right cos independent
pbreak2 :: (Foldable t, Show a) => Pred a -> Pred [a] -> Pred [a] -> Pred (t a)
pbreak2 p p0 p1 = _PBreak p (_PBoth (_PMsg Inline "Left Predicate" p0) (_PMsg Inline "Right Predicate" p1))

ppartition2 :: (Foldable t, Show a) => Pred a -> Pred [a] -> Pred [a] -> Pred (t a)
ppartition2 p p0 p1 = _PPartition p (_PBoth (_PMsg Inline "Left Predicate" p0) (_PMsg Inline "Right Predicate" p1))

-- these are trivial using _PFn/PFn but does give documentation using String instead of a mysterious PFn
-- also cos I use them a lot
pstar :: (Show b, Show b', Show c', Show c) => String -> (b -> c) -> (b' -> c') -> Pred (c, c') -> Pred (b, b')
pstar s f g = _PFn ("(***)" `stringAp` s) (f *** g)

(***!) :: (Show b, Show b', Show c', Show c) => (b -> c) -> (b' -> c') -> Pred (c, c') -> Pred (b, b')
(***!) = pstar ""

pfanout, pamp :: (Show b, Show c', Show c) => String -> (b -> c) -> (b -> c') -> Pred (c, c') -> Pred b
pfanout s f g = _PFn ("(&&&)" `stringAp` s) (f &&& g)
pamp = pfanout

(&&&!) :: (Show b,Show c', Show c) => (b -> c) -> (b -> c') -> Pred (c, c') -> Pred b
(&&&!) = pfanout ""

pstar2 :: (Show a,Show b) => String -> (a -> b) -> Pred (b, b) -> Pred (a, a)
pstar2 s  = join (pstar s)

pzipand :: (Foldable t, Show a) => [Pred a] -> Pred (t a)
pzipand ps = _PMsg Inline "PZipAnd" $ _PZipExact ps 0 (_PLift "and" and)

pzipor :: (Foldable t, Show a) => [Pred a] -> Pred (t a)
pzipor ps = _PMsg Inline "PZipOr" $ _PZipExact ps 0 (_PLift "or" or)

pands :: Show a => [Pred a] -> Pred a
pands ps = _PMsg Inline "PAnds" $ _POps ps (_PLift "and" and)

pors :: Show a => [Pred a] -> Pred a
pors ps = _PMsg Inline "POrs" $ _POps ps (_PLift "or" or)


-- way cool:
-- | generalises PForAll and PExists
--
-- >>> pe2' (pquantifier (_PRange 4 7) 1) [1..10]
-- <BLANKLINE>
-- TrueP  PPartition | lefts=6 (0,1) | rights=4 (3,4)
-- |
-- +- TrueP  PPartition Predicate
-- |  |
-- |  `- TrueP  PFn (***) length | a=([1,2,3,8,9,10],[4,5,6,7]) | b=(6,4)
-- |     |
-- |     `- TrueP  PConst a=(6,4)
-- |
-- `- PPartition debugging info
--    |
--    +- FalseP i=0: 1 < 4 (Under)
--    |
--    +- FalseP i=1: 2 < 4 (Under)
--    |
--    +- FalseP i=2: 3 < 4 (Under)
--    |
--    +- TrueP  i=3: 4 == [4..7]
--    |
--    +- TrueP  i=4: 5 == [4..7]
--    |
--    +- TrueP  i=5: 6 == [4..7]
--    |
--    +- TrueP  i=6: 7 == [4..7]
--    |
--    +- FalseP i=7: 8 > 7 (Over)
--    |
--    +- FalseP i=8: 9 > 7 (Over)
--    |
--    `- FalseP i=9: 10 > 7 (Over)
-- <BLANKLINE>
--
-- >>> pe1' (pquantifier (peven * pgt 5) (puncurry (-) (pgt 2))) [1..10]
-- <BLANKLINE>
-- TrueP  PPartition | lefts=7 (0,1) | rights=3 (5,6)
-- |
-- `- TrueP  PPartition Predicate
--    |
--    `- TrueP  PFn (***) length | a=([1,2,3,4,5,7,9],[6,8,10]) | b=(7,3)
--       |
--       `- TrueP  PFn uncurry | a=(7,3) | b=4
--          |
--          `- TrueP  4 > 2
-- <BLANKLINE>
--
pquantifier :: (Show a, Foldable t) => Pred a -> Pred (Int, Int) -> Pred (t a)
pquantifier p p12 = _PPartition p (pstar2 "length" length p12)

-- all vs at least one: so we have flexibility to make sure that at least 1/2 are valid
pforall, pforall' :: (Foldable t, Show a) => Pred a -> Pred (t a)
pforall = flip pquantifier (_PFst (peq 0))
pforall' = flip _PPartition (_PFst _PNull)

pexists, pexists' :: (Foldable t, Show a) => Pred a -> Pred (t a)
pexists = flip pquantifier (_PSnd (pgt 0))
pexists' = flip _PPartition (_PSnd (-_PNull))

-- | like 'Data.Function.on' for predicates
plift2 :: (Show a, Show b, Show b', Show a') => (a -> a') -> (b -> b') -> (a' -> b' -> Bool) -> Pred (a, b)
plift2 f g = pstar "plift2" f g . _PLift "uncurry" . uncurry

-- | like 'Data.Function.on' for predicates but uses the same function for both sides
pliftBi :: (Show a, Show a') => (a -> a') -> (a' -> a' -> Bool) -> Pred (a, a)
pliftBi f = pstar2 "pliftBi" f . _PLift "uncurry" . uncurry

pfsts :: (Functor f, Show (f a), Show (f (a, b))) => Pred (f a) -> Pred (f (a, b))
pfsts = phide . _PFn "fsts" (fmap fst)

psnds :: (Functor f, Show (f b), Show (f (a, b))) => Pred (f b) -> Pred (f (a, b))
psnds = phide . _PFn "snds" (fmap snd)

psnds2 :: (Functor f2, Functor f1, Show (f2 b2), Show (f1 b1), Show (f1 (a1, b1)), Show (f2 (a2, b2))) =>
     Pred (f1 b1, f2 b2) -> Pred (f1 (a1, b1), f2 (a2, b2))
psnds2 = phide . _PFn "snds2" (fmap snd *** fmap snd)

pcatch :: Pred a -> Pred a -> Pred a
pcatch e = _PMsg Inline "PCatch" . _PIf (Just e) Nothing Nothing

pordie :: Show a => String -> Pred a -> Pred a
pordie s = _PMsg Inline "POrDie" . _PIf Nothing (Just (pfail s)) Nothing

pwhen, punless :: Pred a -> Pred a -> Pred a
pwhen = _PIf Nothing Nothing . Just
punless p = _PIf Nothing (Just p) Nothing

-- works on a tuple: runs a maybe on each side then one of 4 predicates depending on the Nothing Just combinations
pprismLR, pprismLR' :: (Show a, Show a', Show b, Show b') =>
     String
  -> (a -> Maybe b)
  -> (a' -> Maybe b')
  -> Pred () -- when both sides are nothing
  -> Pred b
  -> Pred b'
  -> Pred (b, b') -- both match -- use this for comparing: eg PCmp2 or PEq2 or just plain PFn uncurry
  -> Pred (a, a')
pprismLR s f g p0 p1 p2 p3 = _PFn ("pprismLR " <> s) (\(a, a') -> case (f a, g a') of
                               (Nothing,Nothing) -> Left (Left ())
                               (Just b,Nothing)  -> Left (Right b)
                               (Nothing,Just b') -> Right (Left b')
                               (Just b,Just b')  -> Right (Right (b, b'))) (_PEither (_PEither p0 p1) (_PEither p2 p3))

-- use These cos more natural then is Maybe These as opposed to Either Either Either
pprismLR' s f g p0 p1 p2 p3 = _PFn ("pprismLR " <> s) (\(a, a') -> case (f a, g a') of
                               (Nothing,Nothing) -> Nothing
                               (Just b,Nothing)  -> Just $ This b
                               (Nothing,Just b') -> Just $ That b'
                               (Just b,Just b')  -> Just $ These b b') (_PMaybe p0 (_PThese p1 p2 p3))

pprismLR'' :: (Show a, Show a', Show b, Show b') =>
     String
  -> (a -> Maybe b)
  -> (a' -> Maybe b')
  -> Pred () -- when both sides are nothing
  -> Pred (These b b')
  -> Pred (a, a')
pprismLR'' s f g p0 p1 = _PFn ("pprismLR'' " <> s) (\(a, a') -> case (f a, g a') of
                               (Nothing,Nothing) -> Nothing
                               (Just b,Nothing)  -> Just $ This b
                               (Nothing,Just b') -> Just $ That b'
                               (Just b,Just b')  -> Just $ These b b') (_PMaybe p0 p1)

pprismL :: (Show a, Show x, Show b) =>
     String
  -> (a -> Maybe b)  -- match lhs of tuple
  -> Pred x        -- if no match ie Nothing then do this
  -> Pred (b, x)    -- else result of applying lhs
  -> Pred (a, x)
pprismL s f p q = _PFn ("PPrismL " <> s) (\(a, x) -> maybe (Left x) (Right . (,x)) (f a)) (_PEither p q)

pprismR :: (Show a, Show x, Show b) => String -> (a -> Maybe b) -> Pred x -> Pred (x, b) -> Pred (x, a)
pprismR s f p q = _PFn ("PPrismR " <> s) (\(x, a) -> maybe (Left x) (Right . (x,)) (f a)) (_PEither p q)

-- same but for Either instead of Maybe
pprismLEither :: (Show a, Show c, Show x, Show b) =>
     (a -> Either b c) -> Pred (b, x) -> Pred (c, x) -> Pred (a, x)
pprismLEither f p q = _PFn "pprismle" (\(a, x) -> either (Left . (,x)) (Right . (,x)) (f a)) (_PEither p q)

pprismREither :: (Show a, Show c, Show x, Show b) =>
     (a -> Either b c) -> Pred (x, b) -> Pred (x, c) -> Pred (x, a)
pprismREither f p q = _PFn "pprismre" (\(x, a) -> either (Left . (x,)) (Right . (x,)) (f a)) (_PEither p q)

-- | most common version of 'PPrism'
--
-- >>> pe1' (pprism0 (^? key "glossary" . key "GlossDiv" . key "title" . _String) "s") json1
-- <BLANKLINE>
-- TrueP  PPrism (Just) [] "S"
-- |
-- `- TrueP  PStringCI "S" == "s"
-- <BLANKLINE>
--
-- >>> let zzz = _PLinear Rigid [preq (pprism0 (^? _Bool) 1), preq (pprism0 (^? _Number) 1)]
-- >>> pe2' (pprism0 (^? _Array) zzz) "[1,true]"
-- <BLANKLINE>
-- TrueP  PPrism (Just) [] [Number 1.0,Bool True]
-- |
-- `- TrueP  PLinear | debug=[OneMatch 0,OneMatch 1] match=[(0,[1]),(1,[0])]
--    |
--    +- TrueP  Predicates | PZipAnd | PZipExact | as=[1,1] | (bad,good)=(0,2)
--    |  |
--    |  `- TrueP  PLift and | a=[True,True]
--    |     |
--    |     +- TrueP  i=0
--    |     |  |
--    |     |  +- TrueP  1 == 1
--    |     |  |
--    |     |  `- PPrism
--    |     |     |
--    |     |     +- PConst FalseP
--    |     |     |
--    |     |     `- PConst TrueP
--    |     |
--    |     `- TrueP  i=1
--    |        |
--    |        +- TrueP  1 == 1
--    |        |
--    |        `- PPrism
--    |           |
--    |           +- PConst FalseP
--    |           |
--    |           `- PConst TrueP
--    |
--    +- TrueP  PLinear | OneMatch 0 a=Number 1.0 cnt=1 (i=1, a=Number 1.0)
--    |  |
--    |  +- FalseP i=0: PPrism (Nothing) [] | PConst a=()
--    |  |
--    |  `- TrueP  i=1: PPrism (Just) [] 1.0
--    |     |
--    |     `- TrueP  PConst a=1.0
--    |
--    `- TrueP  PLinear | OneMatch 1 a=Bool True cnt=1 (i=0, a=Bool True)
--       |
--       +- TrueP  i=0: PPrism (Just) [] True
--       |  |
--       |  `- TrueP  PConst a=True
--       |
--       `- FalseP i=1: PPrism (Nothing) [] | PConst a=()
-- <BLANKLINE>
--
pprism0, pprism1 :: (Show b) => (a -> Maybe b) -> Pred b -> Pred a
pprism0 f = _PPrism "" f 0
pprism1 f = _PPrism "" f 1

pprism2 :: (Show b) => String -> String -> (a -> Maybe b) -> Pred b -> Pred a
pprism2 s e f = _PPrism s f (pfail e)

pprism' :: (Show a, Show b, Show c) => String -> (a -> Either b c) -> Pred b -> Pred c -> Pred a
pprism' s g = (_PFn s g .) . _PEither

preq, popt, pnever :: Pred a -> (Pred Int, Pred a)
preq = (preq',)
popt = (popt',)
pnever = (pnever',)

pij :: Int -> Int -> Pred a -> (Pred Int, Pred a)
pij = ((,) .) . _PRange

(..!) :: (Show a, Ord a) => a -> a -> Pred a
(..!) = _PRange

preq', popt', pnever' :: Pred Int
preq' = _PRange 1 1
popt' = _PRange 0 1
pnever' = _PRange 0 0

pmsgIfNotTrue :: String -> Pred a -> Pred a
pmsgIfNotTrue = pmsgIf (isn't _TrueP)

pmsgIfNotTrue' :: String -> Pred a -> Pred a
pmsgIfNotTrue' s p =
  let m = Just (_PMsg Inline s p)
  in _PIf m m Nothing p

pmsgIf :: (BoolP -> Bool) -> String -> Pred a -> Pred a
pmsgIf f msg = _PTree go
  where go tt | f (tt ^. boolP) = addMessagePre msg tt
              | otherwise = tt

-- | false and true predicates
pfalse, ptrue :: Show a => Pred a
pfalse = _PConst $ mkBool FalseP []
ptrue = _PConst $ mkBool TrueP []

-- | false and true predicates with a string message
pfalse', ptrue' :: Show a => String -> Pred a
pfalse' = _PConst . mkBool FalseP . (:[])
ptrue' = _PConst . mkBool TrueP . (:[])

-- | fail predicate with an exception and a message
pfail :: Show a => String -> Pred a
pfail = _PConst . mkfail

-- | most common use of 'POne' is to fail if empty or if too many elements
--
-- >>> pe1' (pone $ pgt 4) []
-- <BLANKLINE>
-- FalseP POne empty! | PConst a=()
-- <BLANKLINE>
--
-- >>> pe1' (pone $ pgt 4) [10]
-- <BLANKLINE>
-- TrueP  POne 10
-- |
-- `- TrueP  10 > 4
-- <BLANKLINE>
--
-- >>> pe1' (pone $ pgt 4) [10,11,12]
-- <BLANKLINE>
-- FalseP POne extra values! a=10 s'=[11,12]
-- |
-- `- FalseP PConst a=(10,[11,12])
-- <BLANKLINE>
--
pone :: (AsEmpty s, Cons s s a a, Show a, Show s) => Pred a -> Pred s
pone = _POne 0 0

-- | most common use of 'POneT' is to fail if empty or if too many elements
poneT :: (Foldable t, Show a) => Pred a -> Pred (t a)
poneT = _POneT 0 0

-- | POneT in terms of POne but POneT has equality
poneT' :: (Foldable t, Show a, Show (t a)) => Pred () -> Pred (a, [a]) -> Pred a -> Pred (t a)
poneT' p q = phide . pfn toList . _POne p q

-- | 'POne' in terms of 'PUncons'
pone' :: (AsEmpty s, Cons s s a a, Show a, Show s) => Pred () -> Pred (a,s) -> Pred a -> Pred s
pone' e e1 p = _PUncons e $ _PIf Nothing (Just e1) (Just (_PFst p)) (_PSnd _PEmpty)

-- | lifts 'maybeToEither' over a functor see 'PMorph' for Foldable but you lose ordering
pmaybeF :: (Show (f (Either a b)), Show (f a), Functor f) => (a -> Maybe b) -> Pred (f (Either a b)) -> Pred (f a)
pmaybeF = _PFn "pmaybeF" . fmap . maybeToEither

-- | lifts 'maybeToEither' over a foldable see 'PMorph' but does not retain ordering
pmaybeT :: (Show a, Show b, Show (t a), Foldable t) => (a -> Maybe b) -> Pred [Either a b] -> Pred (t a)
pmaybeT f = _PFn "pmaybeT" (map (maybeToEither f) . toList)

-- | lifts 'maybeToEither' over a []. emulates 'PMorph' but not as good messages
-- Examples:
--
-- >>> pe1' (pmorph (^? ix 3 . to show) 1) [[1,2,3,4],[10..11],[],[19..30],[]]
-- <BLANKLINE>
-- TrueP  PFn pmorph | a=[[1,2,3,4],[10,11],[],[19,20,21,22,23,24,25,26,27,28,29,30],[]] | b=([[10,11],[],[]],["4","22"])
-- |
-- `- TrueP  PConst a=([[10,11],[],[]],["4","22"])
-- <BLANKLINE>
--
pmorph :: (Foldable t, Show (t a), Show a, Show b) =>
     (a -> Maybe b) -> Pred ([a], [b]) -> Pred (t a)
pmorph f = _PFn "pmorph" (partitionEithers . map (maybeToEither f) . toList)

-- | generic version of 'PHead' using 'PUncons' and 'Cons' class instead of []
phead :: (Cons s s a a, Show a, Show s) => Pred () -> Pred a -> Pred s
phead e = _PMsg Inline "phead" . _PUncons e . phide . _PFst

--plast :: (Snoc s s a a, Show a, Show s) => Pred () -> Pred a -> Pred s
--plast e = PPrism "plast" (^? _last) (pmsgIfNotTrue "empty" e)

-- | generic version of 'PLast' using 'PUnsnoc' and 'Snoc' class
plast :: (Snoc s s a a, Show a, Show s) => Pred () -> Pred a -> Pred s
plast e = _PMsg Inline "plast" . _PUnsnoc e . phide . _PSnd

lpredE :: String -> Pred a -> Pred a
lpredE = _PTree . flip addError

rpred :: String -> Pred a -> Pred a
rpred = _PTree . addMessagePre

rpred1 :: (BoolP -> BoolP) -> Pred a -> Pred a
--rpred1 f = PTree (\t -> t & boolP %~ f)
rpred1 = _PTree . over boolP

plt, ple, pge, pgt :: (Show a, Ord a) => a -> Pred a
plt = _PCmp Lt
ple = _PCmp Le
pge = _PCmp Ge
pgt = _PCmp Gt

peq, pne :: (Show a, Eq a) => a -> Pred a
peq = _PEq True
pne = _PEq False


-- | predicates for comparing values in a tuple
--
-- >>> pe' peq2 (14,4)
-- <BLANKLINE>
-- FalseP PEq2 14 == 4
-- <BLANKLINE>
--
-- >>> pe' plt2 (14,4)
-- <BLANKLINE>
-- FalseP PCmp2 14 < 4
-- <BLANKLINE>
--
-- >>> pe' pge2 (14,4)
-- <BLANKLINE>
-- TrueP  PCmp2 14 >= 4
-- <BLANKLINE>
--
plt2, ple2, pge2, pgt2 :: (Show a, Ord a) => Pred (a, a)
plt2 = _PCmp2 Lt
ple2 = _PCmp2 Le
pge2 = _PCmp2 Ge
pgt2 = _PCmp2 Gt

peq2, pne2 :: (Show a, Eq a) => Pred (a, a)
peq2 = _PEq2 True
pne2 = _PEq2 False

pnum, palpha, palphaNum :: Pred Char
pnum = _PRange '0' '9'
palpha = _PLift "palpha" isAlpha
palphaNum = _PLift "palphaNum" isAlphaNum

pdist :: SConv s => Int -> Dist s -> [(Pred Int, Pred s)]
pdist mx (Dist p cs s) =
     [(p, _PString cs SNone s)]
  <> [(_PRange 0 0, _PDist CI s (_PRange 1 mx)) | mx >= 1] -- dont use if with <> cos will grab the next value in the else!
  <> case cs of
       CI -> []
       CS -> [(_PRange 0 0, sci s * (-scs s))] -- tricky: if matches ci but isnt the same as cs

pdists :: SConv s => Int -> [Dist s] -> [(Pred Int, Pred s)]
pdists mx ps = concat $ ps <&> pdist mx

-- | only Loose makes sense with Dist cos Rigid will find all errors just using plain PLinear!
--
-- >>> pe1' (plinearDist 2 [dopt "idris"]) ["idirs","haskell"]
-- <BLANKLINE>
-- FalseP PLinear Failed Pred [Int]
-- |
-- +- FalseP Predicates | PZipAnd | PZipExact | (bad,good)=(1,2)
-- |  |
-- |  `- FalseP PLift and | a=[True,False,True]
-- |     |
-- |     +- TrueP  i=0
-- |     |  |
-- |     |  +- TrueP  0 == [0..1]
-- |     |  |
-- |     |  `- PStringCS a == "idris"
-- |     |
-- |     +- FalseP i=1
-- |     |  |
-- |     |  +- FalseP 1 > 0 (Over)
-- |     |  |
-- |     |  `- PDistCI "idris"
-- |     |     |
-- |     |     `- a `elem` [1..2]
-- |     |
-- |     `- TrueP  i=2
-- |        |
-- |        +- TrueP  0 == 0
-- |        |
-- |        `- PAnd
-- |           |
-- |           +- PStringCI a == "idris"
-- |           |
-- |           `- PNot
-- |              |
-- |              `- PStringCS a == "idris"
-- |
-- +- TrueP  PLinear | OneMatch 0 a="idirs" cnt=1 (i=1, a="idirs")
-- |  |
-- |  +- FalseP i=0: PStringCS "idirs" == "idris"
-- |  |
-- |  +- TrueP  i=1: PDistCI | dist=2 | s=idris | t=idirs
-- |  |  |
-- |  |  `- TrueP  2 == [1..2]
-- |  |
-- |  `- FalseP i=2: PAnd
-- |     |
-- |     +- FalseP PStringCI "idirs" == "idris"
-- |     |
-- |     `- TrueP  PNot
-- |        |
-- |        `- FalseP PStringCS "idirs" == "idris"
-- |
-- `- TrueP  PLinear NoMatch 1 a="haskell"
--    |
--    +- FalseP i=0: PStringCS "haskell" == "idris"
--    |
--    +- FalseP i=1: PDistCI | dist=7 | s=idris | t=haskell
--    |  |
--    |  `- FalseP 7 > 2 (Over)
--    |
--    `- FalseP i=2: PAnd
--       |
--       +- FalseP PStringCI "haskell" == "idris"
--       |
--       `- TrueP  PNot
--          |
--          `- FalseP PStringCS "haskell" == "idris"
-- <BLANKLINE>
--
plinearDist :: (Foldable t, SConv s) => Int -> [Dist s] -> Pred (t s)
plinearDist n ds = _PLinear Loose (pdists n ds)

-- | used by 'plinearDist' to look for a match on s and not allowed to match on values that are at least 1 unit distance from it
-- ie looks for fat fingering
data Dist s = Dist (Pred Int) Case s deriving Show

-- | required
dreq :: s -> Dist s
dreq = Dist preq' CS

dopt :: s -> Dist s
dopt = Dist popt' CS

dij :: Int -> Int -> s -> Dist s
dij i j = Dist (_PRange i j) CS

dnever :: s -> Dist s
dnever = Dist (_PRange 0 0) CS

dreqCI :: s -> Dist s
dreqCI = Dist preq' CI

doptCI :: s -> Dist s
doptCI = Dist popt' CI

dijCI :: Int -> Int -> s -> Dist s
dijCI i j = Dist (_PRange i j) CI

dneverCI :: s -> Dist s
dneverCI = Dist (_PRange 0 0) CI

-- | prefix match: most common version is fail if no match and use Longest match
--
-- >>> pe2' (pregex (((,,) . read @Int) <$> some (psym isDigit) <*> few (sym 'x') <*> some (psym isDigit)) $ 1) "123x1"
-- <BLANKLINE>
-- TrueP  PRegex RLong as="123x1" b=(123,"x","1") rs=""
-- |
-- `- TrueP  PConst a=((123,"x","1"),"")
-- <BLANKLINE>
--
-- >>> pe2' (pregex (((,,) . read @Int) <$> some (psym isDigit) <*> few (psym isDigit) <*> some (psym isDigit)) $ 1) "123x1"
-- <BLANKLINE>
-- TrueP  PRegex RLong as="123x1" b=(12,"","3") rs="x1"
-- |
-- `- TrueP  PConst a=((12,"","3"),"x1")
-- <BLANKLINE>
--
-- >>> pe2' (pregex (((,,) . read @Int) <$> some (psym isDigit) <*> few (psym isDigit) <*> some (psym isDigit)) $ 1) "1231"
-- <BLANKLINE>
-- TrueP  PRegex RLong as="1231" b=(123,"","1") rs=""
-- |
-- `- TrueP  PConst a=((123,"","1"),"")
-- <BLANKLINE>
--
-- >>> pe2' (pregex ((,,) <$> ratio <* sym 'x' <*> few (psym isDigit) <*> int) 1) "123x987"
-- <BLANKLINE>
-- TrueP  PRegex RLong as="123x987" b=(123 % 1,"",987) rs=""
-- |
-- `- TrueP  PConst a=((123 % 1,"",987),"")
-- <BLANKLINE>
--
pregex  :: (Foldable t, Show a, Show b) => RE a b -> Pred (b,[a]) -> Pred (t a)
pregex r = _PRegex RLong r 0

-- | infix match: most common version is fail if no match and use Longest match
--
-- >>> pe2' (pregexi (read @Int <$> some (psym isDigit)) 1) "abc123def"
-- <BLANKLINE>
-- TrueP  PRegexI RLong as="abc123def" b=123 used="abc" remaining="def"
-- |
-- `- TrueP  PConst a=("abc",123,"def")
-- <BLANKLINE>
--
-- >>> pe2' (pregexi (read @Int <$> some (psym isDigit)) $ p_2 (pgt 122)) "abc123def"
-- <BLANKLINE>
-- TrueP  PRegexI RLong as="abc123def" b=123 used="abc" remaining="def"
-- |
-- `- TrueP  PFn _2 | a=("abc",123,"def") | b=123
--    |
--    `- TrueP  123 > 122
-- <BLANKLINE>
--
-- >>> pe2' (pregex ((read @Integer <$> some (psym isDigit)) <|> pure 999) $ p_1 (pgt 122)) "123def"
-- <BLANKLINE>
-- TrueP  PRegex RLong as="123def" b=123 rs="def"
-- |
-- `- TrueP  PFn _1 | a=(123,"def") | b=123
--    |
--    `- TrueP  123 > 122
-- <BLANKLINE>
--
-- >>> pe2' (pregexi ((read @Int <$> some (psym isDigit)) <|> pure 999) $ p_2 (pgt 122)) "abc123def"
-- <BLANKLINE>
-- TrueP  PRegexI RLong as="abc123def" b=999 used="" remaining="abc123def"
-- |
-- `- TrueP  PFn _2 | a=("",999,"abc123def") | b=999
--    |
--    `- TrueP  999 > 122
-- <BLANKLINE>
--
-- >>> pe2' (pregexi (intersperseNP 4 (sym '.') int) $ p_1 _PNull * p_2 (_PForAll (ple 255)) * p_2 (_PLen (peq 4))) "start123.223.1.256end"
-- <BLANKLINE>
-- FalseP PRegexI RLong as="start123.223.1.256end" b=[123,223,1,256] used="start" remaining="end"
-- |
-- `- FalseP PAnd
--    |
--    +- FalseP PAnd
--    |  |
--    |  +- FalseP PFn _1 | a=("start",[123,223,1,256],"end") | b="start"
--    |  |  |
--    |  |  `- FalseP PNull length=5 as="start"
--    |  |
--    |  `- FalseP PFn _2 | a=("start",[123,223,1,256],"end") | b=[123,223,1,256]
--    |     |
--    |     `- FalseP PForAll | cnt=1 (i=3, a=256)
--    |        |
--    |        +- TrueP  i=0: 123 <= 255
--    |        |
--    |        +- TrueP  i=1: 223 <= 255
--    |        |
--    |        +- TrueP  i=2: 1 <= 255
--    |        |
--    |        `- FalseP i=3: 256 <= 255
--    |
--    `- TrueP  PFn _2 | a=("start",[123,223,1,256],"end") | b=[123,223,1,256]
--       |
--       `- TrueP  PLen 4 as=[123,223,1,256]
--          |
--          `- TrueP  4 == 4
-- <BLANKLINE>
--
pregexi :: (Foldable t, Show a, Show b) => RE a b -> Pred ([a],b,[a]) -> Pred (t a)
pregexi r = _PRegexI RLong r 0

-- | most common usecase. match all 'peq2' and use 'RLong' ie longest match
--
-- >>> pe2' (pregexs [int, "." *> int, "." *> int, "." *> int] $ _PBoth (_PLen (peq 4) * _PForAll (_PRange 0 255)) _PNull) ("123.33.281.2abcdef" :: String)
-- <BLANKLINE>
-- FalseP PRegexs (4) | matched all(4) | leftovers="abcdef" | as="123.33.281.2abcdef"
-- |
-- +- FalseP PBoth
-- |  |
-- |  +- TrueP  PEq2 4 == 4
-- |  |
-- |  `- FalseP PBoth
-- |     |
-- |     +- FalseP PAnd
-- |     |  |
-- |     |  +- TrueP  PLen 4 as=[123,33,281,2]
-- |     |  |  |
-- |     |  |  `- TrueP  4 == 4
-- |     |  |
-- |     |  `- FalseP PForAll | cnt=1 (i=2, a=281)
-- |     |     |
-- |     |     +- TrueP  i=0: 123 == [0..255]
-- |     |     |
-- |     |     +- TrueP  i=1: 33 == [0..255]
-- |     |     |
-- |     |     +- FalseP i=2: 281 > 255 (Over)
-- |     |     |
-- |     |     `- TrueP  i=3: 2 == [0..255]
-- |     |
-- |     `- FalseP PNull length=6 as="abcdef"
-- |
-- `- matched all(4) | leftovers="abcdef"
--    |
--    +- i=0 | b=123 | used="123" | remaining=".33.281.2abcdef"
--    |
--    +- i=1 | b=33 | used=".33" | remaining=".281.2abcdef"
--    |
--    +- i=2 | b=281 | used=".281" | remaining=".2abcdef"
--    |
--    `- i=3 | b=2 | used=".2" | remaining="abcdef"
-- <BLANKLINE>
--
--
-- >>> pe2' (pregexs (int : replicate 3 ("." *> int)) 1) "123.33.1.2"
-- <BLANKLINE>
-- TrueP  PRegexs (4) | matched all(4) | leftovers="" | as="123.33.1.2"
-- |
-- +- TrueP  PBoth
-- |  |
-- |  +- TrueP  PEq2 4 == 4
-- |  |
-- |  `- TrueP  PConst a=([123,33,1,2],"")
-- |
-- `- matched all(4) | leftovers=""
--    |
--    +- i=0 | b=123 | used="123" | remaining=".33.1.2"
--    |
--    +- i=1 | b=33 | used=".33" | remaining=".1.2"
--    |
--    +- i=2 | b=1 | used=".1" | remaining=".2"
--    |
--    `- i=3 | b=2 | used=".2" | remaining=""
-- <BLANKLINE>
--
-- >>> pe2' (pregexs [int, "." *> int, "." *> int, "." *> int] $ _PBoth (_PLen (peq 4) * _PForAll (_PRange 0 255)) _PNull) "123.33x.281.2abcdef"
-- <BLANKLINE>
-- FalseP PRegexs (4) | only matched 2 of {4} | leftovers="x.281.2abcdef" | as="123.33x.281.2abcdef"
-- |
-- +- FalseP PBoth
-- |  |
-- |  +- FalseP not all matched | PEq2 4 == 2
-- |  |
-- |  `- FalseP PBoth
-- |     |
-- |     +- FalseP PAnd
-- |     |  |
-- |     |  +- FalseP PLen 2 as=[123,33]
-- |     |  |  |
-- |     |  |  `- FalseP 2 == 4
-- |     |  |
-- |     |  `- TrueP  PForAll
-- |     |     |
-- |     |     +- TrueP  i=0: 123 == [0..255]
-- |     |     |
-- |     |     `- TrueP  i=1: 33 == [0..255]
-- |     |
-- |     `- FalseP PNull length=13 as="x.281.2abcdef"
-- |
-- `- only matched 2 of {4} | leftovers="x.281.2abcdef"
--    |
--    +- i=0 | b=123 | used="123" | remaining=".33x.281.2abcdef"
--    |
--    `- i=1 | b=33 | used=".33" | remaining="x.281.2abcdef"
-- <BLANKLINE>
--
-- >>> pe2' (pregexs (replicate 6 (double <* spaces)) $ _PFst $ _PForAll (_PRange 54 304)) "213   1223 23    55 99 1111    8x"
-- <BLANKLINE>
-- FalseP PRegexs (6) | matched all(6) | leftovers="8x" | as="213   1223 23    55 99 1111    8x"
-- |
-- +- FalseP PBoth
-- |  |
-- |  +- TrueP  PEq2 6 == 6
-- |  |
-- |  `- FalseP PFst a=[213.0,1223.0,23.0,55.0,99.0,1111.0] snd="8x"
-- |     |
-- |     `- FalseP PForAll | cnt=3 (i=1, a=1223.0)
-- |        |
-- |        +- TrueP  i=0: 213.0 == [54.0..304.0]
-- |        |
-- |        +- FalseP i=1: 1223.0 > 304.0 (Over)
-- |        |
-- |        +- FalseP i=2: 23.0 < 54.0 (Under)
-- |        |
-- |        +- TrueP  i=3: 55.0 == [54.0..304.0]
-- |        |
-- |        +- TrueP  i=4: 99.0 == [54.0..304.0]
-- |        |
-- |        `- FalseP i=5: 1111.0 > 304.0 (Over)
-- |
-- `- matched all(6) | leftovers="8x"
--    |
--    +- i=0 | b=213.0 | used="213   " | remaining="1223 23    55 99 1111    8x"
--    |
--    +- i=1 | b=1223.0 | used="1223 " | remaining="23    55 99 1111    8x"
--    |
--    +- i=2 | b=23.0 | used="23    " | remaining="55 99 1111    8x"
--    |
--    +- i=3 | b=55.0 | used="55 " | remaining="99 1111    8x"
--    |
--    +- i=4 | b=99.0 | used="99 " | remaining="1111    8x"
--    |
--    `- i=5 | b=1111.0 | used="1111    " | remaining="8x"
-- <BLANKLINE>
--
-- >>> pe2' (pregexs (replicate 6 (int <* spaces)) $ _PFst $ _PForAll (_PRange 100 204)) "213   1223 23    55"
-- <BLANKLINE>
-- FalseP PRegexs (6) | only matched 4 of {6} | leftovers="" | as="213   1223 23    55"
-- |
-- +- FalseP PBoth
-- |  |
-- |  +- FalseP not all matched | PEq2 6 == 4
-- |  |
-- |  `- FalseP PFst a=[213,1223,23,55] snd=""
-- |     |
-- |     `- FalseP PForAll | cnt=4 (i=0, a=213)
-- |        |
-- |        +- FalseP i=0: 213 > 204 (Over)
-- |        |
-- |        +- FalseP i=1: 1223 > 204 (Over)
-- |        |
-- |        +- FalseP i=2: 23 < 100 (Under)
-- |        |
-- |        `- FalseP i=3: 55 < 100 (Under)
-- |
-- `- only matched 4 of {6} | leftovers=""
--    |
--    +- i=0 | b=213 | used="213   " | remaining="1223 23    55"
--    |
--    +- i=1 | b=1223 | used="1223 " | remaining="23    55"
--    |
--    +- i=2 | b=23 | used="23    " | remaining="55"
--    |
--    `- i=3 | b=55 | used="55" | remaining=""
-- <BLANKLINE>
--
pregexs :: (Foldable t, Eq a, Show a, Show b) => [RE a b] -> Pred ([b],[a]) -> Pred (t a)
pregexs rs p = pregexs' RLong rs (_PBoth (pmsgIfNotTrue "not all matched" (_PEq2 True)) p)

-- | tack on 'RType'
pregexs' :: (Foldable t, Eq a, Show a, Show b) => RType -> [RE a b] -> Pred ((Int,Int),([b],[a])) -> Pred (t a)
pregexs' t = _PRegexs . map (t,)

-- | runs 'PISect' after getting rid of duplicates
--
-- >>> pe2' (pisectNub @[] 1) ("aaabc","adbbef")
-- <BLANKLINE>
-- TrueP  PISect as="abc" bs="adbef" left="c" isect="ab" right="def"
-- |
-- `- TrueP  PConst a=("c","ab","def")
-- <BLANKLINE>
--
-- >>> pe1' (pisectNub @[] 1) ("aaabc","adef")
-- <BLANKLINE>
-- TrueP  PISect left="bc" isect="a" right="def"
-- |
-- `- TrueP  PConst a=("bc","a","def")
-- <BLANKLINE>
--
-- >>> pe1' (pisectNub @[] 1) ("aaabc","adef")
-- <BLANKLINE>
-- TrueP  PISect left="bc" isect="a" right="def"
-- |
-- `- TrueP  PConst a=("bc","a","def")
-- <BLANKLINE>
--
-- >>> pe1' (pisectNub @[] 1) ("aaabc","adbbef")
-- <BLANKLINE>
-- TrueP  PISect left="c" isect="ab" right="def"
-- |
-- `- TrueP  PConst a=("c","ab","def")
-- <BLANKLINE>
--
pisectNub :: (Foldable t, Ord a, Show a, Show (t a)) => Pred ([a], [a], [a]) -> Pred (t a, t a)
pisectNub = phide . pstar2 "nub" (nub . toList) . _PISect

-- | runs 'PISectList' after getting rid of duplicates
pisectListNub :: (Foldable t, Foldable u, Ord a, Show (u (t a)), Show a) => Pred ([a], [a]) -> Pred (u (t a))
pisectListNub = phide . _PFn "nublist" (fmap (nub . toList) . toList) . _PISectList

-- | lifted version of 'Control.Arrow.first'
pfirst :: (Show b, Show a, Show x) => (a -> b) -> Pred (b, x) -> Pred (a, x)
pfirst = _PFn "pfirst" . first

-- | lifted version of 'Control.Arrow.second'
psecond :: (Show b, Show a, Show x) => (a -> b) -> Pred (x, b) -> Pred (x, a)
psecond = _PFn "psecond" . second

pe, pe1, pe2, pe', pe1', pe2', peu, peu1, peu2 :: Pred a -> a -> IO ()
pe = peWith (horizontal o0)
pe1 = peWith (horizontal o1)
pe2 = peWith (horizontal o2)

-- for use with doctest as we dont want colors cos will mess up the ouput
pe' = peWith (horizontal $ setc0 o0)
pe1' = peWith (horizontal $ setc0 o1)
pe2' = peWith (horizontal $ setc0 o2)

peu = peWith (unicode o0)
peu1 = peWith (unicode o1)
peu2 = peWith (unicode o2)

peWith :: POpts -> Pred a -> a -> IO ()
peWith o (Pred _ p) = prtImpl o . fmap (toNodeString o) . p o

matchKeyP :: Pred String -> (NonEmpty JPath, Value) -> Maybe (String, Value)
matchKeyP p (JPKey k :| _, v) =
  let ll = _pfn p defOpts k
  in case getBool ll of
    TrueP -> Just (k, v)
    _ -> Nothing
matchKeyP _ _ = Nothing

-- using Pred cos makes it easier: just ignoring result unless TrueP
-- we dont trace this stuff cos not needed
-- the value-add is that it returns a String
matchStringP :: Pred String -> (NonEmpty JPath, Value) -> Maybe String
matchStringP p (x :| _, _) =
  case x ^? _JPValue . _String . to T.unpack of
    Just s -> do
                let ll = _pfn p defOpts s
                case getBool ll of
                  TrueP -> Just s
                  _ -> Nothing
    Nothing -> Nothing
-- | match on any json 'String'
--
-- >>> pe1' (pjsonString 1 (psnds $ _PLinear Rigid $ map (preq . peq) ["Vladimir"])) json2
-- <BLANKLINE>
-- FalseP PJson
-- |
-- +- FalseP PLinear | errors(7): NoMatch 0 | NoMatch 1 | NoMatch 2 | NoMatch 3 | NoMatch 4 | NoMatch 5 | NoMatch 6
-- |  |
-- |  +- TrueP  Predicates | PZipAnd | PZipExact | (bad,good)=(0,1)
-- |  |  |
-- |  |  `- TrueP  PLift and | a=[True]
-- |  |     |
-- |  |     `- TrueP  i=0
-- |  |        |
-- |  |        +- TrueP  1 == 1
-- |  |        |
-- |  |        `- a == "Vladimir"
-- |  |
-- |  +- FalseP PLinear NoMatch 0 a="Diaz"
-- |  |  |
-- |  |  `- FalseP i=0: "Diaz" == "Vladimir"
-- |  |
-- |  +- FalseP PLinear NoMatch 1 a="Daniel"
-- |  |  |
-- |  |  `- FalseP i=0: "Daniel" == "Vladimir"
-- |  |
-- |  +- FalseP PLinear NoMatch 2 a="Red"
-- |  |  |
-- |  |  `- FalseP i=0: "Red" == "Vladimir"
-- |  |
-- |  +- FalseP PLinear NoMatch 3 a="Rose"
-- |  |  |
-- |  |  `- FalseP i=0: "Rose" == "Vladimir"
-- |  |
-- |  +- FalseP PLinear NoMatch 4 a="Doe"
-- |  |  |
-- |  |  `- FalseP i=0: "Doe" == "Vladimir"
-- |  |
-- |  +- FalseP PLinear NoMatch 5 a="John"
-- |  |  |
-- |  |  `- FalseP i=0: "John" == "Vladimir"
-- |  |
-- |  +- FalseP PLinear NoMatch 6 a="Vygodsky"
-- |  |  |
-- |  |  `- FalseP i=0: "Vygodsky" == "Vladimir"
-- |  |
-- |  `- TrueP  PLinear | OneMatch 7 a="Vladimir" cnt=1 (i=0, a="Vladimir")
-- |     |
-- |     `- TrueP  i=0: "Vladimir" == "Vladimir"
-- |
-- `- Debugging jpaths
--    |
--    +- i=0 | [JPIndex 0,JPKey "lastName",JPValue (String "Diaz")]
--    |
--    +- i=1 | [JPIndex 0,JPKey "firstName",JPValue (String "Daniel")]
--    |
--    +- i=2 | [JPIndex 1,JPKey "lastName",JPValue (String "Red")]
--    |
--    +- i=3 | [JPIndex 1,JPKey "firstName",JPValue (String "Rose")]
--    |
--    +- i=4 | [JPIndex 2,JPKey "lastName",JPValue (String "Doe")]
--    |
--    +- i=5 | [JPIndex 2,JPKey "firstName",JPValue (String "John")]
--    |
--    +- i=6 | [JPIndex 3,JPKey "lastName",JPValue (String "Vygodsky")]
--    |
--    `- i=7 | [JPIndex 3,JPKey "firstName",JPValue (String "Vladimir")]
-- <BLANKLINE>
--
-- >>> pe2' (pjsonString (sinfix "iso") $ psnds $ _PShow 1) json1
-- <BLANKLINE>
-- TrueP  PJson
-- |
-- +- TrueP  PShow
-- |  |
-- |  +- TrueP  PConst a=["ISO 8879:1986"]
-- |  |
-- |  `- ===== PShow =====
-- |     |
-- |     `- i=0 a="ISO 8879:1986"
-- |
-- `- Debugging jpaths
--    |
--    `- i=0 | [JPKey "glossary",JPKey "GlossDiv",JPKey "GlossList",JPKey "GlossEntry",JPKey "Abbrev",JPValue (String "ISO 8879:1986")] | a="ISO 8879:1986"
-- <BLANKLINE>
--
pjsonString :: Pred String -> Pred [(NonEmpty JPath, String)] -> Pred Value
pjsonString = _PJson . matchStringP


-- | 'PJsonKey' but expects exactly one match
--
-- >>> pe' (pjsonKeyOne "abbrev" 1) json1
-- <BLANKLINE>
-- TrueP  PJsonKey
-- |
-- +- TrueP  POne String "ISO 8879:1986"
-- |  |
-- |  `- TrueP
-- |
-- `- Debugging jpaths
--    |
--    `- i=0 | key=Abbrev
-- <BLANKLINE>
--
-- >>> pe' (pjsonKeyOne "abbrev" 1) json0
-- <BLANKLINE>
-- FalseP PJsonKey | json search failed
-- |
-- +- FalseP POne empty!
-- |
-- `- Debugging jpaths
-- <BLANKLINE>
--
-- >>> pe' (pjsonKeyOne "title" 1) json1
-- <BLANKLINE>
-- FalseP PJsonKey
-- |
-- +- FalseP POne extra values! a=String "S" s'=[String "example glossary"]
-- |  |
-- |  `- FalseP
-- |
-- `- Debugging jpaths
--    |
--    +- i=0 | key=title
--    |
--    `- i=1 | key=title
-- <BLANKLINE>
--
-- >>> pe1' (pjsonKeyOne (sinfix "seeal") $ jarray 0 $ _PLinear Rigid [preq "xml",preq "gml"]) json1
-- <BLANKLINE>
-- TrueP  PJsonKey
-- |
-- +- TrueP  POne Array [String "GML",String "XML"]
-- |  |
-- |  `- TrueP  PPrism (Just) [jarray] [String "GML",String "XML"]
-- |     |
-- |     `- TrueP  PLinear
-- |        |
-- |        +- TrueP  Predicates | PZipAnd | PZipExact | (bad,good)=(0,2)
-- |        |  |
-- |        |  `- TrueP  PLift and | a=[True,True]
-- |        |     |
-- |        |     +- TrueP  i=0
-- |        |     |  |
-- |        |     |  +- TrueP  1 == 1
-- |        |     |  |
-- |        |     |  `- PStringCI a == String "xml"
-- |        |     |
-- |        |     `- TrueP  i=1
-- |        |        |
-- |        |        +- TrueP  1 == 1
-- |        |        |
-- |        |        `- PStringCI a == String "gml"
-- |        |
-- |        +- TrueP  PLinear | OneMatch 0 a=String "GML" cnt=1 (i=1, a=String "GML")
-- |        |  |
-- |        |  +- FalseP i=0: PStringCI String "GML" == String "xml"
-- |        |  |
-- |        |  `- TrueP  i=1: PStringCI String "GML" == String "gml"
-- |        |
-- |        `- TrueP  PLinear | OneMatch 1 a=String "XML" cnt=1 (i=0, a=String "XML")
-- |           |
-- |           +- TrueP  i=0: PStringCI String "XML" == String "xml"
-- |           |
-- |           `- FalseP i=1: PStringCI String "XML" == String "gml"
-- |
-- `- Debugging jpaths
--    |
--    `- i=0 | key=GlossSeeAlso | [JPKey "glossary",JPKey "GlossDiv",JPKey "GlossList",JPKey "GlossEntry",JPKey "GlossDef",JPKey "GlossSeeAlso"]
-- <BLANKLINE>
--
-- >>> pe' (pjsonKeyOne "abbrev" $ sinfix "iso") json1
-- <BLANKLINE>
-- TrueP  PJsonKey
-- |
-- +- TrueP  POne String "ISO 8879:1986"
-- |  |
-- |  `- TrueP  PStringCI String "iso" `isInfixOf` String "ISO 8879:1986"
-- |
-- `- Debugging jpaths
--    |
--    `- i=0 | key=Abbrev
-- <BLANKLINE>
--
pjsonKeyOne :: Pred String -> Pred Value -> Pred Value
pjsonKeyOne q = _PJsonKey q . psnds . pone

pjsonKeyOne' :: Pred String -> Pred (NonEmpty JPath, Value) -> Pred Value
pjsonKeyOne' q = _PJsonKey q . pone

-- unsafe
jkeyPrint :: AsValue s => Pred String -> s -> IO [Value]
jkeyPrint pk js = jkeyPrint' $ jvisitor (matchKeyP pk) (js ^?! _Value)


linearImpl :: Show x =>
                     POpts
                    -> String
                    -> Rigid
                    -> [(Pred Int,Pred x)]
                    -> [x]
                    -> TT
linearImpl opts nm noextravalues qps as =
    let tss = zipWith (\j a -> ((j, a), zipWith (\i (_, Pred _ p)  -> ((i, a), p opts a)) [0::Int ..] qps)) [0::Int ..] as
        -- one mega mkNode with subnodes and subnodes beneath if failure
        -- process one 'a' over all the ps and summarise which single p worked -- if not it is a left [need to stash all the values for output]
        -- do repeatedly then pass back over the list and adjust the summary for each one based on previous info if there is an error
        -- map has predicates to values used for the next predicate on [Int]
        (ret, vvv) = flip S.runState (M.empty :: Map Int [Int]) $
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

        cnts = map (\j -> maybe 0 length (M.lookup j vvv)) [0 .. length qps -1]
        zzz = map (\(q, p) -> if oDebug opts >= 1 then _PTree (fn p) q else q) qps
        -- grafts showPred tree if debug mode
        fn p tt = mkNode (getBool tt, []) [tt, fmap (\n -> BoolPE (getBool tt) False [n]) (_ppred p)]

        ll = addMessagePre "Predicates" (_pfn (pzipand zzz) opts cnts)

        msgs = [if null errs then "" else "errors(" <> show (length errs) <> "): " <> intercalate " | " (map show errs)
               ,showA opts 2 "debug=" (map fst ret) <> showA opts 2 " match=" (itoList vvv)
               ]
      in case getBool ll of
           FailP e -> mkNode (FailP ("Failed Pred [Int]" N.<| e), nm : msgs) (ll : ns)
           FalseP -> mkNode (FalseP, nm <> " Failed Pred [Int]" : msgs) (ll : ns)
           TrueP -> mkNode (_BoolP # null errs, nm :msgs) (ll : ns)


----------------------------------- START JSON STUFF ----------------------------------------
-- | 'PJsonP' but converts the 'NonEmpty' 'JPath' to '[JPath]'
pjsonpNE :: NonEmpty JPath -> Pred () -> Pred Value -> Pred Value
pjsonpNE = _PJsonP . reverse . N.toList

-- | match on json 'Array' and pull out the value at the given index or indices
pjsonIndex :: (Int -> Bool) -> Pred [(NonEmpty JPath, (Int, Value))] -> Pred Value
pjsonIndex = _PJson . matchIndex

-- | match on json 'Number' and pull out any numbers that satisfy the function predicate
--
-- >>> pe1' ((pjsonNumber (const True)) (psnds $ _PLinear Rigid $ map (preq . peq) [24,39])) json2
-- <BLANKLINE>
-- FalseP PJson
-- |
-- +- FalseP PLinear | errors(2): NoMatch 2 | NoMatch 3
-- |  |
-- |  +- TrueP  Predicates | PZipAnd | PZipExact | (bad,good)=(0,2)
-- |  |  |
-- |  |  `- TrueP  PLift and | a=[True,True]
-- |  |     |
-- |  |     +- TrueP  i=0
-- |  |     |  |
-- |  |     |  +- TrueP  1 == 1
-- |  |     |  |
-- |  |     |  `- a == 24.0
-- |  |     |
-- |  |     `- TrueP  i=1
-- |  |        |
-- |  |        +- TrueP  1 == 1
-- |  |        |
-- |  |        `- a == 39.0
-- |  |
-- |  +- TrueP  PLinear | OneMatch 0 a=24.0 cnt=1 (i=0, a=24.0)
-- |  |  |
-- |  |  +- TrueP  i=0: 24.0 == 24.0
-- |  |  |
-- |  |  `- FalseP i=1: 24.0 == 39.0
-- |  |
-- |  +- TrueP  PLinear | OneMatch 1 a=39.0 cnt=1 (i=1, a=39.0)
-- |  |  |
-- |  |  +- FalseP i=0: 39.0 == 24.0
-- |  |  |
-- |  |  `- TrueP  i=1: 39.0 == 39.0
-- |  |
-- |  +- FalseP PLinear NoMatch 2 a=45.0
-- |  |  |
-- |  |  +- FalseP i=0: 45.0 == 24.0
-- |  |  |
-- |  |  `- FalseP i=1: 45.0 == 39.0
-- |  |
-- |  `- FalseP PLinear NoMatch 3 a=27.0
-- |     |
-- |     +- FalseP i=0: 27.0 == 24.0
-- |     |
-- |     `- FalseP i=1: 27.0 == 39.0
-- |
-- `- Debugging jpaths
--    |
--    +- i=0 | [JPIndex 0,JPKey "age",JPValue (Number 24.0)]
--    |
--    +- i=1 | [JPIndex 1,JPKey "age",JPValue (Number 39.0)]
--    |
--    +- i=2 | [JPIndex 2,JPKey "age",JPValue (Number 45.0)]
--    |
--    `- i=3 | [JPIndex 3,JPKey "age",JPValue (Number 27.0)]
-- <BLANKLINE>
--
pjsonNumber :: (Scientific -> Bool) -> Pred [(NonEmpty JPath, Scientific)] -> Pred Value
pjsonNumber = _PJson . matchNumber

-- | match on all json 'Bool'
pjsonBool :: Pred [(NonEmpty JPath, Bool)] -> Pred Value
pjsonBool = _PJson matchBool

-- | match on all json 'Array'
pjsonArrays :: Pred [(NonEmpty JPath, [Value])] -> Pred Value
pjsonArrays = _PJson matchArrays

-- | match on all json 'Object'
pjsonObjects :: Pred [(NonEmpty JPath, HashMap Text Value)] -> Pred Value
pjsonObjects = _PJson matchObjects

lnum :: AsValue a =>
     Int -> Int -> Pred Scientific -> (Pred Int, Pred a)
lnum i j = pij i j . jnumber pfalse

lstring :: AsValue a =>
     Int -> Int -> Pred String -> (Pred Int, Pred a)
lstring i j = pij i j . jstring pfalse

-- dont often need this cos can use "xx" cos defined for Aeson String!
jstring :: AsValue s => Pred () -> Pred String -> Pred s
jstring = _PPrism "jstring" (^? _String . to T.unpack)

-- | converts a predicate on a json 'Value' to a predicate on Scientific. if not match then call () predicate
jnumber :: AsValue s => Pred () -> Pred Scientific -> Pred s
jnumber = _PPrism "jnumber" (^? _Number)

jnumbers :: (Foldable t, AsValue s, Show s) => Pred ([s], [Scientific]) -> Pred (t s)
jnumbers = _PMorph (^? _Number)
-- | pull out all the numbers but fail if not all pulled
--
-- >>> pe2' (_PJsonKey "AgE" $ psnds $ jnumbers' $ _PShow 1) json2
-- <BLANKLINE>
-- TrueP  PJsonKey
-- |
-- +- TrueP  PMorph [Number 24.0,Number 39.0,Number 45.0,Number 27.0] bad=[] good=[24.0,39.0,45.0,27.0]
-- |  |
-- |  `- TrueP  PBoth
-- |     |
-- |     +- TrueP  PNull length=0 as=[]
-- |     |
-- |     `- TrueP  PShow
-- |        |
-- |        +- TrueP  PConst a=[24.0,39.0,45.0,27.0]
-- |        |
-- |        `- ===== PShow =====
-- |           |
-- |           +- i=0 a=24.0
-- |           |
-- |           +- i=1 a=39.0
-- |           |
-- |           +- i=2 a=45.0
-- |           |
-- |           `- i=3 a=27.0
-- |
-- `- Debugging jpaths
--    |
--    +- i=0 | key=age | [JPIndex 0,JPKey "age"] | value=Number 24.0
--    |
--    +- i=1 | key=age | [JPIndex 1,JPKey "age"] | value=Number 39.0
--    |
--    +- i=2 | key=age | [JPIndex 2,JPKey "age"] | value=Number 45.0
--    |
--    `- i=3 | key=age | [JPIndex 3,JPKey "age"] | value=Number 27.0
-- <BLANKLINE>
--
jnumbers' :: (Foldable t, AsValue s, Show s) => Pred [Scientific] -> Pred (t s)
jnumbers' = _PMorph (^? _Number) . _PBoth _PNull

jstrings :: (Foldable t, AsValue s, Show s) => Pred ([s], [String]) -> Pred (t s)
jstrings = _PMorph (^? _String . to T.unpack)

-- | pull out all the strings but fail if not all pulled
--
-- >>> pe' (_PJsonKey "title" $ psnds $ jstrings' $ _PShow 1) json1
-- <BLANKLINE>
-- TrueP  PJsonKey
-- |
-- +- TrueP  PMorph
-- |  |
-- |  `- TrueP  PBoth
-- |     |
-- |     +- TrueP  PNull length=0
-- |     |
-- |     `- TrueP  PShow
-- |        |
-- |        +- TrueP
-- |        |
-- |        `- ===== PShow =====
-- |           |
-- |           +- i=0 a="S"
-- |           |
-- |           `- i=1 a="example glossary"
-- |
-- `- Debugging jpaths
--    |
--    +- i=0 | key=title
--    |
--    `- i=1 | key=title
-- <BLANKLINE>
--
jstrings' :: (Foldable t, AsValue s, Show s) => Pred [String] -> Pred (t s)
jstrings' = _PMorph (^? _String . to T.unpack) . _PBoth _PNull

jbools :: (Foldable t, AsValue s, Show s) => Pred ([s], [Bool]) -> Pred (t s)
jbools = _PMorph (^? _Bool)

jbools' :: (Foldable t, AsValue s, Show s) => Pred [Bool] -> Pred (t s)
jbools' = _PMorph (^? _Bool) . _PBoth _PNull

jintegral :: (AsValue s, Show a, Integral a) => Pred () -> Pred a -> Pred s
jintegral = _PPrism "jintegral" (^? _Integral)

jinteger :: AsValue s => Pred () -> Pred Integer -> Pred s
jinteger = jintegral

-- | extract a Double from json 'Value'
jdouble :: AsValue s => Pred () -> Pred Double -> Pred s
jdouble = _PPrism "jdouble" (^? _Double)

-- | extract a Bool from json 'Value'
jbool :: AsValue s => Pred () -> Pred Bool -> Pred s
jbool = _PPrism "jbool" (^? _Bool)

-- | predicate for json 'Null'
jnull :: AsValue s => Pred s
jnull = jnull' 0 1

jnull' ::AsValue s => Pred () -> Pred () -> Pred s
jnull' = _PPrism "jnull" (^? _Null)

jnotnull :: (AsValue s, Show s) => Pred s
jnotnull = -jnull

jvalue :: AsValue s => Pred () -> Pred Value -> Pred s
jvalue = _PPrism "jvalue" (^? _Value)

-- | change a predicate on 'Value' to a predicate 'Array' but if fails call the () predicate
--
-- >>> pe' (jarray 0 $ _PIx 2 0 $ _PIx "firstName" 0 $ "johan") json2
-- <BLANKLINE>
-- FalseP PPrism (Just) [jarray]
-- |
-- `- FalseP PIx 2 Object (fromList [("lastName",String "Doe"),("age",Number 45.0),("firstName",String "John"),("likesPizza",Bool ...
--    |
--    `- FalseP PIx "firstName" String "John"
--       |
--       `- FalseP PStringCI String "John" == String "johan"
-- <BLANKLINE>
--
jarray :: AsValue s => Pred () -> Pred (Vector Value) -> Pred s
jarray = _PPrism "jarray" (^? _Array)

jobject :: AsValue s => Pred () -> Pred (HashMap Text Value) -> Pred s
jobject = _PPrism "jobject" (^? _Object)

-- useful cos now we can use this in PLinearOLD / PForAll / PExists
jobjectList :: AsValue s => Pred () -> Pred [(Text, Value)] -> Pred s
jobjectList = _PPrism "jobjectList" (^? _Object . to H.toList)

pjpaths :: Show a => Pred [[JPath]] -> Pred [(NonEmpty JPath, a)]
pjpaths = phide . _PFn "pjpaths" (fmap (reverse . toList . fst))

-- psnds $ psnds -- exactly the same result
pjvalues :: (Show a, Show c, Show b) => Pred [c] -> Pred [(a, (b, c))]
pjvalues = phide . _PFn "pjvalues" (fmap (snd . snd))

----------------------------------- END JSON STUFF ----------------------------------------
----------------------------------- START DATETIME STUFF ----------------------------------------

-- | finds difference between two dates in days. uses 'pcu'
--
-- >>> let dt = UTCTime (read "2018-04-19") 360
-- >>> pe' (pdays id (pgt 10)) (dt, dt & date %~ addDays 15)
-- <BLANKLINE>
-- TrueP  PFn uncurry | a=(2018-04-19 00:06:00 UTC,2018-05-04 00:06:00 UTC) | b=15
-- |
-- `- TrueP  15 > 10
-- <BLANKLINE>
--
-- >>> let dt = UTCTime (read "2018-04-19") 360
-- >>> let dt1 = UTCTime (read "2018-04-25") 380
-- >>> pe2' (pdays id (_PRange 4 6)) (dt,dt1)
-- <BLANKLINE>
-- TrueP  PFn uncurry | a=(2018-04-19 00:06:00 UTC,2018-04-25 00:06:20 UTC) | b=6
-- |
-- `- TrueP  6 == [4..6]
-- <BLANKLINE>
--
pdays :: (Show a, Show x, Dateable a) => (x -> (a, a)) -> Pred Integer -> Pred x
pdays f = pcu f (on (flip diffDays) (^. date))

-- | finds difference between two dates in hours. uses 'pcu'
phours :: (Show a, Show x, Dateable a, Timeable a) => (x -> (a, a)) -> Pred Integer -> Pred x
phours f = pcu f (on (\(d, t) (d1, t1) -> 24 * diffDays d1 d  + fromIntegral (t1-t)) ((^. date) &&& (^. hours)))

-- | finds difference between two dates in minutes. uses 'pcu'
pminutes :: (Show a, Show x, Dateable a, Timeable a) => (x -> (a, a)) -> Pred Integer -> Pred x
pminutes f = pcu f (on (\(d, t) (d1, t1) -> 24 * 60 * diffDays d1 d  + truncate ((t1-t)/60)) ((^. date) &&& (^. timeAsDiff)))

-- | finds difference between two dates in seconds. uses 'pcu'
--
-- >>> let dt = UTCTime (read "2018-04-19") 360
-- >>> let dt1 = UTCTime (read "2018-04-19") 380
-- >>> pe2' (pseconds id (_PRange 19 22)) (dt,dt1)
-- <BLANKLINE>
-- TrueP  PFn uncurry | a=(2018-04-19 00:06:00 UTC,2018-04-19 00:06:20 UTC) | b=20
-- |
-- `- TrueP  20 == [19..22]
-- <BLANKLINE>
--
pseconds :: (Show a, Show x, Dateable a, Timeable a) => (x -> (a, a)) -> Pred Integer -> Pred x
pseconds f = pcu f (on (\(d, t) (d1, t1) -> 24 * 60 * 60 * diffDays d1 d  + truncate (t1-t)) ((^. date) &&& (^. timeAsDiff)))

----------------------------------- END DATETIME STUFF ----------------------------------------

-- | a predicate on a given type in a vinyl record. so if you do a Pred Char it will expect to find a Char somewhere in that record
prx :: (Show b, Show (record W.Identity rs), RecElemFCtx record W.Identity, RecElem record b b rs rs (RIndex b rs)) => Pred b -> Pred (record W.Identity rs)
prx = _PFn "prx" recGet

-- have to AllowAmbiguousTypes
pri' :: forall n f a xs. (RecordToList xs, ReifyConstraint Show f xs, RMap xs, Show (f a), G.KnownNat n, IndexType (Lit n) xs a) => Pred (f a) -> Pred (Rec f xs)
pri' =
  let i = G.natVal (Proxy @n)
  in _PFn ("@" <> show i <> "'") (fromIndex (Proxy @(Lit n)))

pri :: forall n a xs . (RecordToList xs, ReifyConstraint Show W.Identity xs, RMap xs, Show a, G.KnownNat n, IndexType (Lit n) xs a) => Pred a -> Pred (Rec W.Identity xs)
pri =
  let i = G.natVal (Proxy @n)
  in _PFn ("@" <> show i) (W.getIdentity . fromIndex (Proxy @(Lit n)))
