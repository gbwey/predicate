{-# OPTIONS -Wall #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE MultiWayIf #-}
module PredHelper where
import Data.Foldable
import Control.Lens
import Control.Arrow
import Data.List
import Data.Function
import qualified Data.Tree.View as TV
import Data.Tree
import Data.Tree.Lens
import Data.Proxy
import Data.List.NonEmpty (NonEmpty(..))
import qualified Data.List.NonEmpty as N
import Data.Char
import Data.Maybe
import qualified Data.Map.Strict as M
import Data.Map.Strict (Map)
import qualified Data.Text as T
import Data.Text (Text)
import Control.Applicative
import Data.Bool
import Data.Ord
import Data.Data
import Data.Tagged
import Data.Aeson
import qualified Data.ByteString.Lazy.Char8 as BL8
import qualified Data.ByteString.Char8 as BS8
import Control.Monad
import System.Console.Pretty
import Data.Semigroup
import Data.These
import Data.List.Split
import Text.EditDistance
import GHC.Generics (Generic)

-- | overrides Ord instance to hold the constructor value
newtype COrd k = COrd k deriving Show

unCOrd :: COrd k -> k
unCOrd (COrd k) = k

instance Data k => Ord (COrd k) where
  compare = comparing (constrIndex . toConstr . unCOrd)

instance Data k => Eq (COrd k) where
  (==) = on (==) (constrIndex . toConstr . unCOrd)
-- better cos could case match on whole map using keys if you want
-- and then fold the results back
-- or provide a with function that gives you access to all of that folded
-- | holds values keyed by its constructor
newtype CMap k v = CMap { unCMap :: Map (COrd k) v } deriving Show

-- | builds a map keyed by constructor
--
--   >>> toCMap (flip compare 7 &&& (:[])) [1..10]
--   CMap {unCMap = fromList [(COrd LT,[1,2,3,4,5,6]),(COrd EQ,[7]),(COrd GT,[8,9,10])]}
--
--   >>> toCMap (between 3 7 &&& (:[])) [1..10]
--   CMap {unCMap = fromList [(COrd LT,[1,2]),(COrd EQ,[3,4,5,6,7]),(COrd GT,[8,9,10])]}
--
--   >>> toCMap (flip compare 7 &&& (:[])) [7,7,7,7]
--   CMap {unCMap = fromList [(COrd EQ,[7,7,7,7])]}
--
--   >>> toCMap (flip compare 7 &&& (:[])) [1..6]
--   CMap {unCMap = fromList [(COrd LT,[1,2,3,4,5,6])]}
--
--   >>> toCMap (flip compare 7 &&& (:[])) [8..10]
--   CMap {unCMap = fromList [(COrd GT,[8,9,10])]}
--
toCMap :: (Data k, Monoid v) => (a -> (k, v)) -> [a] -> CMap k v
toCMap f = CMap . M.fromListWith (flip mappend) . map (first COrd . f)

toCMap' :: Data k => (a -> k) -> [a] -> CMap k [a]
toCMap' f = toCMap (f &&& (:[]))

getC1 :: CMap k v -> [(k,v)]
getC1 = map (first unCOrd) . M.toList . unCMap

getC :: (Data k, Monoid v) => k -> CMap k v -> v
getC k = fromMaybe mempty . M.lookup (COrd k) . unCMap

-- can case on the keys and fold into w
withC :: Monoid w => ((k,v) -> w) -> CMap k v -> w
withC f = foldMap f . getC1


-- fromConstrB (need to know a value to provide for those with data in the constructor)
-- could pass in undefined to the field
-- no such thing as a proxy to a value unless we use singletons or proxys
{-
>getC True $ toCMap snd [(1,True),(2,False),(3,True)]
Just [(3,True),(1,True)]
>getC False $ toCMap snd [(1,True),(2,False),(3,True)]
Just [(2,False)]
-}


equalShow :: Bool -> String
equalShow b = if b then "==" else "/="

pr :: (Show a, Foldable t) => t a -> IO ()
pr = mapM_ print

pr' :: Foldable t => t String -> IO ()
pr' = mapM_ putStrLn

-- todo: where are the lenses for NonEmpty?
-- just use N.tail and N.head! dont need this stuff unless you are changing stuff!
_tail1 :: Lens' (NonEmpty a) [a]
_tail1 asfb (x :| as) = (x :|) <$> asfb as

-- dude this is an Iso [nope: cos we lose information
-- not a lens:cos need to change all the 'a' in NonEmpty to 'b'
-- _head1' :: Lens (NonEmpty a) (NonEmpty b) a b
-- _head1' afb (a :| as) = (:| as) <$> afb a

-- allows us to change types!!
_head1' :: Traversal (NonEmpty a) (NonEmpty b) a b
_head1' afb (a :| as) = (:|) <$> afb a <*> traverse afb as

_cons1' :: Iso (NonEmpty a) (NonEmpty b) (a, [a]) (b, [b])
_cons1' = iso (N.head &&& N.tail) (uncurry (:|))

-- this is useful cos we can change types
_snoc1' :: Iso (NonEmpty a) (NonEmpty b) ([a], a) ([b], b)
_snoc1' = iso (N.init &&& N.last) (\(bs,b) -> N.fromList (bs <> [b]))

-- this is ok -- cant change types -- N.head
_head1 :: Lens' (NonEmpty a) a
_head1 afb (a :| x) = (:| x) <$> afb a

_snoc1 :: Lens' (NonEmpty a) a
_snoc1 afb (a :| x) = (:| x) <$> afb a
{-
>(1 :| [2..4]) & _head1' %~ succ
2 :| [3,4,5]
>(1 :| [2..4]) & _head1' %~ show . succ
"2" :| ["3","4","5"]
-}

-- | PLinear error messages
data Linearity =
    OneMatch !Int -- ^ has id of the one match
  | MoreThanOneMatch ![Int] -- ^ two or more predicates match the same value
  | ErrorsInPred ![Int] -- ^ found an exception running these predicate
  | NoMatch !Int  -- ^ a value that matches no predicate. ok if 'Loose'
  | MissingPredicates -- ^ no predicates specified
  deriving (Show, Eq)

linearityFilter :: Rigid -> Linearity -> Bool
linearityFilter noextravalues =
  \case
     OneMatch {} -> False
     MoreThanOneMatch {} -> True
     ErrorsInPred {} -> True
     NoMatch {} -> noextravalues == Rigid
     MissingPredicates {} -> noextravalues == Rigid

-- | yields description text and function associated with 'CmpOperator'
ccmp :: Ord a => CmpOperator -> (String, a -> a -> Bool)
ccmp = \case
          Lt -> ("<",  (<))
          Le -> ("<=", (<=))
          Ge -> (">=", (>=))
          Gt -> (">",  (>))
          Eq -> ("==", (==))
          Ne -> ("/=", (/=))

-- just looks at adjacent elements but good enough -- makes sense for eq and ne so leave as is
-- abczde has only 'd' as not sorted
-- | see 'POrder'. compares adjacent values using the operator
isSorted :: Ord a => CmpOperator -> [a] -> [(Bool, a)]
isSorted _ [] = []
isSorted c z@(a:as) =  (True, a) : zipWith (\x y -> (snd (ccmp c) x y, y)) z as

isSortedEq :: Eq a => Bool -> [a] -> [(Bool, a)]
isSortedEq _ [] = []
isSortedEq b z@(a:as) =  (True, a) : zipWith (\x y -> (b == (x == y), y)) z as

-- | string type conversions used by 'PString' and 'PDist'
class Show a => SConv a where
  -- | compare two values using 'Case'
  scompare :: Case -> StringOperator -> a -> a -> Bool
  -- | display quoted value
  sdisp :: a -> String
  sdisp = dquoted . sstring
  -- | convert to String
  sstring :: a -> String

instance a ~ Char => SConv [a] where
  scompare ci sop =
    let fn = case sop of
              SNone -> (==)
              SPrefix -> isPrefixOf
              SInfix -> isInfixOf
              SSuffix -> isSuffixOf
    in on fn (case ci of CI -> map toLower; CS -> id)
  sstring = id

instance SConv Text where
  scompare ci sop =
    let fn = case sop of
              SNone -> (==)
              SPrefix -> T.isPrefixOf
              SInfix -> T.isInfixOf
              SSuffix -> T.isSuffixOf
    in on fn (case ci of CI -> T.toLower; CS -> id)
  sstring = T.unpack

instance SConv Value where
  scompare ci sop (String s) (String t) = scompare ci sop s t
  scompare _ _ _ _ = False
  sdisp = show
  sstring (String s) = T.unpack s
  sstring o = show o

instance SConv BS8.ByteString where
  scompare ci sop =
    let fn = case sop of
              SNone -> (==)
              SPrefix -> BS8.isPrefixOf
              SInfix -> BS8.isInfixOf
              SSuffix -> BS8.isSuffixOf
    in on fn (case ci of CI -> BS8.map toLower; CS -> id)
  sstring = BS8.unpack

instance SConv BL8.ByteString where
  scompare ci sop =
    let fn = case sop of
              SNone -> (==)
              SPrefix -> BL8.isPrefixOf
              SInfix -> on BS8.isInfixOf BL8.toStrict
              SSuffix -> BL8.isSuffixOf
    in on fn (case ci of CI -> BL8.map toLower; CS -> id)
  sstring = BL8.unpack

dquoted :: String -> String
dquoted = (<> "\"") . ("\"" <>)

data CmpOperator = Lt | Le | Ge | Gt | Eq | Ne deriving Eq

instance Show CmpOperator where
  show = fst . ccmp @()  -- need to lock it down to some Ord

data StringOperator = SNone | SPrefix | SInfix | SSuffix deriving (Show, Eq)

fromStringOperator :: StringOperator -> String
fromStringOperator =
  \case
    SNone -> "=="
    SPrefix -> "`isPrefixOf`"
    SInfix -> "`isInfixOf`"
    SSuffix -> "`isSuffixOf`"

showStringOperator :: StringOperator -> String -> String -> String
showStringOperator sop s1 s2 =
  let o = " " <> fromStringOperator sop <> " "
  in case sop of
    SNone -> s1 <> o <> s2
    _ -> s2 <> o <> s1

-- | predicates can return true false or an exception
data BoolP =
    FailP (NonEmpty String)
  | FalseP
  | TrueP
  deriving (Data, Show,Eq)

_FailP :: Prism' BoolP (NonEmpty String)
_FailP = prism' FailP $ \case
                         FailP s -> Just s
                         _ -> Nothing

_FalseP :: Prism' BoolP ()
_FalseP = prism' (const FalseP) $
            \case
               FalseP -> Just ()
               _ -> Nothing

_TrueP :: Prism' BoolP ()
_TrueP = prism' (const TrueP) $
            \case
               TrueP -> Just ()
               _ -> Nothing

-- | BoolP uses conjunction.
instance Semigroup BoolP where
  FailP e <> FailP e1 = FailP (e <> e1)
  FailP e <> _ = FailP e
  _ <> FailP e1 = FailP e1
  TrueP <> TrueP = TrueP
  FalseP <> _ = FalseP
  _ <> FalseP = FalseP

instance Monoid BoolP where
  mempty = TrueP

-- | used by external applications to hold results of a predicate result
data BoolPE = BoolPE { _peBoolP :: BoolP -- ^ holds the result of running the predicate
                     , _peShowBool :: Bool -- ^ show the result above or skip it in the case of debugging. see 'mkNodeDebug'
                     , _peStrings :: [String] -- ^ optional strings to include in the results
                     } deriving (Show, Eq, Data)

peBoolP :: Lens' BoolPE BoolP
peBoolP afb s = (\b -> s { _peBoolP = b }) <$> afb (_peBoolP s)

peShowBool :: Lens' BoolPE Bool
peShowBool afb s = (\b -> s { _peShowBool = b }) <$> afb (_peShowBool s)

peStrings :: Lens' BoolPE [String]
peStrings afb s = (\b -> s { _peStrings = b }) <$> afb (_peStrings s)

instance Semigroup BoolPE where
  BoolPE a b c <> BoolPE a1 b1 c1 = BoolPE (a <> a1) (b || b1) (c <> c1)

type TT = Tree BoolPE

type PE = Either PredE PredExceptionE

-- | error predicate when predicate is false. used by external callers
data PredE = PredE { _peErr :: !String
                   , _peInput :: !String
                   , _peLogs :: [String]
                   } deriving (Generic, Eq)

instance Show PredE where
  show (PredE e i j) =
    mconcat
    ["PredE err="
    ,take 2000 e
    ,"\n"
    ,"input="
    ,take 100 i
    ,intercalate "\n" j]

-- | error predicate when predicate has an exception. used by external callers
data PredExceptionE = PredExceptionE { _peExceptionE :: NonEmpty String
                   , _peErrE :: !String
                   , _peInputE :: !String
                   , _peLogsE :: [String]
                   } deriving (Generic, Eq)

instance Show PredExceptionE where
  show (PredExceptionE excs e i j) =
    mconcat
    ["PredExceptionE excs="
    ,intercalate " | " (toList excs)
    ,"\nerr="
    ,take 2000 e
    ,"\ninput="
    ,take 100 i
    ,"\n"
    ,intercalate "\n" (toList j)]


_BoolP :: Prism' BoolP Bool
_BoolP = prism' (bool FalseP TrueP) $ \case
                                        FalseP -> Just False
                                        TrueP -> Just True
                                        FailP {} -> Nothing

liftBool2 :: (Bool -> Bool -> Bool) -> BoolP -> BoolP -> BoolP
liftBool2 f b b1 = maybe (b <> b1) (_BoolP #) (on (liftA2 f) (^? _BoolP) b b1)

impl :: Bool -> Bool -> Bool
impl p q = not p || q

--type BoolP = Either (NonEmpty String) Bool

getBool :: TT -> BoolP
getBool = view boolP

boolP :: Lens' TT BoolP
boolP = root . peBoolP

toNodeString :: POpts -> BoolPE -> String
toNodeString o (BoolPE pb b ss) =
  (if b then showBoolP o pb <> " " else mempty) <> displayMessages ss

showBoolP :: POpts -> BoolP -> String
showBoolP o =
  \case
    b@(FailP es@(_ :| _)) | length es == 1 -> "[" <> colorMe o b "Error" <> fn <> "]"
                          | otherwise -> "[" <> colorMe o b "Errors" <> "(" <> show (length es) <> ")" <> fn <> "]"
            where fn = let r = displayMessages $ toList es
                       in if null r then "" else " " <> r
    b@TrueP -> colorMe o b (show b <> " ")
    b@FalseP -> colorMe o b (show b)

-- | colors the result of the predicate based on the current color palette
colorMe :: POpts -> BoolP -> String -> String
colorMe o b s =
  let (_, PColor f) = oColor o
  in f b s

-- | italics dont work but underline does
-- | color palettes
color0, color1, color2, color3, color4 :: (String, PColor)
color0 = ("color0", PColor $ flip const)

color1 =
  ("color1",) $ PColor $ \case
    FailP {} -> bgColor Magenta
    FalseP -> bgColor Red
    TrueP -> bgColor Green

color2 =
  ("color2",) $ PColor $ \case
    FailP {} -> bgColor Magenta
    FalseP -> bgColor Red
    TrueP -> bgColor White

color3 =
  ("color3",) $ PColor $ \case
    FailP {} -> bgColor Blue
    FalseP -> color Red
    TrueP -> color White

color4 =
  ("color4",) $ PColor $ \case
    FailP {} -> bgColor Cyan
    FalseP -> color Red
    TrueP -> color Green

showBoolPSimple :: BoolP -> String
showBoolPSimple b = maybe "FailP" show (b ^? _BoolP)

displayMessages :: [String] -> String
displayMessages es =
  case filter (not . all isSpace) es of
    [] -> ""
    z -> intercalate " | " z

newtype PColor = PColor { unPColor :: BoolP -> String -> String }
--instance ToExpr PColor where
--  toExpr _ = Lst []

-- | customizable options
data POpts = POpts { oShowA :: Maybe Int -- ^ length of data to display for 'showA'
                   , oMaxElements :: !Int -- ^ maximum number of elements to dispay
                   , oDebug :: !Int  -- ^ debug level
                   , oDisp :: Disp -- ^ how to display the tree orientation and unicode etc
                   , oHide :: !Int -- ^ hides one layer of a tree
                   , oColor :: !(String, PColor) -- ^ color palette used
                   } -- deriving G.Generic

data Disp = NormalDisp | Unicode deriving (Show, Eq)

instance Show POpts where
  show opts =
    "POpts: showA=" <> show (oShowA opts)
    <> " maxElements=" <> show (oMaxElements opts)
    <> " debug=" <> show (oDebug opts)
    <> " disp=" <> show (oDisp opts)
    <> " hide=" <> show (oHide opts)
    <> " color=" <> show (fst (oColor opts))
{-
>prettyEditExpr $ ediff o1 o2
POpts
  {oColor = _X_ "color1" [],
   oDebug = -1 +2,
   oDisp = NormalDisp,
   oHide = 0,
   oMaxElements = 20,
   oShowA = Just -120 +200}
-}

diffOpts :: POpts -> POpts -> [String]
diffOpts p1 p2 =
  let fn :: (Show a, Eq a) => String -> a -> a -> Maybe String
      fn s x y | x==y = Nothing
               | otherwise = Just (s <> ": " <> show x <> "/=" <> show y)
  in mapMaybe (\z -> z p1 p2) -- flip ($ 1) 2
    [ on (fn "showA") oShowA
    , on (fn "maxElements") oMaxElements
    , on (fn "debug") oDebug
    , on (fn "disp") oDisp
    , on (fn "hide") oHide
    , on (fn "color") (fst . oColor)
    ]

defOpts :: POpts
defOpts = o0

o0 :: POpts
o0 = POpts
    { oShowA = Just 110
    , oMaxElements = 5
    , oDebug = 0
    , oDisp = NormalDisp
    , oHide = 0
    , oColor = color1
    }

colorMap :: Map String PColor
colorMap = M.fromListWith (error "dude") [color0, color1, color2, color3, color4]

o1 :: POpts
o1 = defOpts { oDebug = 1, oShowA = Just 120, oMaxElements = 10 }

o2 :: POpts
o2 = defOpts { oDebug = 2, oShowA = Just 200, oMaxElements = 20 }

o3 :: POpts
o3 = defOpts { oDebug = 4, oShowA = Just 400, oMaxElements = 30 }

defh, defu :: POpts
defh = o1
defu = setu o1


{-
addHide :: POpts -> Int -> POpts
addHide o i = o { oHide = max i (oHide o + i) }

subHide :: POpts -> Int -> POpts
subHide o i = o { oHide = min 0 (oHide o - i) }

unhide :: POpts -> POpts
unhide o = o { oHide = 0 }
-}
seta :: Int -> POpts -> POpts
seta w o = o { oShowA = Just w }

setm :: Int -> POpts -> POpts
setm x o = o { oMaxElements = x }

setd :: Int -> POpts -> POpts
setd v o = o { oDebug = v }

setu :: POpts -> POpts
setu o = o { oDisp = Unicode }

setc :: (String, PColor) -> POpts -> POpts
setc pc o = o { oColor = pc }

setc0, setc1, setc2, setc3, setc4 :: POpts -> POpts
setc0 o = o { oColor = color0 }
setc1 o = o { oColor = color1 }
setc2 o = o { oColor = color2 }
setc3 o = o { oColor = color3 }
setc4 o = o { oColor = color4 }

showLit :: POpts -> Int -> String -> String -> String
showLit o i s a =
  if oDebug o >= i then
    let f n = let ss = take n a
              in ss <> (if length ss==n then " ..." else "")
    in maybe "" (\n -> s <> f n) (oShowA o)
  else ""

showA :: Show a => POpts -> Int -> String -> a -> String
showA o i s a = showLit o i s (show a)

mkNode, mkNodeDebug :: (BoolP, [String]) -> Forest BoolPE -> TT
mkNode (x, y) = Node (BoolPE x True y)
mkNodeDebug (x, y) = Node (BoolPE x False y)

toProxy :: Tagged s a -> Proxy s
toProxy = const Proxy

mkBool :: BoolP -> [String] -> BoolPE
mkBool b = BoolPE b True

mkfail :: String -> BoolPE
mkfail e = mkfail' e []

mkfail' :: String -> [String] -> BoolPE
mkfail' e = BoolPE (FailP (e :| [])) True

addMessagePre :: String -> TT -> TT
addMessagePre = addMessagesPre . (:[])

addMessagesPre :: [String] -> TT -> TT
addMessagesPre ss tt = tt & root . peStrings %~ (ss <>)

addError :: TT -> String -> TT
addError tt s = tt & boolP . _FailP %~ (s N.<|)

showRange :: (Ord a, Show a) => a -> a -> String
showRange a1 a2 =
  case compare a1 a2 of
    GT -> showRange a2 a1
    LT -> "`elem` [" <> show a1 <> ".." <> show a2 <> "]"
    EQ -> "== " <> show a1

showElem :: (Foldable t, Show a) => POpts -> t a -> String
showElem opts = showElemImpl opts . toList

showIElem :: (FoldableWithIndex i f, Show i, Show a) => POpts -> f a -> String
showIElem opts = showElemImpl opts . itoList

showElemImpl :: Show a => POpts -> [a] -> String
showElemImpl opts as
  | length as <= 2 * oMaxElements opts = show as
  | otherwise = "["
               <> intercalate ", " (map show (take (oMaxElements opts) as))
               <> ".."
               <> intercalate ", " (map show (drop (length as - oMaxElements opts) as))
               <> "]"

prtTT :: POpts -> TT -> IO ()
prtTT o = prtImpl o . fmap (toNodeString o)

prtImpl :: POpts -> Tree String -> IO ()
prtImpl = (putStrLn .) . showImpl

showImpl :: POpts -> Tree String -> String
showImpl o = ("\n" <>) . case oDisp o of
                           Unicode -> TV.showTree
                           NormalDisp -> drawTree

{-
ppEditTree :: (a -> PP.Doc) -> Edit (EditTree a) -> PP.Doc
ppEditTree pp = PP.sep . ppEdit
  where
    ppEdit (Cpy tree) = [ ppTree' tree ]
    ppEdit (Ins tree) = [ PP.char '+' PP.<> ppTree' tree ]
    ppEdit (Del tree) = [ PP.char '-' PP.<> ppTree' tree ]
    ppEdit (Swp a b) =
        [ PP.char '-' PP.<> ppTree' a
        , PP.char '+' PP.<> ppTree' b
        ]

    ppTree' (EditNode x []) = pp x
    ppTree' (EditNode x xs) = PP.parens $ PP.hang (pp x) 2 $
       PP.sep $ concatMap ppEdit xs
-}

unicode :: POpts -> POpts
unicode o = o { oDisp = Unicode }

horizontal :: POpts -> POpts
horizontal o = o { oDisp = NormalDisp }

formatList :: forall x z . Show x => POpts -> [((Int, x), z)] -> String
formatList opts = unwords . map (\((i, a), _) -> "(i=" <> show i <> showA opts 0 ", a=" a <> ")")

isTruncated :: POpts -> [a] -> Bool
isTruncated opts = (> 2 * oMaxElements opts) . length

-- msg is only used for an exception: up to the calling programs to deal with ading msg to good and bad
evalBinStrict :: String
                 -> (Bool -> Bool -> Bool)
                 -> TT -> TT
                 -> TT
evalBinStrict s fn ll rr =
  [ll, rr] & case (getBool ll,getBool rr) of
       (l@FailP {}, r@FailP {}) -> mkNode (l <> r, [s <> " (b)"])
       (l@FailP {}, _) -> mkNode (l, [s <> " (l)"])
       (_, r@FailP {}) -> mkNode (r, [s <> " (r)"])
       (b, b1) -> mkNode (liftBool2 fn b b1, [s])

splitAndP :: Show x =>
                    POpts
                    -> [String]
                    -> [((Int, x), TT)]
                    -> Either TT ([((Int, x), TT)], [((Int, x), TT)])
splitAndP opts msgs ts = -- could do isn't _BoolP
-- uses a typesafe Map to hold the values
  let cmap = toCMap' (^. _2 . boolP) ts
  in case getC (FailP ("" :| [])) cmap of
       excs@(e:_) -> Left $ mkNode (getBool (snd e), msgs <> ["excs=" <> show (length excs) <> " " <> formatList opts [e]]) (map fixit ts)
       _ -> Right (getC FalseP cmap, getC TrueP cmap)

fixit :: ((Int, x), TT) -> TT
fixit ((i, _), Node r xs) =
        Node (r & peStrings %~ \case
                                  [] -> ["i=" <> show i]
                                  w:ws -> ("i=" <> show i <> ": " <> w): ws) xs

orderImpl :: Show b =>
                   POpts
                   -> [(Bool, b)]
                   -> ([((Int, b), TT)],
                       (Maybe ((Int, b), TT), String))
orderImpl opts xs =
  let (_, bads) = partition (fst.snd) (zip [0::Int ..] xs)
      ts = zipWith (\i (b, a) -> ((i, a), mkNode (_BoolP # b, [showA opts 0 "" a]) [])) [0::Int ..] xs
  in (ts,) $ case bads of
                 [] -> (Nothing, "")
                 (i, (_, a)):_ -> (Just (ts!!i), " errs=" <> show (length bads) <> " " <> show (i, a))

partitionImpl2 :: (Show a2, Show a1) =>
                       POpts
                       -> String
                       -> [((Int, x), TT)]
                       -> ([(a2, b1)], [(a1, b2)])
                       -> TT
                       -> TT
partitionImpl2 opts nm ts (bads, goods) ll =
    let msgl = case bads of
                [] -> []
                b:_ -> ["lefts=" <> show (length bads) <> " " <> show (fst b)]
        msgr = case goods of
                [] -> []
                g:_ -> ["rights=" <> show (length goods) <> " " <> show (fst g)]
    in mkNode (getBool ll, [nm] <> msgl <> msgr)
             ([
              mkNode (getBool ll, [nm <> " Predicate"]) [ll]
              ] <>
              [mkNodeDebug (TrueP, [nm <> " debugging info "]) (map fixit ts) | oDebug opts > 1]
             )

breakImpl2 :: Show a2 =>
                       POpts
                       -> String
                       -> [((Int, x), TT)]
                       -> ([(a1, b2)], [(a2, b1)])
                       -> TT
                       -> TT
breakImpl2 opts nm ts (bads, goods) ll =
    let msgl = ["lefts=" <> show (length bads)]
        msgr = case goods of
                [] -> []
                g:_ -> ["rights=" <> show (length goods) <> " pivot=" <> show (fst g)]
    in mkNode (getBool ll, [nm] <> msgl <> msgr)
             ([mkNode (getBool ll, [nm <> " Predicate"]) [ll]]
               <>
              [mkNodeDebug (TrueP, [nm <> " debugging info "]) (map fixit ts) | oDebug opts > 1]
              )

{-
instance Monoid a => Monoid (Tree a) where
  mempty = Node mempty mempty
  mappend (Node a as) (Node b bs) = Node (a `mappend` b) (as <> bs)
instance Monoid a => Monoid (Tree a) where
  mempty = return mempty
  mappend n n1 = n >>= \a -> n1 >>= \a1 -> return (a `mappend` a1)
-}

-- | lifts a Maybe to an Either. used by 'PMorph' 'pmorph' 'pmaybeT' 'pmaybeF'
maybeToEither :: (a -> Maybe b) -> (a -> Either a b)
maybeToEither f a = maybe (Left a) Right (f a)

{-
Data.List.groupBy is seriously messed up: should be able to do groupBy (<=) but does a span on first element
as opposed to comparing consecutive elements against each other
checks everything relative to first element until something <= comes along and then adds a group
ie uses span to grab the largest group
-}
-- | better version of 'Data.List.groupBy' as it checks each adjacent element
--
--   >>> groupBy' (<) [1,4,5,2,3,1]
--   [[1,4,5],[2,3],[1]]
--
--   >>> groupBy (<) [1,4,5,2,3,1]
--   [[1,4,5,2,3],[1]]
--
groupBy' :: (a -> a -> Bool) -> [a] -> [[a]]
groupBy' _ [] = []
groupBy' p (a:as) =
  let xs = (False,a) : zipWith (\x y -> (p x y,y)) (a:as) as
      f = \case
            [] -> Nothing
            (b,a'):ws | b -> error "groupBy' found b=True!!"
                      | otherwise -> let (m,n) = span fst ws
                                     in Just (a':map snd m,n)
  in unfoldr f xs

-- | use by 'pgroupBy' for grouping. between i and j is 'EQ' and outside of that is 'LT' or 'GT'
between :: (Show a, Ord a) => a -> a -> a -> Ordering
between i j = fst . between' i j

-- handles all conditions: ie i==j then treat as == else range
-- allow i and j to be reversed
between' :: (Show a, Ord a) => a -> a -> a -> (Ordering, String)
between' i j a
  | i > j = between' j i a -- reversed
  | otherwise =
  if | a<i -> (LT, "< " <> show i <> " (Under)")
     | a>j -> (GT, "> " <> show j <> " (Over)")
     | i == j -> (EQ, "== " <> show i)
     | otherwise -> (EQ, "== [" <> show i <> ".." <> show j <> "]")

-- | case insensitive vs case sensitive
data Case = CI | CS deriving (Show,Eq)

-- | used 'plinearDist'
dist :: Case -> String -> String -> Int
dist = on (levenshteinDistance defaultEditCosts) . doCase

doCase :: Case -> String -> String
doCase CI = map toLower
doCase CS = id

-- | used by 'PLinear' rigid means each value has to match one of the predicates
data Rigid = Rigid | Loose deriving (Show, Eq)

-- | used by 'PMsg' for inlining or nesting messages
data Inline = Inline | Nested deriving (Show, Eq)

stringAp :: String -> String -> String
stringAp x s = x <> (if null s then "" else " ") <> s

-- | tokenizes but is not precise as 'interperseP' where you can allow only 1 delimiter
tokenizeS, tokenizeS1 :: String -> [String]
tokenizeS = split (whenElt isSpace)
tokenizeS1 = split (dropDelims $ whenElt isSpace)

-- realistically having a dedicated PISect* makes little sense cos can just call pfn isect or isectList
-- but leave in to see how it can be used
-- | intersection of two strings with left only, both and right only
isect :: Ord a => ([a], [a]) -> ([a],[a],[a])
isect (as, bs) =
  let m = M.fromListWith (<>) $ map (,This (Sum 1)) as <> map (,That (Sum 1)) bs
  in flip M.foldMapWithKey m $ \k t -> case join bimap getSum t of
                                  This i -> (replicate i k, [], [])
                                  That j -> ([],[],replicate j k)
                                  These i j -> (replicate (i-j) k, replicate (min i j) k, replicate (j-i) k)

-- no value: _1 _2 _3 are indices
--isectMap :: Ord a => [a] -> [a] -> Map Ordering [a]
--isectMap as bs = let (x,y,z) = isect as bs in M.fromList [(LT, x), (EQ, y), (GT, z)]


isectN :: Ord a => ([a],[a]) -> ([a],[a]) -> ([a],[a])
isectN (b,g) (b1,g1) =
  let (x,y,z) = isect (g,g1)
  in (b<>x<>z<>b1,y)

isectList :: Ord a => [[a]] -> ([a],[a])
isectList = foldr1 isectN . map ([],)

const2 :: a -> x -> y -> a
const2 = const . const

beforeafter :: These b1 b2 -> String
beforeafter = mergeTheseWith (const "-") (const "+") (const2 "-+")

dispIJ :: These Int Int -> String
dispIJ = these (\i -> "{" <> show i <> ",}")
               (\j -> "{," <> show j <> "}")
               (\i j -> if i==j then "{" <> show i <> "}"
                        else "{" <> show i <> "," <> show j <> "}")

-- how much consumed
-- use foldr f id
regexsToTT :: (Show a, Show b) => POpts -> These Int Int -> [a] -> [(b,[a],[a])] -> (Either [String] [String], TT)
regexsToTT opts thij as xs =
  let ns = flip imap xs $ \i (b,before,after) -> mkNodeDebug (TrueP, ["i=" <> show i, showA opts 1 "b=" b, showA opts 2 "used=" before, showA opts 2 "remaining=" after]) []
      ii = these id (const 0) const thij
      msgs | length xs >= ii = Right $ ("matched all(" <> show (length xs) <> ")") : [showA opts 1 "leftovers=" as]
           | otherwise = Left ["only matched " <> show (length xs) <> " of " <> dispIJ thij, showA opts 1 "leftovers=" as]
  in (msgs, mkNodeDebug (TrueP, either id id msgs) ns)
