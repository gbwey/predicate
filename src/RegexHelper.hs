{-# OPTIONS -Wall #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DataKinds #-}
module RegexHelper where
import Text.Regex.Applicative
import Text.Regex.Applicative.Common
import Data.Char
import Data.Function
import Data.Ratio
import Data.List
import Data.Foldable
import Data.Maybe
import Control.Monad
import Data.Time
import Data.These
import Control.Lens
import qualified Data.Vinyl.Recursive as WR
import qualified Data.Vinyl as W
import Data.Vinyl
import Data.Vinyl.TypeLevel
import qualified Data.Vinyl.Functor as W
import Data.Proxy
import Data.List.NonEmpty (NonEmpty(..))

-- | regex flag
data RType = RFirst -- ^ find first matching result
           | RLong  -- ^ find longest matching result
           | RShort -- ^ find shortest matching result
           deriving (Show,Eq)

rprefix :: RType -> RE s a -> [s] -> Maybe (a, [s])
rprefix = \case
            RFirst -> findFirstPrefix
            RLong -> findLongestPrefix
            RShort -> findShortestPrefix

rinfix :: RType -> RE s a -> [s] -> Maybe ([s], a, [s])
rinfix = \case
            RFirst -> findFirstInfix
            RLong -> findLongestInfix
            RShort -> findShortestInfix

------------------------------------------- start regex stuff -----------------------

-- | match a non space token
token :: RE Char String
token = some (psym (not . isSpace))

-- delimit on spaces
-- use few so that subsequent parsers get a chance else will grab everything
-- | split a string into non space tokens dropping spaces
tokenizeSpaces :: RE Char [String]
tokenizeSpaces = catMaybes <$> few (Just <$> token <|> Nothing <$ spaces)

-- a bit loose cos allows multiple delimiters and no way to stop that cos lhs wont pick up stuff
-- use intersperseNP for more exactness ie matches exact number and fixed delimiter instead of allowing multiple delimiters
--tokenize' :: (a -> Bool) -> RE a [[a]]
--tokenize' p = catMaybes <$> few (Just <$> some (psym (not . p)) <|> Nothing <$ some (psym p))

-- | tokenize using a single delimiter. see 'intersperseP'
tokenize1 :: (a -> Bool) -> RE a [[a]]
tokenize1 p = intersperseP (psym p) (some (psym (not . p)))

-- | tokenize using one or more delimiters. see 'intersperseP'
tokenizeN :: (a -> Bool) -> RE a [[a]]
tokenizeN p = intersperseP (some (psym p)) (some (psym (not . p)))

oneOf :: [RE s a] -> RE s a
oneOf = asum

oneOfChars :: String -> RE Char Char
oneOfChars = psym . flip elem

notOneOfChars :: String -> RE Char Char
notOneOfChars = psym . flip notElem

{-
-- crap versions
intersperseP' :: Monoid m => RE s x -> [RE s m] -> RE s m
intersperseP' _ [] = pure mempty
intersperseP' x ps = foldr1 (\a b -> mappend <$> a <* x <*> b) ps

intersperseFixedP :: Int -> RE s x -> RE s a -> RE s [a]
intersperseFixedP n d p = intersperseP' d (replicate n (pure <$> p))
-}

-- ok this is better cos will do as many matches as it can so always succeeds instead of limited number
-- the delimiter will match exactly: sym '.' vs some (sym '.')
-- | tokenize by first regex and dump the delimiters
intersperseP :: RE s x -> RE s a -> RE s [a]
intersperseP = intersperseP' few
--intersperseP d p = ((:) <$> p <*> few (d *> p)) <|> pure []

-- matches at least n!
-- cant be less than 1 cos will always try to run 'p' but otherwise makes no sense
-- problem is that it will match but there could be more matches: so would need to run and check no remainder
-- or run intersperseP and count the number
-- | tokenize exactly n tokens
intersperseNP :: Int -> RE s x -> RE s a -> RE s [a]
intersperseNP = intersperseP' . replicateM . pred

-- | need to force failure if no match! ie empty not pure () as we had before
intersperseP' :: Alternative f => (f b -> f [b]) -> f a -> f b -> f [b]
intersperseP' f d p = ((:) <$> p <*> f (d *> p)) <|> empty

-- | match at least i regexs ie re{i,}
widthMin :: Int -> RE s a -> RE s [a]
widthMin i p | i>=0 = liftA2 (<>) (replicateM i p) (few p)
             | otherwise = error ("invalid width: i=" ++ show i)

-- | match at most i regexs ie re{,i}
widthMax :: Int -> RE s a -> RE s [a]
widthMax = width . (0,)

widthExact :: Int -> RE s a -> RE s [a]
widthExact = width . join (,)

-- a bit gack! but works:replicate j down to i times
-- | match between i and j regexs ie re{i,j}
width :: (Int,Int) -> RE s a -> RE s [a]
width (i, j) p | i>=0 && i<=j =
 asum (map (`replicateM` p) [j,j-1 .. i])
                 | otherwise = error $ "invalid width " ++ show (i,j) -- needs monad for failMsg

-- | match uppercase and zero or more lower case letters
capitalWord :: RE Char String
capitalWord = (:)
          <$> psym isUpper
          <*> many (psym isLower)

-- case insensitive match on a character
symCI :: Char -> RE Char Char
symCI c = psym (on (==) toLower c)

-- case insenstive match on a string
stringCI :: String -> RE Char String
stringCI = traverse symCI

--betw :: RE [s] x -> RE [s] y -> RE [s] a -> RE [s] a
betw :: Applicative f => f a1 -> f b -> f a2 -> f a2
betw o c p = o *> p <* c

--digit :: RE Char Int
--digit = digitToInt <$> psym isDigit

-- | match on a signed integral number
int' :: Num a => RE Char a
int' = (*) <$> sign <*> unsigned

-- | match on a signed integral number
unsigned :: Num a => RE Char a
unsigned = fromIntegral . foldl' (\x a -> 10*x+digitToInt a) 0 <$> some (psym isDigit)

-- | monomorphic version of 'int''
int :: RE Char Int
int = int'

sign :: Num a => RE Char a
sign = 1 <$ sym '+' <|> (-1) <$ sym '-' <|> pure 1

sign' :: Num a => RE Char (a -> a)
sign' = id <$ sym '+' <|> negate <$ sym '-' <|> pure id

-- | match on a signed double
double :: RE Char Double
double = fromRational <$> ratio

-- | match on a signed rational
ratio :: RE Char Rational
ratio = f <$> sign @Integer
          <*> unsigned @Integer
          <*> (sym '.' *> some (psym isDigit) <|> pure "0")
      where f s n d = fromIntegral s*(abs (fromIntegral n) + read @Integer d % 10 ^ length d)

-- | match on a space
space :: RE Char Char
space = psym isSpace

spaces, spaces1 :: RE Char String
spaces = many space
spaces1 = some space

-- | unquote a value
quoted :: RE Char String
quoted = betw (sym '"') (sym '"') (some (psym (/='"')))

-- | unparen a value
parened :: RE Char String
parened = betw (sym '(') (sym ')') (some (psym (`notElem` ['(',')'])))

braced :: RE Char String
braced = betw (sym '{') (sym '}') (some (psym (`notElem` ['{','}'])))

newLineP :: RE Char Char
newLineP = psym (`elem` ['\n','\r'])

newlines, newlines1 :: RE Char String
newlines = many newLineP
newlines1 = some newLineP

quote :: String -> String
quote = wrap "\"" "\""

wrap :: Semigroup c => c -> c -> c -> c
wrap c d = (c <>) . (<> d)

word :: RE Char String
word = some (psym isLetter)

dots, dots1 :: RE a [a]
dots = many anySym
dots1 = some anySym

dot :: RE a a
dot = anySym

dots' :: RE a [a]
dots' = few anySym

_d, _s, _w, _h, _D, _S, _W :: RE Char Char
_d = psym isDigit
_s = psym isSpace
_w = psym (\c -> isAlphaNum c || c=='_')
_h = psym isHexDigit
-- _w' = psym ((||) <$> isAlphaNum <*> (=='_'))  using reader applicative
-- _w'' = psym (and . sequenceA [isAlphaNum, (=='x')])

_D = psym (not . isDigit)
_S = psym (not . isSpace)
_W = psym (\c -> not (isAlphaNum c || c=='_'))


_d1, _w1, _s1, _h1 :: RE Char String
_d1 = (:[]) <$> psym isDigit
_s1 = (:[]) <$> psym isSpace
_w1 = (:[]) <$> psym (\c -> isAlphaNum c || c=='_')
_h1 = (:[]) <$> psym isHexDigit

--hexDigit :: Num a => RE Char a
--hexDigit = fromIntegral . digitToInt <$> psym isHexDigit

octDigit :: Num a => RE Char a
octDigit = fromIntegral . digitToInt <$> psym isOctDigit

binDigit :: Num a => RE Char a
binDigit = fromIntegral . digitToInt <$> psym isBinDigit

-- use decimal for regex applicative common cos classes with dec from decoding
--dec :: Num a => RE Char a
--dec = foldl' (\d i -> d*10 + i) 0 <$> some digit

hex :: Num a => RE Char a
hex = foldl' (\d i -> d*16 + i) 0 <$> some hexDigit

oct :: Num a => RE Char a
oct = foldl' (\d i -> d*8 + i) 0 <$> some octDigit

bin :: Num a => RE Char a
bin = foldl' (\d i -> d*2 + i) 0 <$> some binDigit

isBinDigit :: Char -> Bool
isBinDigit = flip elem ['0','1']
{-
runRegexsOLD :: [(RType, RE a b)] -> [a] -> [(b,[a],[a])]
runRegexsOLD = go
  where
  go [] _ = []
  go ((t,regex):rs) as =
      case rprefix t regex as of
        Nothing -> []
        Just (b,as') -> (b,take (length as - length as') as, as') : go rs as'

runRegexs :: NonEmpty (RType, RE a b) -> [a] -> [(b, [a], [a])]
runRegexs = foldr f (const [])
  where
      f (t, regex) k as =
          case rprefix t regex as of
            Nothing -> []
            Just (b,as') -> (b,take (length as - length as') as, as') : k as'
-}
runRegexs :: NonEmpty (RType, RE a b) -> [a] -> [(b, [a], [a])]
runRegexs = foldr f (const [])
  where
      f (t, regex) k as =
          case runRegexs1 (t,regex) as of
            Nothing -> []
            Just xs@(_,_,as') -> xs : k as'

runRegexs1 :: (RType, RE a b) -> [a] -> Maybe (b, [a], [a])
runRegexs1 (t, regex) as =
  case rprefix t regex as of
    Nothing -> Nothing
    Just (b,as') -> Just (b,take (length as - length as') as, as')

theseLR :: (c -> c -> c) -> (a -> c) -> (b -> c) -> These a b -> c
theseLR f l r = \case
  This i -> l i
  That j -> r j
  These i j -> f (l i) (r j)

theseLeft :: (a -> c) -> c -> These a b -> c
theseLeft l c = these l (const c) (\i _ -> l i)

theseRight :: (b -> c) -> c -> These a b -> c
theseRight r c = these (const c) r (\_ j -> r j)

runRegexN' :: These Int Int -> (RType, RE a b) -> [a] -> (Bool, [(b, [a], [a])])
runRegexN' thij rx as =
  let (ret,_) = runRegexN thij rx as
  in (,ret) $ theseLR (&&) (<=length ret) (>=length ret) thij

runRegexN :: These Int Int -> (RType, RE a b) -> [a] -> ([(b, [a], [a])], [a])
runRegexN thij rx | theseRight (<=0) False thij = ([],)
                  | otherwise = go 0 []
  where go n ret as =
          case runRegexs1 rx as of
            Nothing -> (ret,as)
            Just xs@(_,_,remn) -> case thij of
                                    That j | n+1>=j -> (ret<>[xs],remn)
                                    These _ j | n+1>=j -> (ret<>[xs],remn)
                                    _ -> go (n+1) (ret<>[xs]) remn


-- does no validation cos only applicative
-- parse a gregorian date yyyy-mm-dd -- or just use >readMaybe @Day "1999-12-19" even has error handling
gregorian :: RE Char Day
gregorian = fromGregorian
       <$> (read <$> widthExact 4 _d)
       <* sym '-'
       <*> (read <$> widthExact 2 _d)
       <* sym '-'
       <*> (read <$> widthExact 2 _d)

gregorian' :: RE Char Day
gregorian' = fromGregorian
       <$> unsigned
       <* sym '-'
       <*> unsigned
       <* sym '-'
       <*> unsigned

-- | parse an ipaddress
ipaddr :: Num a => RE Char (IP a)
ipaddr = IP <$> unsigned <* sym '.' <*> unsigned <* sym '.' <*> unsigned <* sym '.' <*> unsigned

-- | parse an ipaddress
ipaddr' :: RE Char (IP Int)
ipaddr' = IP <$> octetP <* sym '.' <*> octetP <* sym '.' <*> octetP <* sym '.' <*> octetP

octetP :: Read a => RE Char a
octetP = read <$> width (1,3) _d

data IP a = IP { _octet1 :: a, _octet2 :: a, _octet3 :: a, _octet4 :: a } deriving (Ord,Eq,Foldable)

instance (Read a,Ord a, Num a) => Read (IP a) where
  readsPrec _i s =  case findLongestPrefix ipaddr s of
                     Nothing -> []
                     Just (ip,xs) | isIPValid ip -> [(ip,xs)]
                                  | otherwise -> [(ip,"oops not quite right but what ever xs[" <> xs <> "]")]

instance Show a => Show (IP a) where
  show ip = "IP:" <> intercalate "." (ip ^.. folded . to show)

octet1, octet2, octet3, octet4 :: Lens' (IP a) a
octet1 afb (IP a b c d) = (\x -> IP x b c d) <$> afb a
octet2 afb (IP a b c d) = (\x -> IP a x c d) <$> afb b
octet3 afb (IP a b c d) = (\x -> IP a b x d) <$> afb c
octet4 afb (IP a b c d) = IP a b c <$> afb d

isIPValid :: (Ord a, Num a, Foldable f) => f a -> Bool
isIPValid ip = all ((>=0) <&&> (<=255)) $ ip ^.. folded

(<&&>) :: Applicative f => f Bool -> f Bool -> f Bool
(<&&>) = liftA2 (&&)

_IP :: (Num a, Ord a) => Prism' (a,a,a,a) (IP a)
_IP = prism' (\(IP a b c d) -> (a,b,c,d))
              (\xs@(a,b,c,d) -> if isIPValid (xs ^.. each) then Just (IP a b c d) else Nothing)

newtype WR w a = WR { unWR :: (a, w) }
instance Functor (WR w) where
  fmap f (WR (a, w)) = WR (f a, w)

instance Monoid w => Applicative (WR w) where
  pure a = WR (a, mempty)
  WR (ab, w1) <*> WR (a, w2) = WR (ab a, w1 `mappend` w2)

newtype ST1 w e s a = ST1 { unST1 :: s -> ([w], Either e (s, a)) }

instance Functor (ST1 w e s) where
  fmap f (ST1 g) = ST1 $ \s -> case g s of
                                 (w,Left e) -> (w,Left e)
                                 (w,Right (s', a)) -> (w,Right (s', f a))

instance Applicative (ST1 w e s) where
  pure a = ST1 $ \s -> (mempty, Right (s, a))
  ST1 sab <*> ST1 sa =
    ST1 $ \s -> case sab s of
                  (w,Left e) -> (w,Left e)
                  (w,Right (s', ab)) -> case sa s' of
                                          (w1,Left e) -> (w<>w1, Left e)
                                          (w1,Right (s'', a)) -> (w<>w1, Right (s'', ab a))

{-
newtype STR e s a = STR { unSTR :: s -> Either e (s, a) }
instance Functor (STR e s) where
  fmap f (STR g) = STR $ \s -> case g s of
                               Left e -> Left e
                               Right (s', a) -> Right (s', f a)
instance Applicative (STR e s) where
  pure a = STR $ \s -> Right (s, a)
  STR sab <*> STR sa = STR $ \s -> case sab s of
                                  Left e -> Left e
                                  Right (s', ab) -> case sa s' of
                                                     Left e -> Left e
                                                     Right (s'', a) -> Right (s'', ab a)
-}

data RXHolder a = RXHolder { _rx1 :: RE Char a, _rx2 :: a }

instance Show a => Show (RXHolder a) where
  showsPrec _ (RXHolder _ a) = (("a=" <> show a)<>)

toRXHolder :: Rec (RE Char) rs -> Rec RXHolder rs
toRXHolder = WR.rmap $ \r -> RXHolder r undefined

-- | attempts to run each regex inside a RXHolder record until all succeed or there is a failure to match
-- also records where the failure occured ie the column number and the field within the RXHolder record
evalRXHolder :: RecAll RXHolder rs Show => String -> Rec RXHolder rs -> ([RResult], Either String ((Int, String), Rec W.Identity rs))
evalRXHolder ss rc =
  flip unST1 (0, ss)
      $ rtraverse (\(W.Compose (W.Dict (RXHolder r _))) -> ST1 $ \(i,s) ->
  case findLongestPrefix r s of
    Nothing -> ([], Left s)
    Just (a,b) -> ([RResult i (show (RXHolder r a)) (take (length s-length b) s) b], Right ((i+1,b),W.Identity a))
      ) (WR.reifyConstraint (Proxy @Show) rc)

data RResult = RResult { rindex :: Int, rshow :: String, rused :: String, rremaining :: String } deriving (Show,Eq)
