{-
>encode $ object ["abc" A..= 13] & key "abc" . _Number %~ (+3)
"{\"abc\":16}"
it :: BL.ByteString

>encode [1,2,3]
"[1,2,3]"

>encode ("abc",True)
"[\"abc\",true]"

>encode ("abc",True) & nth 1 . _Bool %~ not
"[\"abc\",false]"

>encode ("abc",True) & nth 0 . _String <>~ "fred"
"[\"abcfred\",true]"

>encode ("abc",True) & nth 0 . _String <<>~ "fred"
("abcfred","[\"abcfred\",true]")
-}

{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ViewPatterns #-}
module JsonHelper where
import Data.Foldable ( Foldable(toList), forM_ )
import Control.Lens
import Control.Arrow
import Data.List ( intercalate )
import Data.Tree ( Tree(Node) )
import Data.List.NonEmpty (NonEmpty(..))
import qualified Data.List.NonEmpty as N
import qualified Data.Text as T
import Data.Text (Text)
import Data.Aeson ( Value(..) )
import Data.Aeson.Lens
import Data.Aeson.Encode.Pretty ( encodePretty )
import qualified Data.ByteString.Lazy.Char8 as BL8
import Data.HashMap.Strict (HashMap)
import qualified Data.HashMap.Strict as H
import Data.Scientific ( Scientific )
import qualified Data.Sequence as Seq
import qualified Control.Monad.State.Strict as S
import Control.Monad ( forM )
import qualified Formatting as F
import PredHelper
import Data.Data ( Data(toConstr) )
import Data.Function ( on )

-- | pretty print json
jprtPretty :: Value -> IO ()
jprtPretty = BL8.putStrLn . encodePretty

jprt :: POpts -> Value -> IO ()
jprt o = prtImpl o . fmap (showJDisp2a (\case [] -> "";z -> show z)) . jtree2

showJDisp2 :: (JDisp, [JPath]) -> (String, [JPath])
showJDisp2 (jd, js) =
  case jd of
   JArray -> ("[Array]", js)
   JObject -> ("[Object]", js)
   JKey k -> ("key=" <> show k, js)
   JValue v -> (show v, [])

showJDisp2a :: ([JPath] -> String) -> (JDisp, [JPath]) -> String
showJDisp2a f (showJDisp2 -> (a,b)) =
  F.formatToString (F.right 15 ' ' F.% "   " F.% F.string) a (f b)

jprtPrism :: POpts -> Value -> IO ()
jprtPrism o = prtImpl o . fmap (showJDisp2a showJPaths) . jtree2

jprth :: Value -> IO ()
jprth = jprt defh

jprtu :: Value -> IO ()
jprtu = jprt defu

jprtSimple :: POpts -> Value -> IO ()
jprtSimple o = prtImpl o . fmap (show . snd) . jtree

--jtree1 :: Value -> Tree (String, JDisp)
--jtree1 = fmap (first showJPaths) . jtree2

jtree2 :: Value -> Tree (JDisp, [JPath])
jtree2 v = jtree v <&> \x -> x & _2 . traverse  %~ either JPIndex (JPKey . T.unpack)

jtree :: Value -> Tree (JDisp, [Either Int Text])
jtree = fmap (second reverse) . go []
  where go ss =
          \case
            Array vs -> Node (JArray, ss) $ zipWith (\i v -> go (Left i:ss) v) [0::Int ..] (toList vs)
            Object hm -> Node (JObject, ss)
                           $ H.toList hm <&> \(k,v) -> Node (JKey (T.unpack k), Right k:ss) [go (Right k:ss) v]
            v -> Node (JValue v, ss) []

data JDisp = JObject | JArray | JKey String | JValue Value deriving (Show,Eq)

_JObject :: Prism' JDisp ()
_JObject = prism' (const JObject) $ \case
                                       JObject  -> Just ()
                                       _ -> Nothing

_JArray :: Prism' JDisp ()
_JArray = prism' (const JArray) $ \case
                                     JArray -> Just ()
                                     _ -> Nothing

_JKey :: Prism' JDisp String
_JKey = prism' JKey $ \case
                               JKey i -> Just i
                               _ -> Nothing

_JValue :: Prism' JDisp Value
_JValue = prism' JValue $ \case
                               JValue i -> Just i
                               _ -> Nothing

-- this is very good: just enough:coherent and no duplicates
-- jpath is index into a value: DO NOT GO DEEPER THAN THIS!
-- tried that and made things too difficult
data JPath = JPKey !String
           | JPIndex !Int
           | JPValue !Value
             deriving (Show,Eq)

_JPIndex :: Prism' JPath Int
_JPIndex = prism' JPIndex $ \case
                               JPIndex i -> Just i
                               _ -> Nothing

_JPKey :: Prism' JPath String
_JPKey = prism' JPKey $ \case
                               JPKey k -> Just k
                               _ -> Nothing

_JPValue :: Prism' JPath Value
_JPValue = prism' JPValue $ \case
                               JPValue v -> Just v
                               _ -> Nothing

showJPath :: JPath -> String
showJPath = \case
   JPIndex i -> "nth " ++ show i
   JPKey k -> "key " ++ show k
   JPValue (String _) -> "_String"
   JPValue (Number _) -> "_Number"
   JPValue (Bool _) -> "_Bool"
   JPValue Null -> "_Null"
   -- stop here else we cant prism anymore with key nth etc would need to use ix instead
   -- doesnt seem to be a problem leave them in!
   JPValue (Array _) -> "_Array"
   JPValue (Object _) -> "_Object"

--ok this is seriously cool: generates the lists of prism cmds to get to the given key
showJPaths :: [JPath] -> String
showJPaths = intercalate "." . map showJPath

showJPathsNE :: NonEmpty JPath -> String
showJPathsNE = showJPaths . reverse . toList

-- key is to drop the end JPath entry cos just repeats everything
-- gives you sets of keys for each hashmap so you can use PLinear on them
--jkeyLevels :: Value -> [([JPath], [Text])]
--jkeyLevels = map (first (reverse . N.tail)) . jvisitor (uncurry (*>) . ((^? _head1 . _JPValue) *** (^? _Object . to H.keys)))

jkeyLevels :: Value -> [([JPath], [Text])]
jkeyLevels js = jkeyLevels' js & traverse . _2 . traverse %~ fst

-- same as above but also gives you the values
jkeyLevels' :: Value -> [([JPath], [(Text, Value)])]
jkeyLevels' = map (first (reverse . N.tail)) . jvisitor (uncurry (*>) . ((^? _head1 . _JPValue) *** (^? _Object . to itoList)))

-- | visitor for Json
jvisitor :: ((NonEmpty JPath, Value) -> Maybe a) -> Value -> [(NonEmpty JPath, a)]
jvisitor p = toList . flip S.execState Seq.empty . go mempty
  where
  fff s ss v =
    case p (s:|ss, v) of
      Just a -> id %= (Seq.:|> (s:|ss,a))
      Nothing -> pure ()
  go ss v' = do
    fff (JPValue v') ss v'
    case v' of
      Array vs -> forM_ (zip [0..] (toList vs)) $ \(i,v) -> do
                    let s = JPIndex i
                    fff s ss v
                    go (s:ss) v
      Object hm ->
        forM_ (H.toList hm) $ \(k',v) -> do
          let s = JPKey (T.unpack k')
          fff s ss v
          go (s:ss) v
      _ -> pure ()

-- hasKeyOLD just tells you the key is there and then is done
-- and hasKeyALT are similar but hasKeyALT works on an extracted Value
-- object to value
-- not sure about this one?
--hasKey1 :: (AsValue s, Show s) => String -> Pred z Value -> Pred s
--hasKey1 k = PPrism k (^? key (T.pack k)) 0

-- bang json into a Tree and then pretty print it
-- is there a pretty aeson that works for Value?

-- keep track of all the paths you took
-- could use Plated instance from lens-aeson but then we dont have tracking
-- pass in a predicate and run it off String instead of Value or decode it

-- need to reverse this: and use pr'
-- mapM_ putStrLn $ x ^.. _1 . traverse . _1 . to (jasprism . toList)
-- key "Abbrev".key "GlossEntry".key "GlossList".key "GlossDiv".key "glossary"

-- visits every value so we need to add JPValue for the rest
-- N.head to get bottom element cos in reverse order

-- gets you down to the primitive value you want
-- what about passing in a prism and getting the value from that directly
-- not sure this buys us much: just use PJSonP and jstring / jnumber etc to get where we want to go
--jpathZnork :: Prism' Value a -> [String] -> String -> POpts -> [JPath] -> Value -> (TT, Either String a, [JPath])
----jpathZnork psm ss jps v = jpath ss jps v & _2 %~ \mb -> mb >>= (^? psm)
--jpathZnork psm ss e opts jps v = jpath ss opts jps v & _2 %~ (>>= maybe (Left e) Right . preview psm)
{-
jpathObject :: [String] -> POpts -> [JPath] -> Value -> (TT, Either String (HashMap Text Value), [JPath])
jpathObject ss = jpathZnork _Object ss "_Object"

jpathArray :: [String] -> POpts -> [JPath] -> Value -> (TT, Either String (Vector Value), [JPath])
jpathArray ss = jpathZnork _Array ss "_Array"

jpathString :: [String] -> POpts -> [JPath] -> Value -> (TT, Either String Text, [JPath])
jpathString ss = jpathZnork _String ss "_String"

jpathNumber :: [String] -> POpts -> [JPath] -> Value -> (TT, Either String Scientific, [JPath])
jpathNumber ss = jpathZnork _Number ss "_Number"

jpathBool :: [String] -> POpts -> [JPath] -> Value -> (TT, Either String Bool, [JPath])
jpathBool ss = jpathZnork _Bool ss "_Bool"

jpathNull :: [String] -> POpts -> [JPath] -> Value -> (TT, Either String (), [JPath])
jpathNull ss = jpathZnork _Null ss "_Null"
-}
jpath :: [String] -> POpts -> [JPath] -> Value -> (TT, Either String Value, [JPath])
jpath ss opts = go []
  where
  go prevjps [] v = (mkNode (TrueP,ss ++ ["matched complete path"] ++ (if null prevjps then [] else [showLit opts 1 "partial match=" (showJPaths prevjps)])) [], Right v, prevjps)
  go prevjps (jp:jps) v =
      case chkValue jp v of
           Left e -> (mkNodeDebug (FalseP, ss <> [showLit opts 1 "match failed on " (showJPath jp), e] <> (if null prevjps then [] else [showLit opts 1 "partial match=" (showJPaths prevjps)])) []
                           , Left e
                           , prevjps)
           Right v' -> let (tt, mv, prevjps') = go (prevjps ++ [jp]) jps v'
                       in (mkNodeDebug (TrueP, ss <> [showJPath jp] <> [showA opts 1 "value=" v']) [tt]
                           , mv
                           , prevjps')

chkValue :: JPath -> Value -> Either String Value
chkValue jp v =
  case jp of
    JPKey k -> case v ^? key (T.pack k) of
                 Nothing -> case v ^? _Object . to H.keys of
                               Just ks -> Left $ "valid keys are [" <> T.unpack (T.intercalate "," ks) <> "]"
                               Nothing -> Left $ "expected an Object but found " <> show (toConstr v)
                 Just x -> Right x

    JPIndex i -> case v ^? nth i of
                 Nothing -> case v ^? _Array . to length of
                               Just len -> Left $ "valid indices are [0.." <> show (len-1) <> "]"
                               Nothing -> Left $ "expected an Array but found " <> show (toConstr v)
                 Just x -> Right x

    JPValue v' | on (==) toConstr v' v -> if v' == v then Right v else Left (show v' <> " /= " <> show v)
               | otherwise -> Left $ "expected " <> show (toConstr v') <> " but found " <> show (toConstr v)


-- the value-add is pulling the index + value so we dont have to do a partial lookup on _JPIndex
matchIndex :: (Int -> Bool) -> (NonEmpty JPath, Value) -> Maybe (Int, Value)
matchIndex p (JPIndex i :| _, v) | p i = Just (i, v)
matchIndex _ _ = Nothing

matchArrays :: (NonEmpty JPath, Value) -> Maybe [Value]
matchArrays (x :| _, _) = x ^? _JPValue . _Array . to toList

-- not so useful cos lost keys
--matchObjects :: (NonEmpty JPath, Value) -> Maybe [(String, Value)]
--matchObjects (x :| _, _) = x ^? _JPValue . _Object . to (map (first T.unpack) . H.toList)

-- use PI* stuff to look at values
matchObjects :: (NonEmpty JPath, Value) -> Maybe (HashMap Text Value)
matchObjects (x :| _, _) = x ^? _JPValue . _Object

matchNumber :: (Scientific -> Bool) -> (NonEmpty JPath, Value) -> Maybe Scientific
matchNumber p (x :| _, _) =
  case x ^? _JPValue . _Number of
    Just s | p s -> Just s
    _ -> Nothing

-- returns all bools
matchBool :: (NonEmpty JPath, Value) -> Maybe Bool
matchBool (x :| _, _) = x ^? _JPValue . _Bool

-- returns all bools
matchNull :: (NonEmpty JPath, Value) -> Maybe ()
matchNull (x :| _, _) = x ^? _JPValue . _Null

jkeyPrint' :: (Show a, Foldable t) => [(t JPath, (String, a))] -> IO [a]
jkeyPrint' xs = do
  putStrLn ""
  forM (zip [0::Int ..] xs) $ \(i, (reverse . toList -> jps,(k,v))) -> do
    putStrLn $ "i=" <> show i <> "\tkey   => " <> k
    putStrLn $ "\tjpath => " <> show jps
    putStrLn $ "\tprism => " <> showJPaths jps
    putStrLn $ "\tvalue => " <> show v
    putStrLn ""
    return v

{-
>filter ((==1) . length . fst) $ jvisitor (^? _1 . _head1 . _JPKey) json1
[(JPKey "glossary" :| [],"glossary")]
>filter ((==2) . length . fst) $ jvisitor (^? _1 . _head1 . _JPKey) json1
[(JPKey "GlossDiv" :| [JPKey "glossary"],"GlossDiv"),(JPKey "title" :| [JPKey "glossary"],"title")]
>pr $ filter ((==2) . length . fst) $ jvisitor (^? _1 . _head1 . _JPKey) json2
(JPKey "lastName" :| [JPIndex 0],"lastName")
(JPKey "age" :| [JPIndex 0],"age")
(JPKey "firstName" :| [JPIndex 0],"firstName")
(JPKey "likesPizza" :| [JPIndex 0],"likesPizza")
(JPKey "lastName" :| [JPIndex 1],"lastName")
(JPKey "age" :| [JPIndex 1],"age")
(JPKey "firstName" :| [JPIndex 1],"firstName")
(JPKey "likesPizza" :| [JPIndex 1],"likesPizza")
(JPKey "lastName" :| [JPIndex 2],"lastName")
(JPKey "age" :| [JPIndex 2],"age")
(JPKey "firstName" :| [JPIndex 2],"firstName")
(JPKey "likesPizza" :| [JPIndex 2],"likesPizza")
(JPKey "lastName" :| [JPIndex 3],"lastName")
(JPKey "age" :| [JPIndex 3],"age")
(JPKey "firstName" :| [JPIndex 3],"firstName")
(JPKey "likesPizza" :| [JPIndex 3],"likesPizza")

>"[7,true,\"xyz\"]" & nth 0 . _Number %~ (+99)
"[106,true,\"xyz\"]"

>"[1,true]" ^? _Array
Just [Number 1.0,Bool True]

>"[1,true]" ^? _Value . nth 1
Just (Bool True)

>x = fst $ eval o1 (pprism0 (^? _Array) $ PShow 1 * PLinear Rigid ([preq (pprism0 (^? _Bool) 1), preq (peq (Number 9))] <> pdist 3 preq' CS "abc")) "[9,true,\"abC\"]"

cant change BoolPE using mapped or traverse cos the container is fixed!
you can fmap it tho

x & mapped %~ show


show . _peBoolP <$> x

>x ^? branches . ix 0 . root . peBoolP
Just FalseP
>x ^. root . peBoolP
FalseP

https://stackoverflow.com/questions/45736393/how-to-extract-part-of-an-aeson-value-that-satisfies-a-condition
(<&&>) = liftA2 (&&)

 key "instances" . values
 . filtered (anyOf (key "tags" . values)
 $ allOf (key "key") (=="hostname")
    <&&> allOf (key "value") (=="author1useast1"))
 . key "instanceId"

{
  "instances": [
    {
      "instanceId": "i-1234",
      "tags": [
        {
          "value": "author1useast1",
          "key": "hostname"
        }
      ]
    },
    {
      "instanceId": "i-5678",
      "tags": [
        {
          "value": "proxy1useast1",
          "key": "hostname"
        }
      ]
    }
  ]
}
I would like to get a list of all instances/instanceId where instances/tags has a
hostname of author1useast1.


>"[true,1]" ^? _JSON @_ @(Bool,Int) . alongside id id
Just (True,1)

>"[true,\"abc\"]" ^.. _JSON @_ @(Bool,String) . alongside id (to length)
[(True,3)]
>"[true,\"abc\"]" ^.. _JSON @_ @(Bool,String) . alongside (to not) (to length)
[(False,3)]
-}