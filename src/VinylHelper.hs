{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE AllowAmbiguousTypes #-} -- need this cos of fromIx
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE NoStarIsType #-}
module VinylHelper where
import Data.Semigroup ( Sum(Sum, getSum) )
import Data.Vinyl
import Data.Vinyl.TypeLevel ( Nat(..), RIndex )
import qualified Data.Vinyl.Functor as W
import qualified Data.Vinyl.Recursive as WR
import Data.Proxy ( Proxy(..) )
import qualified GHC.TypeLits as G

recLen :: Rec f rs -> Int
recLen = getSum . WR.rfoldMap (const (Sum 1))

recGet :: (RecElemFCtx record W.Identity,
      RecElem record c c rs rs (RIndex c rs)) =>
     record W.Identity rs -> c
recGet = W.getIdentity . rget

-- index into a vinyl record: need to index based on a number that gets converted to an int someho
-- best i can do is Lit type family ie Proxy @(Lit 3) vs (Proxy @('S ('S ('S 'Z))))
-- was xs :: [*] which is too restrictive cos wont work with ElField!
class IndexType (n :: Nat) (xs :: [k]) a | n xs -> a where
  fromIx :: Rec f xs -> f a
  fromIndex :: Proxy n -> Rec f xs -> f a

instance IndexType 'Z (x ': xs) x where
  fromIx (x :& _) = x
  fromIndex Proxy (x :& _) = x

instance IndexType n xs a => IndexType ('S n) (x ': xs) a where
  fromIx (_ :& xs) = fromIndex (Proxy @n) xs
  fromIndex Proxy (_ :& xs) = fromIndex (Proxy @n) xs

-- stolen from singleton-nats:Data.Nat
type family Lit n where
  Lit 0 = 'Z
  Lit n = 'S (Lit ((G.-) n 1))
--  Lit n = 'S (Lit (n G.- 1))  -- hlint cant handle infix so make it prefix

-- | 'rind' gets the index of a vinyl record using @n
rind :: forall n a xs. (IndexType (Lit n) xs a) => Rec W.Identity xs -> a
rind = W.getIdentity . fromIndex (Proxy @(Lit n))

rind' :: forall n f a xs. (IndexType (Lit n) xs a) => Rec f xs -> f a
rind' = fromIndex (Proxy @(Lit n))

{-# COMPLETE E1 #-}
pattern E1 :: f a -> Rec f '[a]
pattern E1 fa = fa :& RNil

{-# COMPLETE E2 #-}
pattern E2 :: f a -> f b -> Rec f '[a,b]
pattern E2 fa fb = fa :& fb :& RNil

{-# COMPLETE E3 #-}
pattern E3 :: f a -> f b -> f c -> Rec f '[a,b,c]
pattern E3 fa fb fc = fa :& fb :& fc :& RNil

{-# COMPLETE E4 #-}
pattern E4 :: f a -> f b -> f c -> f d -> Rec f '[a,b,c,d]
pattern E4 fa fb fc fd = fa :& fb :& fc :& fd :& RNil

{-# COMPLETE E5 #-}
pattern E5 :: f a -> f b -> f c -> f d -> f e -> Rec f '[a,b,c,d,e]
pattern E5 fa fb fc fd fe = fa :& fb :& fc :& fd :& fe :& RNil

{-# COMPLETE E6 #-}
pattern E6 :: f a -> f b -> f c -> f d -> f e -> f f' -> Rec f '[a,b,c,d,e,f']
pattern E6 fa fb fc fd fe ff = fa :& fb :& fc :& fd :& fe :& ff :& RNil
