{-# LANGUAGE GADTs #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE NoStarIsType #-}
module SimplifyPredState where
import Control.Lens
import Control.Arrow
import Data.Function ( on )
import Data.Coerce ( coerce )
import PredState
import PredHelper

simplifyRange :: Pred z a -> Pred z a
simplifyRange (PRange a b) | a > b = pfalse
simplifyRange p = p

simplifyElem :: Pred z a -> Pred z a
simplifyElem (PElem ta) | null ta = pfalse
simplifyElem p = p

simplifyNotConst :: Pred z a -> Pred z a
simplifyNotConst (PNot (PConst b)) = PConst (b & peBoolP . _BoolP %~ not)
simplifyNotConst p = p

simplifyNotNot :: Pred z a -> Pred z a
simplifyNotNot (PNot (PNot p)) = p
simplifyNotNot p = p

simplifyAndConstL :: Pred z a -> Pred z a
simplifyAndConstL (PAnd (PConst b) q) =
  case view peBoolP b of
    TrueP -> q
    FalseP -> pfalse
    FailP {} -> PConst b
simplifyAndConstL p = p

simplifyAndConstR :: Pred z a -> Pred z a
simplifyAndConstR (PAnd p (PConst b)) =
  case view peBoolP b of
    TrueP -> p
    FalseP -> pfalse
    FailP {} -> PConst b
simplifyAndConstR p = p

simplifyAndNot :: Pred z a -> Pred z a
simplifyAndNot (PAnd (PNot p) (PNot q)) = PNot (POr p q)
simplifyAndNot p = p

simplifyXorConstL :: Pred z a -> Pred z a
simplifyXorConstL (PXor (PConst b) q) =
  case view peBoolP b of
    TrueP -> PNot q
    FalseP -> q
    FailP {} -> PConst b
simplifyXorConstL p = p

simplifyXorConstR :: Pred z a -> Pred z a
simplifyXorConstR (PXor p (PConst b)) =
  case view peBoolP b of
    TrueP -> PNot p
    FalseP -> p
    FailP {} -> PConst b
simplifyXorConstR p = p

simplifyXorNot :: Pred z a -> Pred z a
simplifyXorNot (PXor (PNot p) (PNot q)) = PXor q p
simplifyXorNot p = p

simplifyOrConstB :: Pred z a -> Pred z a
simplifyOrConstB (POr (PConst b) (PConst b1)) =
  case (view peBoolP b, view peBoolP b1) of
    (TrueP, FailP {}) -> ptrue
    (FailP {}, TrueP) -> ptrue
    (FalseP, FailP {}) -> PConst b1
    (FailP {}, FalseP) -> PConst b
    (FailP {}, FailP {}) -> PConst (b <> b1)
    (_, _) -> let x = on (liftBool2 (||)) (view peBoolP) b b1
              in PConst ((b <> b1) & peBoolP .~ x)
simplifyOrConstB p = p

simplifyOrConstL :: Pred z a -> Pred z a
simplifyOrConstL (POr (PConst b) q) =
  case view peBoolP b of
    TrueP -> ptrue
    FalseP -> q
    FailP {} -> PConst b
simplifyOrConstL p = p

simplifyOrConstR :: Pred z a -> Pred z a
simplifyOrConstR (POr p (PConst b)) =
  case view peBoolP b of
    TrueP -> ptrue
    FalseP -> p
    FailP {} -> PConst b
simplifyOrConstR p = p

simplifyOrNot :: Pred z a -> Pred z a
simplifyOrNot (POr (PNot p) (PNot q)) = PNot (PAnd p q)
simplifyOrNot p = p

simplifyImplConstB :: Pred z a -> Pred z a
simplifyImplConstB (PImpl (PConst b) (PConst b1)) =
  case (view peBoolP b, view peBoolP b1) of
    (FailP {}, _) -> PConst (b <> b1)
    (_, FailP {}) -> PConst (b <> b1)
    (_, _) -> let x = on (liftBool2 impl) (view peBoolP) b b1
              in PConst ((b <> b1) & peBoolP .~ x)

simplifyImplConstB p = p

simplifyImplConstL :: Pred z a -> Pred z a
simplifyImplConstL (PImpl (PConst b) q) =
  case view peBoolP b of
    TrueP -> q
    FalseP -> ptrue
    FailP {} -> PConst b
simplifyImplConstL p = p

simplifyImplNot :: Pred z a -> Pred z a
simplifyImplNot (PImpl (PNot p) (PNot q)) = PImpl q p
simplifyImplNot p = p

simplifyImplNot2 :: Pred z a -> Pred z a
simplifyImplNot2 (PImpl (PNot p) q) = POr p q
simplifyImplNot2 p = p

-- if same PConst on both sides then we know the answer
simplifyMaybeConst2 :: Pred z a -> Pred z a
simplifyMaybeConst2 p@(PMaybe (PConst b) (PConst b1)) =
  case (view peBoolP b, view peBoolP b1) of
    (TrueP, TrueP) -> ptrue
    (FalseP, FalseP) -> pfalse
    (FailP {}, FailP {}) -> PConst (b <> b1)
    (FailP {}, _) -> PConst b
    (_, FailP {}) -> PConst b1
    _ -> p
simplifyMaybeConst2 p = p

-- if same PConst on both sides then we know the answer
simplifyEitherConst2 :: Pred z a -> Pred z a
simplifyEitherConst2 p@(PEither (PConst b) (PConst b1)) =
  case (view peBoolP b, view peBoolP b1) of
    (TrueP, TrueP) -> ptrue
    (FalseP, FalseP) -> pfalse
    (FailP {}, FailP {}) -> PConst (b <> b1)
    (FailP {}, _) -> PConst b
    (_, FailP {}) -> PConst b1
    _ -> p
simplifyEitherConst2 p = p

-- if same PConst on both sides then we know the answer
simplifyIxConst2 :: Pred z a -> Pred z a
simplifyIxConst2 p@(PIx _ (PConst b) (PConst b1)) =
  case (view peBoolP b, view peBoolP b1) of
    (TrueP, TrueP) -> ptrue
    (FalseP, FalseP) -> pfalse
    (FailP {}, FailP {}) -> PConst (b <> b1)
    (FailP {}, _) -> PConst b
    (_, FailP {}) -> PConst b1
    _ -> p
simplifyIxConst2 p = p

-- if same PConst on both sides then we know the answer
simplifyHeadConst2 :: Pred z a -> Pred z a
simplifyHeadConst2 p@(PHead (PConst b) (PConst b1)) =
  case (view peBoolP b, view peBoolP b1) of
    (TrueP, TrueP) -> ptrue
    (FalseP, FalseP) -> pfalse
    (FailP {}, FailP {}) -> PConst (b <> b1)
    (FailP {}, _) -> PConst b
    (_, FailP {}) -> PConst b1
    _ -> p
simplifyHeadConst2 p = p

-- if same PConst on both sides then we know the answer
simplifyLastConst2 :: Pred z a -> Pred z a
simplifyLastConst2 p@(PLast (PConst b) (PConst b1)) =
  case (view peBoolP b, view peBoolP b1) of
    (TrueP, TrueP) -> ptrue
    (FalseP, FalseP) -> pfalse
    (FailP {}, FailP {}) -> PConst (b <> b1)
    (FailP {}, _) -> PConst b
    (_, FailP {}) -> PConst b1
    _ -> p
simplifyLastConst2 p = p

simplifyForAllConst :: Pred z a -> Pred z a
simplifyForAllConst (PForAll (PConst b)) =
  case view peBoolP b of
    TrueP -> ptrue
    FalseP -> pfalse
    FailP {} -> PConst b
simplifyForAllConst p = p

simplifyExistsConst :: Pred z a -> Pred z a
simplifyExistsConst (PExists (PConst b)) =
  case view peBoolP b of
    TrueP -> ptrue
    FalseP -> pfalse
    FailP {} -> PConst b
simplifyExistsConst p = p
-- simplifyExistsConst (PExists z@PConst {}) = z  -- doesnt work cos of existential

simplifyNotForAll :: Pred z a -> Pred z a
simplifyNotForAll (PNot (PForAll p)) = PExists (PNot p)
simplifyNotForAll p = p

simplifyNotExists :: Pred z a -> Pred z a
simplifyNotExists (PNot (PExists p)) = PForAll (PNot p)
simplifyNotExists p = p

simplifyCoerceConst :: Pred z a -> Pred z a
simplifyCoerceConst (PCoerce (PConst b)) = PConst (coerce b)
simplifyCoerceConst p = p

simplifyOrDie :: Pred z a -> Pred z a
simplifyOrDie (POrDie s (PConst b)) =
  case view peBoolP b of
    TrueP -> ptrue
    FalseP -> pfail ("POrDie " <> s)
    FailP {} -> PConst b
simplifyOrDie p = p

simplifyCatch :: Pred z a -> Pred z a
simplifyCatch (PCatch (PConst e) (PConst b)) =
  case view peBoolP b of
    FailP {} -> PConst e
    _ -> PConst b
simplifyCatch p = p

simplifyMsg :: Pred z a -> Pred z a
simplifyMsg (PMsg _ _ (PConst b)) = PConst b
simplifyMsg p = p

simplifyChangeOpts :: Pred z a -> Pred z a
simplifyChangeOpts (PChangeOpts _ b@PConst{}) = b
simplifyChangeOpts p = p

simplifyFst :: Pred z a -> Pred z a
simplifyFst (PFst (PConst b)) = PConst b
simplifyFst p = p

simplifySnd :: Pred z a -> Pred z a
simplifySnd (PSnd (PConst b)) = PConst b
simplifySnd p = p

-- cos top down we need to run this several times! gack: need this to be bottom up!
-- not a functor / nor contravariant so not going to happen
simplifyN :: Int -> Pred z a -> Pred z a
--simplifyN = foldr1 (.) . flip replicate simplify
--simplifyN n p = foldr (const simplify) p [1..n]
--simplifyN n = appEndo (stimes n (Endo simplify))
simplifyN = foldr (.) id . flip replicate simplify -- best so far
-- same as foldr1 case but handles n<=0 condition
-- creates a chain of simplifys and then applies 'p' at the end

-- do simplest stuff first
simplify :: Pred z a -> Pred z a
simplify =
   simplify' simplifyCoerceConst
 . simplify' simplifyChangeOpts
 . simplify' simplifyOrDie
 . simplify' simplifyMsg
 . simplify' simplifyCatch
-- . simplify' simplifyOrs
-- . simplify' simplifyAnds
 . simplify' simplifyNotExists
 . simplify' simplifyNotForAll
 . simplify' simplifyExistsConst
 . simplify' simplifyForAllConst

 . simplify' simplifyIxConst2
 . simplify' simplifyMaybeConst2
 . simplify' simplifyEitherConst2

 . simplify' simplifyHeadConst2
 . simplify' simplifyLastConst2
 . simplify' simplifyAndNot
 . simplify' simplifyAndConstR
 . simplify' simplifyAndConstL
 . simplify' simplifyImplNot2
 . simplify' simplifyImplNot
 . simplify' simplifyImplConstB
 . simplify' simplifyImplConstL
 . simplify' simplifyXorNot
 . simplify' simplifyXorConstR
 . simplify' simplifyXorConstL
 . simplify' simplifyOrNot
 . simplify' simplifyOrConstR
 . simplify' simplifyOrConstL
 . simplify' simplifyOrConstB
 . simplify' simplifyNotNot
 . simplify' simplifyNotConst
 . simplify' simplifyFst
 . simplify' simplifySnd
 . simplify' simplifyRange
 . simplify' simplifyElem

{- skolem issues! have to wrap elements of jarray with simplify'
ss p = foldr (\f p' -> go f p') p
  [simplifyNotConst
  , simplifyNotNot
  , simplifyOrConstL
  , ...
  ]
  where go :: (forall x . Pred z x -> Pred x) -> Pred a -> Pred z a
        go f p = simplify' f p
-}

-- top down but we want bottom up
simplify' :: forall a z . (forall x . Pred z x -> Pred z x ) -> Pred z a -> Pred z a
simplify' nat = go
  where
  go :: Pred z b -> Pred z b
  go px = case nat px of
            PFn s f p          -> PFn s f (go p)
            PAnd p q           -> PAnd (go p) (go q)
            POr p q            -> POr (go p) (go q)
            PXor p q           -> PXor (go p) (go q)
            PEquiv p q         -> PEquiv (go p) (go q)
            PImpl p q          -> PImpl (go p) (go q)
            PNot p             -> PNot (go p)
            POps ps q          -> POps (map go ps) (go q)
            PForAll p          -> PForAll (go p)
            PZipExact ps e q     -> PZipExact (map go ps) e (go q)
            PSeq ps q          -> PSeq (map go ps) (go q)
            PExists p          -> PExists (go p)
            PConst b           -> PConst b
            PLift s f          -> PLift s f
            PString b sop s    -> PString b sop s
            PDist b s p        -> PDist b s (go p)
            PCmp c a           -> PCmp c a
            PEq b a            -> PEq b a
            PCmp2 c            -> PCmp2 c
            PEq2 b             -> PEq2 b
            PMatch sop a       -> PMatch sop a
            PRegex t regex e p -> PRegex t regex (go e) (go p)
            PRegexI t regex e p -> PRegexI t regex (go e) (go p)
            PRegexs rs p       -> PRegexs rs (go p)
            PRegexV rs e p     -> PRegexV rs (go e) (go p)
            PRegexN th rs e p  -> PRegexN th rs (go e) (go p)
            PRegexIP th t rx rb e p  -> PRegexIP th t rx rb (go e) (go p)
            PElem as           -> PElem as
            PRange a a'        -> PRange a a'
            PLen p             -> PLen (go p)
            PBoth pa pb        -> PBoth (go pa) (go pb)
            PFst p             -> PFst (go p)
            PSnd p             -> PSnd (go p)
            PNull              -> PNull
            PEmpty             -> PEmpty
            PIf mpexc mpb mpg p -> PIf (go <$> mpexc) (go <$> mpb) (go <$> mpg) (go p)
            PApp a p           -> PApp a (go p)
            PJoin a            -> PJoin a
            PView g p          -> PView g (go p)
            PHead e p          -> PHead (go e) (go p)
            POne e e2 p        -> POne (go e) (go e2) (go p)
            POneT e e2 p       -> POneT (go e) (go e2) (go p)
            PUnconsT e p       -> PUnconsT (go e) (go p)
            PUncons e p        -> PUncons (go e) (go p)
            PLast e p          -> PLast (go e) (go p)
            PUnsnocT e p       -> PUnsnocT (go e) (go p)
            PUnsnoc e p        -> PUnsnoc (go e) (go p)
            PIx i e p          -> PIx i (go e) (go p)
            PCoerce p          -> PCoerce (go p)
            PPartition p pbg   -> PPartition (go p) (go pbg)
            POrder c           -> POrder c
            POrderEq b         -> POrderEq b
            PLinear b qps      -> PLinear b (map (go *** go) qps)
            PSplitAt i p       -> PSplitAt i (go p)
            PBreak p p12       -> PBreak (go p) (go p12)
            PSpan p p12        -> PSpan (go p) (go p12)
--            PSpans ips q       -> PSpans (map (second (go +++ go)) ips) (go q)
            PEither p q        -> PEither (go p) (go q)
            PThese p q pq      -> PThese (go p) (go q) (go pq)
            PISect p           -> PISect (go p)
            PISectList p       -> PISectList (go p)
            PMorph f p         -> PMorph f (go p)
            PMaybe p q         -> PMaybe (go p) (go q)
            PPrism s f e p     -> PPrism s f (go e) (go p)
            PPrismL s f e p    -> PPrismL s f (go e) (go p)
            PPrismR s f e p    -> PPrismR s f (go e) (go p)
            PPrismLE s f e p   -> PPrismLE s f (go e) (go p)
            PPrismRE s f e p   -> PPrismRE s f (go e) (go p)
            PSwap p            -> PSwap (go p)
            PReverse p         -> PReverse (go p)
            POrDie s p         -> POrDie s (go p)
            PCatch p q         -> PCatch (go p) (go q)
            PMsg hide s p      -> PMsg hide s (go p)
            PTree f p          -> PTree f (go p)
            PChangeOpts f p    -> PChangeOpts f (go p)
            PShow p            -> PShow (go p)
            PShowS p           -> PShowS (go p)
            PShow1 p           -> PShow1 (go p)
            PShowS1 p          -> PShowS1 (go p)
            PJson f p          -> PJson f (go p)
            PJsonKey p q       -> PJsonKey (go p) (go q)
            PJsonP jps p q     -> PJsonP jps (go p) (go q)
            PLog f p           -> PLog f (go p)
            PState f p         -> PState f (go p)
            PGet p             -> PGet (go p)

