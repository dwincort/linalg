{-# LANGUAGE UndecidableInstances #-}
-- | Linear algebra after Fortran

module LinAlg where

import qualified Prelude as P
import Prelude hiding ((+),sum,(*),unzip)

import GHC.Generics (Par1(..), (:*:)(..), (:.:)(..))
import qualified Control.Arrow as A
import Data.Distributive
import Data.Functor.Rep
import Data.Constraint (Dict(..))
import Unsafe.Coerce (unsafeCoerce)

infixl 7 :*
type (:*)  = (,)

-- infixl 6 :+
-- type (:+)  = Either

unzip :: Functor f => f (a :* b) -> f a :* f b
unzip ps = (fst <$> ps, snd <$> ps)

type V f = (Representable f, Foldable f, Eq (Rep f), Traversable f)
type V2 f g = (V f, V g)
type V3 f g h = (V2 f g, V h)

class Additive a where
  infixl 6 +
  zero :: a
  (+) :: a -> a -> a

class Additive a => Semiring a where
  infixl 7 *
  one :: a
  (*) :: a -> a -> a

sum :: (Foldable f, Additive a) => f a -> a
sum = foldr (+) zero

-- | Vector addition
infixl 6 +^
(+^) :: (Representable f, Additive s) => f s -> f s -> f s
(+^) = liftR2 (+)

instance Additive Double where { zero = 0; (+) = (P.+) }
instance Semiring Double where { one  = 1; (*) = (P.*) }

infixr 3 :&#
infixr 2 :|#

-- | Compositional Linear map representation. @L f g s@ denotes @f s -* g s@,
-- where @(-*)@ means linear functions.
data L :: (* -> *) -> (* -> *) -> (* -> *) where
  Zero :: V2 f g => L f g s
  Scale :: s -> L Par1 Par1 s
  (:|#) :: V3 f g h => L f h s -> L g h s -> L (f :*: g) h s
  (:&#) :: V3 f g h => L f g s -> L f h s -> L f (g :*: h) s
  JoinL :: V3 f g h => h (L f g s) -> L (h :.: f) g s
  ForkL :: V3 f g h => h (L f g s) -> L f (h :.: g) s

-- Scalable vectors
class V a => HasScaleV a where
  scaleV :: Semiring s => s -> L a a s

type HasScaleV2 a b = (HasScaleV a, HasScaleV b)

instance HasScaleV Par1 where scaleV = Scale

instance (HasScaleV a, HasScaleV b) => HasScaleV (a :*: b) where
  scaleV s = scaleV s *** scaleV s

instance (HasScaleV a, HasScaleV b, Representable b) => HasScaleV (b :.: a) where
  scaleV s = cross (pureRep (scaleV s))

unjoin2 :: (Additive s, V3 f g h) => L (f :*: g) h s -> L f h s :* L g h s
unjoin2 Zero = (zero,zero)
unjoin2 (p :|# q) = (p,q)
unjoin2 ((unjoin2 -> (p,q)) :&# (unjoin2 -> (r,s))) = (p :& r, q :& s)
unjoin2 (ForkL ms) = (ForkL A.*** ForkL) (unzip (unjoin2 <$> ms))

-- unjoin2 ((p :| q) :&# (r :| s)) = (p :&# r, q :#& s)

-- Recursive pattern synonym definition with following bindings:
--   unjoin2 (defined at src/LinAlg.hs:(52,1)-(63,50))
--   :| (defined at src/LinAlg.hs:75:1-55)

#if 0
                               ForkL ms   :: L (f :*: g) (k :.: h) s
                                     ms   :: k (L (f :*: g) h s)
                          unjoin <$> ms   :: k (L f h s :* L g h s)
                   unzip (unjoin <$> ms)  :: k (L f h s) :* k (L g h s)
(ForkL *** ForkL) (unzip (unjoin <$> ms)) :: L f (k :.: h) s :* L g (k :.: h) s
#endif

unfork2 :: (V3 f g h, Additive s) => L f (g :*: h) s -> L f g s :* L f h s
unfork2 Zero = (zero,zero)
unfork2 (p :&# q) = (p,q)
unfork2 ((unfork2 -> (p,q)) :|# (unfork2 -> (r,s))) = (p :|# r, q :|# s)
unfork2 (JoinL ms) = (JoinL A.*** JoinL) (unzip (unfork2 <$> ms))

-- unfork2 ((p :& q) :|# (r :& s)) = (p :|# r, q :|# s)

pattern (:&) :: (V3 f g h, Additive s) => L f g s -> L f h s -> L f (g :*: h) s
pattern u :& v <- (unfork2 -> (u,v)) where (:&) = (:&#)
{-# complete (:&) #-}

pattern (:|) :: (V3 f g h, Additive s) => L f h s -> L g h s -> L (f :*: g) h s
pattern u :| v <- (unjoin2 -> (u,v)) where (:|) = (:|#)
{-# complete (:|) #-}

-- pattern Join :: V h => h (L f g s) -> L (h :.: f) g s
-- pattern Join ms <- (unjoinL -> ms) where Join = JoinL
-- {-# complete Join #-}

unforkL :: (V3 f g h) => L f (h :.: g) s -> h (L f g s)
unforkL Zero       = pureRep Zero
unforkL (p :|# q)  = liftR2 (:|#) (unforkL p) (unforkL q)
unforkL (ForkL ms) = ms
unforkL (JoinL ms) = JoinL <$> distribute (unforkL <$> ms)

#if 0
-- Types for binary join clause
p :|# p' :: L (f :*: f') (h :.: g) s

                      p               :: L f  (h :.: g) s
                                  p'  :: L f' (h :.: g) s
              unforkL p               :: h (L f  g  s)
                          unforkL p'  :: h (L f' g  s)
liftR2 (:|#) (unforkL p) (unforkL p') :: h (L (f :*: f') g s)

-- Types for n-ary join clause:

     JoinL                     ms  :: L (k :.: f) (h :.: g) s
                               ms  :: k (L f (h :.: g) s)
                   unforkL <$> ms  :: k (h (L f g s))
          distrib (unforkL <$> ms) :: h (k (L f g s))
JoinL <$> distrib (unforkL <$> ms) :: h (L (k :.: f) g s)
#endif

unjoinL :: (V3 f g h) => L (h :.: f) g s -> h (L f g s)
unjoinL Zero       = pureRep Zero
unjoinL (p :&# p') = liftR2 (:&#) (unjoinL p) (unjoinL p')
unjoinL (JoinL ms) = ms
unjoinL (ForkL ms) = fmap ForkL (distribute (fmap unjoinL ms))

pattern Fork :: V3 f g h => h (L f g s) -> L f (h :.: g) s
pattern Fork ms <- (unforkL -> ms) where Fork = ForkL
{-# complete Fork #-}

pattern Join :: V3 f g h => h (L f g s) -> L (h :.: f) g s
pattern Join ms <- (unjoinL -> ms) where Join = JoinL
{-# complete Join #-}

instance (V2 f g, Additive s) => Additive (L f g s) where
  zero = Zero
  Zero + m = m
  m + Zero = m
  Scale s + Scale s' = Scale (s + s') -- distributivity
  (f :|# g) + (h :| k) = (f + h) :| (g + k)
  (f :&# g) + (h :& k) = (f + h) :& (g + k)
  ForkL ms  + Fork ms' = Fork (ms +^ ms')
  JoinL ms  + Join ms' = Join (ms +^ ms')

-- | Row-major "matrix" of linear maps
rowMajor' :: (V2 f g, V2 h k) => k (h (L f g s)) -> L (h :.: f) (k :.: g) s
rowMajor' = Fork . fmap Join

-- | Row-major "matrix" of scalars
rowMajor :: (V f, V g) => g (f s) -> L (f :.: Par1) (g :.: Par1) s
rowMajor = rowMajor' . (fmap.fmap) Scale

diagRep :: (Representable h, Eq (Rep h)) => a -> h a -> h (h a)
diagRep dflt as =
  tabulate (\ i -> tabulate (\ j -> if i == j then as `index` i else dflt))

idL :: (HasScaleV a, Semiring s) => L a a s
idL = scaleV one

infixr 9 .@
(.@) :: (V3 f g h, Semiring s) => L g h s -> L f g s -> L f h s
Zero      .@ _         = Zero                      -- Zero denotation
_         .@ Zero      = Zero                      -- linearity
Scale a   .@ Scale b   = Scale (a * b)             -- Scale denotation
(p :&# q) .@ m         = (p .@ m) :&# (q .@ m)     -- binary product law
m         .@ (p :|# q) = (m .@ p) :|# (m .@ q)     -- binary coproduct law
(r :|# s) .@ (p :&# q) = (r .@ p) + (s .@ q)       -- biproduct law
ForkL ms' .@ m         = ForkL (fmap (.@ m) ms')   -- n-ary product law
m'        .@ JoinL ms  = JoinL (fmap (m' .@) ms)   -- n-ary coproduct law
JoinL ms' .@ ForkL ms  = sum (ms' .^ ms)           -- biproduct law

(.^) :: (Representable p, V3 f g h, Semiring s) => p (L g h s) -> p (L f g s) -> p (L f h s)
(.^) = liftR2 (.@)

instance (HasScaleV f, Semiring s) => Semiring (L f f s) where
  one = idL
  (*) = (.@)

-- Binary injections

inl :: (HasScaleV a, V b, Semiring s) => L a (a :*: b) s
inl = idL :& zero

inr :: (HasScaleV b, V a, Semiring s) => L b (a :*: b) s
inr = zero :& idL

-- Binary projections

exl :: (HasScaleV a, V b, Semiring s) => L (a :*: b) a s
exl = idL :| zero

exr :: (HasScaleV b, V a, Semiring s) => L (a :*: b) b s
exr = zero :| idL

-- Note that idL == inl :| inr == exl :& exr.

-- N-ary injections
ins :: (HasScaleV2 a c, Semiring s) => c (L a (c :.: a) s)
ins = unjoinL idL

-- N-ary projections
exs :: (HasScaleV2 a c, Semiring s) => c (L (c :.: a) a s)
exs = unforkL idL

-- Note that idL == joinL ins == forkL exs

-- Binary biproduct bifunctor
(***) :: (V2 a c, V2 b d) => L a c s -> L b d s -> L (a :*: b) (c :*: d) s
f *** g = (f :|# Zero) :&# (Zero :|# g)

-- N-ary biproduct bifunctor
cross :: (V3 a b c, Additive s) => c (L a b s) -> L (c :.: a) (c :.: b) s
cross = JoinL . fmap ForkL . diagRep zero

{- Note that

f *** g == (f :|# Zero) :&# (Zero :|# g)
        == (f :&# Zero) :|# (Zero :&# g)
        == (f .@ exl) :&# (g .@ exr)
        == (inl .@ f) :|# (inr .@ g)

cross fs == JoinL (ins .^ fs)
         == ForkL (fs .^ exs)

-}



ifoldrRep :: forall r a b. (Representable r, Foldable r)
            => (Rep r -> a -> b -> b) -> b -> r a -> b
ifoldrRep ix b xs = foldr (uncurry ix) b
  (tabulate (\(i :: Rep r) -> (i, index xs i)) :: r (Rep r, a))


data IsJoin f g s where
  IsJoin :: V3 f g h => h (L f g s) -> IsJoin (h :.: f) g s

isJoin :: forall f g s. V2 f g => L f g s -> Maybe (IsJoin f g s)
isJoin Zero       = Nothing -- IsJoin (pureRep Zero)
isJoin (Scale _)  = Nothing
isJoin (_ :|# _)  = Nothing
isJoin (p :&# q) = case (isJoin p, isJoin q) of
  (Just (IsJoin p'), Just (IsJoin q')) -> Just (IsJoin (liftR2 (:&#) p' q'))
  _ -> Nothing
isJoin (JoinL ms) = Just (IsJoin ms)
isJoin (ForkL (ms :: k (L f g' s))) = case sequenceA (isJoin <$> ms) of
  Just ys -> case ifoldrRep go (unsafeCoerce $ Dict @(), Nothing, const undefined) ys of
    (Dict, Just Dict, k) -> Just $ IsJoin $ fmap ForkL $ distribute $ tabulate k
    _ -> Nothing
  Nothing -> Nothing
  where
    go :: Rep k -> IsJoin f g' s -> (Dict (f ~ (h :.: f')), Maybe (Dict (V2 f' h)), Rep k -> h (L f' g' s))
       -> (Dict (f ~ (h :.: f')), Maybe (Dict (V2 f' h)), Rep k -> h (L f' g' s))
    go k (IsJoin hs) (Dict, _, fun) = (Dict, Just Dict, \k' -> if k == k' then hs else fun k')

pattern Join' :: (V2 f g) => (f ~ (h :.: f'), V2 h f') => h (L f' g s) -> L f g s
pattern Join' ms <- (isJoin -> Just (IsJoin ms)) where Join' = JoinL


data IsFork f g s where
  IsFork :: V3 f g h => h (L f g s) -> IsFork f (h :.: g) s

isFork :: V2 f g => L f g s -> Maybe (IsFork f g s)
isFork Zero       = Nothing --IsJoin (pureRep Zero)
isFork (Scale _)  = Nothing
isFork (_ :&# _)  = Nothing
isFork (p :|# q) = case (isFork p, isFork q) of
  (Just (IsFork p'), Just (IsFork q')) -> Just $ IsFork (liftR2 (:|#) p' q')
  _ -> Nothing
isFork (ForkL ms) = Just $ IsFork ms
isFork (JoinL (ms :: k (L f' g s))) = case sequenceA (isFork <$> ms) of
  Just ys -> case ifoldrRep go (unsafeCoerce $ Dict @(), Nothing, const undefined) ys of
    (Dict, Just Dict, k) -> Just $ IsFork $ fmap JoinL $ distribute $ tabulate k
    _ -> Nothing
  Nothing -> Nothing
  where
    go :: Rep k -> IsFork f' g s -> (Dict (g ~ (h :.: g')), Maybe (Dict (V2 g' h)), Rep k -> h (L f' g' s))
       -> (Dict (g ~ (h :.: g')), Maybe (Dict (V2 g' h)), Rep k -> h (L f' g' s))
    go k (IsFork hs) (Dict, _, fun) = (Dict, Just Dict, \k' -> if k == k' then hs else fun k')

pattern Fork' :: (V2 f g) => (g ~ (h :.: g'), V2 h g') => h (L f g' s) -> L f g s
pattern Fork' ms <- (isFork -> Just (IsFork ms)) where Fork' = ForkL



data IsJoin2 f g s where
  IsJoin2 :: V3 f g h => L f h s -> L g h s -> IsJoin2 (f :*: g) h s

isJoin2 :: forall f g s. V2 f g => L f g s -> Maybe (IsJoin2 f g s)
isJoin2 Zero       = Nothing -- IsJoin2 (pureRep Zero)
isJoin2 (Scale _)  = Nothing
isJoin2 (p :|# q)  = Just $ IsJoin2 p q
isJoin2 (p :&# q) = case (isJoin2 p, isJoin2 q) of
  (Just (IsJoin2 p' p''), Just (IsJoin2 q' q'')) -> Just $ IsJoin2 (p' :&# q') (p'' :&# q'')
  _ -> Nothing
isJoin2 (JoinL _) = Nothing
isJoin2 (ForkL (ms :: k (L f g' s))) = case sequenceA (isJoin2 <$> ms) of
  Just ys -> case ifoldrRep go (unsafeCoerce $ Dict @(), Nothing, const undefined) ys of
    (Dict, Just Dict, k) -> Just $ uncurry IsJoin2 $ ForkL A.*** ForkL $ unzip $ tabulate k
    _ -> Nothing
  Nothing -> Nothing
  where
    go :: Rep k -> IsJoin2 f g' s -> (Dict (f ~ (f' :*: h)), Maybe (Dict (V2 f' h)), Rep k -> (L f' g' s, L h g' s))
       -> (Dict (f ~ (f' :*: h)), Maybe (Dict (V2 f' h)), Rep k -> (L f' g' s, L h g' s))
    go k (IsJoin2 f g) (Dict, _, fun) = (Dict, Just Dict, \k' -> if k == k' then (f,g) else fun k')

pattern (:|:) :: (V2 f g) => (f ~ (f' :*: h), V2 f' h) => L f' g s -> L h g s -> L f g s
pattern f :|: g <- (isJoin2 -> Just (IsJoin2 f g)) where (:|:) = (:|#)



data IsFork2 f g s where
  IsFork2 :: V3 f g h => L f g s -> L f h s -> IsFork2 f (g :*: h) s

isFork2 :: forall f g s. V2 f g => L f g s -> Maybe (IsFork2 f g s)
isFork2 Zero       = Nothing -- IsFork2 (pureRep Zero)
isFork2 (Scale _)  = Nothing
isFork2 (p :&# q)  = Just $ IsFork2 p q
isFork2 (p :|# q) = case (isFork2 p, isFork2 q) of
  (Just (IsFork2 p' p''), Just (IsFork2 q' q'')) -> Just $ IsFork2 (p' :|# q') (p'' :|# q'')
  _ -> Nothing
isFork2 (ForkL _) = Nothing
isFork2 (JoinL (ms :: k (L f' g s))) = case sequenceA (isFork2 <$> ms) of
  Just ys -> case ifoldrRep go (unsafeCoerce $ Dict @(), Nothing, const undefined) ys of
    (Dict, Just Dict, k) -> Just $ uncurry IsFork2 $ JoinL A.*** JoinL $ unzip $ tabulate k
    _ -> Nothing
  Nothing -> Nothing
  where
    go :: Rep k -> IsFork2 f' g s -> (Dict (g ~ (g' :*: h)), Maybe (Dict (V2 g' h)), Rep k -> (L f' g' s, L f' h s))
       -> (Dict (g ~ (g' :*: h)), Maybe (Dict (V2 g' h)), Rep k -> (L f' g' s, L f' h s))
    go k (IsFork2 f g) (Dict, _, fun) = (Dict, Just Dict, \k' -> if k == k' then (f,g) else fun k')

pattern (:&:) :: (V2 f g) => (g ~ (g' :*: h), V2 g' h) => L f g' s -> L f h s -> L f g s
pattern f :&: g <- (isFork2 -> Just (IsFork2 f g)) where (:&:) = (:&#)

-- {-# COMPLETE Zero, Scale, (:&:), (:|:), Join', Fork' #-}
