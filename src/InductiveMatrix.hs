{- |
"Inductive matrices", as in "Type Your Matrices for Great Good: A Haskell
Library of Typed Matrices and Applications (Functional Pearl)" Armando Santos
and José N Oliveira (Haskell Symposium 2020) [URL?]. The main differences:

- Representable functors rather than their index types (logarithms).
- Specified via denotational homomorphisms.
-}

module InductiveMatrix where

import CatPrelude

import qualified LinearFunction as F
import LinearFunction hiding (L)
import Category.Isomorphism

-------------------------------------------------------------------------------
-- | Representation and its denotation
-------------------------------------------------------------------------------

infixr 3 :&#
infixr 2 :|#

type V = Representable

-- | Compositional linear map representation.
data L :: * -> (* -> *) -> (* -> *) -> * where
  Scale :: Semiring s => s -> L s Par1 Par1
  (:|#) :: (C3 V a b c, Additive s) => L s a c -> L s b c -> L s (a :*: b) c
  (:&#) :: C3 V a c k => L s a c -> L s a k -> L s a (c :*: k)
  JoinL :: (C2 V a b, Representable r, Eq (Rep r), Foldable r, Additive s)
        => r (L s a b) -> L s (r :.: a) b
  ForkL :: C3 V a b r => r (L s a b) -> L s a (r :.: b)

instance LinearMap L where
  mu = fwd :<-> rev
   where
     fwd :: L s a b -> F.L s a b
     fwd (Scale s)  = scale s
     fwd (f :|# g)  = fwd f ||| fwd g
     fwd (f :&# g)  = fwd f &&& fwd g
     fwd (JoinL fs) = join (fwd <$> fs)
     fwd (ForkL fs) = fork (fwd <$> fs)
     rev = error "TODO: implement reverse mu on L"

-- TODO: rebuild this fwd definition by composing isomorphisms, eliminating the
-- explicit fwd/rev split. This fwd definition is already built from invertible
-- operations (including scale and fmap of an invertible operation). Dan's
-- failable patterns may be relevant. Can we do so without abstraction leak and
-- without building in a decomposition bias?

-- TODO: Generalize from F.L to all linear map representations. I guess we'll
-- need the intersection of Obj constraints. Or is there a single Obj that all
-- linear map representations can share (not just all _current_)? With careful
-- choice of primitives on all linear map representations, we can probably write
-- a single representation-polymorphic isomorphism that works for _all_ pairs of
-- representations (not just all current). On the other hand, we could instead
-- compose an isomorphism to F.L with an isomorphism from F.L to get the
-- representation-polymorphic isomorphism.

-------------------------------------------------------------------------------
-- | Instances (all deducible from denotational homomorphisms)
-------------------------------------------------------------------------------

-- TODO: Make it compile.
--
-- Does not compile!!!!
-- See:
--
-- Could not deduce (Cartesian (:.:) (L s))
--   arising from a use of ‘unjoin’
--
-- And if we add the constrain we need to add UndecidableInstances:
--
-- The constraint ‘Cartesian (:.:) (L s)’
--  is no smaller than the instance head ‘Additive (L s f g)’
--  (Use UndecidableInstances to permit this)
--
-- And then it will ask for Representable r, for which we need to give
-- a quantified constrain: forall r. Representable r.
instance ( Additive s
         )
          => Additive (L s f g) where
  zero                 = isoRev rowMajIso . isoFwd rowMajIso $ zero
  Scale s + Scale s'   = Scale (s + s')
  JoinL ms  + m = let ms' = unjoin m in Join (ms +^ ms')
  ForkL ms  + m = let ms' = unfork m in Fork (ms +^ ms')
  (f :|# g) + m        = let (h, k) = unjoin2 m in (f + h :|# g + k)
  (f :&# g) + m        = let (h, k) = unfork2 m in (f + h :&# g + k)

rowMajIso :: Iso (->) (L s a b) (b (a s))
rowMajIso = fwd :<-> rev
  where
    fwd :: L s a b -> b (a s)
    fwd (Scale s) = pureRep (pureRep s)
    fwd (f :|# g) = liftR2 (:*:) (fwd f) (fwd g)
    fwd (f :&# g) = fwd f :*: fwd g
    fwd (JoinL m) = cotraverse Comp1 $ fmapRep fwd m
    fwd (ForkL m) = Comp1 $ fmapRep fwd m
    rev :: b (a s) -> L s a b
    rev = undefined -- TODO: Write rev for toRowMajIso.

instance () => Category (L s) where
  type Obj' (L s) a = V a
  id = undefined                                  -- TODO: Write id
  Scale a   . Scale b   = Scale (a * b)           -- Scale denotation
  (p :&# q) . m         = p . m :&# q . m     -- binary product law
  m         . (p :|# q) = m . p :|# m . q     -- binary coproduct law
  (r :|# s) . (p :&# q) = r . p + s . q       -- biproduct law
  ForkL ms' . m         = ForkL (fmap (. m) ms')  -- n-ary product law
  m'        . JoinL ms  = JoinL (fmap (m' .) ms)  -- n-ary coproduct law
  JoinL ms' . ForkL ms  = sum (liftR2 (.) ms' ms)   -- biproduct law

instance (Representable r,Cartesian (:.:) (L s) , Additive s)
      => CartesianR r (:.:) (L s) where
  exs = unfork id
  dups = undefined -- TODO: Write dups

instance (Representable r, Cartesian (:.:) (L s), Additive s)
      => CocartesianR r (:.:) (L s) where
  ins  = unjoin id
  jams = undefined -- TODO: write jams

-- TODO: Derive Via
instance (forall r. Representable r, Additive s) => Monoidal (:*:) (L s) where
  f ### g = (inl . f) :|# (inr . g)

-- TODO: Add deriving via capabilities.
-- Couldn't get constraints to work when defining this instance on the Via
-- type in Category.hs
instance (Representable r, Cartesian (:.:) (L s), Additive s) => MonoidalR r (:.:) (L s) where
  rmap fs = ForkL (fmap (. exr) fs)

-- TODO: Move to Category.hs
-- See: https://en.wikipedia.org/wiki/Abelian_category#Definitions
instance (forall r. Representable r, Additive s) => Cartesian (:*:) (L s) where
  exl = id :| zero
  exr = zero :| id
  dup = id :&# id

-- TODO: Move to Category.hs
-- See: https://en.wikipedia.org/wiki/Abelian_category#Definitions
instance (forall r. Representable r, Additive s) => Cocartesian (:*:) (L s) where
  inl = id :&# zero
  inr = zero :& id
  jam = id :|# id

instance (forall r. Representable r, Additive s) => Biproduct (:*:) (L s)

