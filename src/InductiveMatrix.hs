{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE ScopedTypeVariables #-}

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

type V' a = (Representable a, Eq (Rep a))

class    V' a => V a
instance V' a => V a

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

-- This gives non-exhaustive pattern matching because pattern synonyms
-- cannot be made complete
instance Semiring s => Additive (L s f g) where
  zero                 = isoRev rowMajIso . isoFwd rowMajIso $ zero
  Scale s + Scale s'   = Scale (s + s')
  (f :|# g) + (h :| k) = (f + h) :| (g + k)
  (f :&# g) + (h :& k) = (f + h) :& (g + k)
  ForkL ms  + Fork ms' = Fork (ms +^ ms')
  JoinL ms  + Join ms' = Join (ms +^ ms')

rowMajIso :: Iso (->) (L s a b) (b (a s))
rowMajIso = fwd :<-> rev
  where
    fwd :: L s a b -> b (a s)
    fwd (Scale s) = pureRep (pureRep s)
    fwd (f :|# g) = liftR2 (:*:) (fwd f) (fwd g)
    fwd (f :&# g) = fwd f :*: fwd g
    fwd (JoinL m) = cotraverse Comp1 $ fmap fwd m
    fwd (ForkL m) = Comp1 $ fmap fwd m
    rev :: b (a s) -> L s a b
    rev = undefined -- TODO: Write rev for toRowMajIso.

diagRep :: (Representable h, Eq (Rep h)) => a -> h a -> h (h a)
diagRep dflt as =
  tabulate (\ i -> tabulate (\ j -> if i == j then as `index` i else dflt))

instance Semiring s => Category (L s) where
  type Obj' (L s) a = V a
  id = isoRev rowMajIso (diagRep zero (pureRep one))
  Scale a   . Scale b   = Scale (a * b)           -- Scale denotation
  (p :&# q) . m         = p . m :&# q . m         -- binary product law
  m         . (p :|# q) = m . p :|# m . q         -- binary coproduct law
  (r :|# s) . (p :&# q) = r . p + s . q           -- biproduct law
  ForkL ms' . m         = ForkL (fmap (. m) ms')  -- n-ary product law
  m'        . JoinL ms  = JoinL (fmap (m' .) ms)  -- n-ary coproduct law
  JoinL ms' . ForkL ms  = sum (liftR2 (.) ms' ms) -- biproduct law

instance (V r, Semiring s) => CartesianR r (:.:) (L s) where
  fork = ForkL
  unfork (p :|# q)  = liftR2 (:|#) (unfork p) (unfork q)
  unfork (ForkL ms) = ms
  unfork (JoinL ms) = JoinL <$> distribute (unfork <$> ms)
-- {-# COMPLETE Fork :: L #-} -- Orphan COMPLETE pragmas not supported
-- (These are defined in Category.hs)

instance (V r, Foldable r, Semiring s) => CocartesianR r (:.:) (L s) where
  join = JoinL
  unjoin (p :&# p') = liftR2 (:&#) (unjoin p) (unjoin p')
  unjoin (JoinL ms) = ms
  unjoin (ForkL ms) = fmap ForkL (distribute (fmap unjoin ms))
-- {-# COMPLETE Join :: L #-} -- See complete pragma above

-- TODO: Add deriving capabilities
instance Semiring s => Monoidal (:*:) (L s) where
  f ### g = (inl . f) :|# (inr . g)
-- deriving via (ViaCartesian (:*:) (L s)) instance Monoidal (:*:) (L s)

-- TODO: Add deriving via capabilities.
-- Couldn't get constraints to work when defining this instance on the Via
-- type in Category.hs
instance (Representable r, Eq (Rep r), Semiring s) => MonoidalR r (:.:) (L s) where
  rmap fs = ForkL (liftR2 (.) fs exs)

-- Can't derive via (why?)
-- Error:
-- [bios] [E] The exact Name ‘k1’ is not in scope
--   Probable cause: you used a unique Template Haskell name (NameU),
--   perhaps via newName, but did not bind it
--   If that's it, then -ddump-splices might be useful
--
-- deriving via (ViaCartesian (:.:) (L s)) instance () => (MonoidalR r (:.:) (L s))

-- TODO: Move to Category.hs
-- See: https://en.wikipedia.org/wiki/Abelian_category#Definitions
instance Semiring s => Cartesian (:*:) (L s) where
  (&&&) = (:&#)
  unfork2 f = ((id :|# zero) . f, (zero :|# id) . f)
-- {-# COMPLETE (:&) :: L #-} -- See complete pragma above

-- TODO: Move to Category.hs
-- See: https://en.wikipedia.org/wiki/Abelian_category#Definitions
instance Semiring s => Cocartesian (:*:) (L s) where
  (|||) = (:|#)
  unjoin2 f = (f . (id :&# zero), f . (zero :&# id))
-- {-# COMPLETE (:|) :: L #-} -- See complete pragma above

instance Semiring s => Biproduct (:*:) (L s)

