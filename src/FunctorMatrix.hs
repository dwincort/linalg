{-# LANGUAGE UndecidableInstances #-}

{- |
"Functor Matrices", or a "matrix" represented by a representable functor of
representable functors.
-}

module FunctorMatrix where

import CatPrelude

import qualified LinearFunction as F
import LinearFunction hiding (L(..))
import Category.Isomorphism

-------------------------------------------------------------------------------
-- | Representation and its denotation
-------------------------------------------------------------------------------

type V' a = (Foldable a, Representable a, Eq (Rep a))

class    V' a => V a
instance V' a => V a

type VR r = (V r, Representational1 r)

-- | Compositional linear map representation.
data L s f g where
  L :: (Representable f, Representable g) => { unL :: g (f s) } -> L s f g

instance LinearMap L where
  mu = fwd :<-> rev
    where
      fwd (L gfs) = F.L $ flip fmap gfs . dot
      rev (F.L m) = L $ collect m $ unL id

instance Category (L s) where
  type Obj' (L s) a = (Semiring s, V a)
  id = L basis
  L b . L a = L $ flip cotraverse a . dot <$> b

instance (Representable f, Representable g, Semiring s) => Additive (L s f g) where
  zero = L $ pureRep (pureRep zero)
  (+)  = pointwise (+)

pointwise :: (Representable f, Representable g) => (a -> b -> c) -> L a f g -> L b f g -> L c f g
pointwise f (L a) (L b) = L $ liftR2 (liftR2 f) a b


instance Semiring s => Cartesian (:*:) (L s) where
  L gfa &&& L g'fa = L $ gfa :*: g'fa
  unfork2 (L (x :*: y)) = (L x, L y)

pattern (:&) :: (Cartesian p k, Obj3 k a c d)
             => (a `k` c) -> (a `k` d) -> (a `k` (c `p` d))
pattern f :& g <- (unfork2 -> (f,g)) where (:&) = (&&&)
{-# COMPLETE (:&) :: L #-}

instance Semiring s => Cocartesian (:*:) (L s) where
  L gfa ||| L gf'a = L $ liftR2 (:*:) gfa gf'a
  unjoin2 (L l) = (L $ fstP <$> l, L $ sndP <$> l)
    where
      fstP (x :*: _) = x
      sndP (_ :*: y) = y

pattern (:|) :: (Cocartesian co k, Obj3 k a b c)
             => (a `k` c) -> (b `k` c) -> ((a `co` b) `k` c)
pattern f :| g <- (unjoin2 -> (f,g)) where (:|) = (|||)
{-# COMPLETE (:|) :: L #-}

instance (VR r, Semiring s) => CartesianR r (:.:) (L s) where
  fork   = L . Comp1 . fmap unL
  unfork = fmap L . unComp1 . unL

pattern Fork :: (CartesianR h p k, Obj2 k f g) => h (k f g) -> k f (p h g)
pattern Fork ms <- (unfork -> ms) where Fork = fork
{-# COMPLETE Fork :: L #-}

instance (VR r, Semiring s) => CocartesianR r (:.:) (L s) where
  join   = L . fmap Comp1 . distribute . fmap unL
  unjoin = fmap L . distribute . fmap unComp1 . unL

pattern Join :: (CocartesianR h p k, Obj2 k f g) => h (k f g) -> k (p h f) g
pattern Join ms <- (unjoin -> ms) where Join = join
{-# COMPLETE Join :: L #-}


instance Semiring s => Biproduct (:*:) (L s)
instance (VR r, Semiring s) => BiproductR r (:.:) (L s)

deriving via ViaCartesian (L s) instance Semiring s => Monoidal (:*:) (L s)

deriving via ViaCartesian (L s)
  instance (VR r, Semiring s) => MonoidalR r (:.:) (L s)
