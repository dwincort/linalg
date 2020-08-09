-- {-# OPTIONS_GHC -Wno-unused-imports #-} -- TEMP
{-# LANGUAGE UndecidableSuperClasses #-} -- see below
{-# LANGUAGE UndecidableInstances #-} -- see below

-- | Representable indices as objects

module Category.Index where

-- import qualified Prelude as P
import Prelude hiding (id,(.))
import GHC.Generics ((:*:),(:.:),Par1)
import Data.Functor.Rep

import Misc
import Category

-- Trie functors
class (Representable (Trie i), Rep (Trie i) ~ i) => HasTrie i where
  type Trie i :: * -> *

instance HasTrie () where
  type Trie () = Par1
instance C2 HasTrie i j => HasTrie (i :+ j) where
  type Trie (i :+ j) = Trie i :*: Trie j
instance C2 HasTrie i j => HasTrie (i :* j) where
  type Trie (i :* j) = Trie i :.: Trie j

newtype Indexed k i j = Indexed { unIndexed :: Trie i `k` Trie j }

class    Obj k (Trie i) => ObjI k i
instance Obj k (Trie i) => ObjI k i

-- Potential superclass cycle for ‘ObjI’
--   one of whose superclasses is ‘Obj’
--   one of whose superclass constraints is headed by a type family:
--     ‘Obj' k (Trie i)’
-- Use UndecidableSuperClasses to accept this
--
-- Illegal nested constraint ‘Obj k (Trie i)’
-- (Use UndecidableInstances to permit this)

instance Category k => Category (Indexed k) where
  type Obj' (Indexed k) = ObjI k
  id = Indexed id
  Indexed g . Indexed f = Indexed (g . f)

instance Monoidal k (:*:) => Monoidal (Indexed k) (:+) where
  Indexed f *** Indexed g = Indexed (f *** g)

instance Cartesian k (:*:) => Cartesian (Indexed k) (:+) where
  exl = Indexed exl
  exr = Indexed exr
  dup = Indexed dup

instance Comonoidal k (:*:) => Comonoidal (Indexed k) (:+) where
  Indexed f +++ Indexed g = Indexed (f +++ g)

instance Cocartesian k (:*:) => Cocartesian (Indexed k) (:+) where
  inl = Indexed inl
  inr = Indexed inr
  jam = Indexed jam

instance Biproduct k (:*:) => Biproduct (Indexed k) (:+)

-- TODO: generalize from (:*:) and (:+).

#if 0

type RepX r i = Rep r :* i

instance MonoidalR k r (:.:) => MonoidalR (Indexed k) r RepX where
  cross (fmap unIndexed -> fs) = Indexed (cross fs)

-- Hm. Needs unsaturated type synonym

#endif
