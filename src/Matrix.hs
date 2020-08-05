{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE NoStarIsType #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE Rank2Types #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE UndecidableInstances #-}

{-# OPTIONS_GHC -Wno-name-shadowing #-}
{-# OPTIONS_GHC -Wno-unticked-promoted-constructors #-}

module Matrix where

import Prelude hiding (id, (.))

import qualified Control.Arrow as A
import qualified Data.Finite   as F

import Control.Category  (Category(..))
import Data.Bool         (bool)
import Data.Coerce       (Coercible, coerce)
import Data.Constraint   ((:-)(..), Dict(..), withDict, (\\))
import Data.Distributive (Distributive(..))
import Data.Finite       (Finite)
import Data.Functor.Rep  (Representable(..), liftR2, pureRep)
import Data.Kind         (Constraint, Type)
import Data.Maybe        (fromJust)
import Data.Proxy        (Proxy(..))
import Data.UniformPair  (Pair(..))
import Data.Vector.Sized (Vector)
import Data.Void         (Void, absurd)
import GHC.Generics      ((:*:)(..), (:.:)(..), Par1(..))
import GHC.TypeLits      (type (*), type (+), KnownNat, Nat, SomeNat(..), natVal, someNatVal)
import Unsafe.Coerce     (unsafeCoerce)


--------------------------------------------------------------------------------
-- Categories and Isomorphisms
--------------------------------------------------------------------------------

-- We start with some isomorphism code, basically lifted from Conal's paper draft.
-- There may be a few extraneous things, but I basically only bring in what I'll need.

data a ≌ b = (:⇆)
  { isoFwd :: (a -> b)
  , isoRev :: (b -> a)
  }

instance Category (≌) where
  id = id :⇆ id
  (g :⇆ g') . (f :⇆ f') = (g . f) :⇆ (f' . g')

class Category k => Closed k where
  closed :: k d c -> k a b -> k (c -> a) (d -> b)

instance Closed (->) where
  closed dc ab ca = ab . ca . dc

instance Closed (≌) where
  closed (p :⇆ p') (q :⇆ q') = closed p q :⇆ closed p' q'


class Category k => MonoidalP k where
  (***) :: k a c -> k b d -> k (a,b) (c,d)

instance MonoidalP (->) where
  (***) = (A.***)

instance MonoidalP (≌) where
  (f :⇆ f') *** (g :⇆ g') = (f *** g) :⇆ (f' *** g')


class Category k => MonoidalS k where
  (+++) :: k a c -> k b d -> k (Either a b) (Either c d)

instance MonoidalS (->) where
  (+++) = (A.+++)

instance MonoidalS (≌) where
  (f :⇆ f') +++ (g :⇆ g') = (f +++ g) :⇆ (f' +++ g')


dom :: Closed k => k d c -> k (c -> a) (d -> a)
dom f = closed f id

inv :: a ≌ b -> b ≌ a
inv (fwd :⇆ rev) = rev :⇆ fwd

type f ⩧ g = forall a. f a ≌ g a

repIso :: Representable f => f a ≌ (Rep f -> a)
repIso = index :⇆ tabulate

coerceIso :: Coercible a b => a ≌ b
coerceIso = coerce :⇆ coerce

fmapIso :: Functor f => a ≌ b -> f a ≌ f b
fmapIso (f :⇆ g) = (fmap f :⇆ fmap g)

reindex :: (Representable f, Representable g) => (Rep g ≌ Rep f) -> (f ⩧ g)
reindex h = inv repIso . dom h . repIso

finU1 :: Void ≌ Finite 0
finU1 = absurd :⇆ error "Impossible"

finPar1 :: () ≌ Finite 1
finPar1 = const (F.finite 0) :⇆ const ()

finSum :: (KnownNat m, KnownNat n) => Either (Finite m) (Finite n) ≌ Finite (m + n)
finSum = F.combineSum :⇆ F.separateSum

finProduct :: (KnownNat m, KnownNat n) => (Finite m, Finite n) ≌ Finite (m * n)
finProduct = F.combineProduct :⇆ F.separateProduct


--------------------------------------------------------------------------------
-- Finite Cardinality
--------------------------------------------------------------------------------
-- I also bring in HasFin and some Finite support, once agian lifted from Conal's draft.

type KnownCard a = KnownNat (Card a)

class KnownCard a => HasFin a where
  type Card a :: Nat
  fin :: a ≌ Finite (Card a)

instance HasFin Void where
  type Card Void = 0
  fin = finU1

instance HasFin () where
  type Card () = 1
  fin = finPar1

-- Special casing for UniformPair
instance HasFin Bool where
  type Card Bool = 2
  fin = (F.finite . bool 0 1) :⇆ ((==1) . F.getFinite)

instance KnownNat n => HasFin (Finite n) where
  type Card (Finite n) = n
  fin = id

instance (KnownNat (Card a + Card b), HasFin a, HasFin b) => HasFin (Either a b) where
  type Card (Either a b) = Card a + Card b
  fin = finSum . (fin +++ fin)

instance (KnownNat (Card a * Card b), HasFin a, HasFin b) => HasFin (a, b) where
  type Card (a, b) = Card a * Card b
  fin = finProduct . (fin *** fin)

-- | Isomorphism between `f a` and `g a` when the cardinalities of the representations
-- of `f` and `g` are equal.
cardRepIso :: forall f g a. (Card (Rep f) ~ Card (Rep g), HasFin (Rep f), HasFin (Rep g), Representable f, Representable g)
  => f a ≌ g a
cardRepIso = reindex $ inv fin . fin





--------------------------------------------------------------------------------
-- Abelian Category
--------------------------------------------------------------------------------

-- Here I define what an abelian category is.  This could certainly be generalized
-- in the future (for intsance, by depending on a `Category` superclass), but I
-- refrain from generalization here mostly because of the constrained nature.
-- That is, the way that I defined `Matrix` means that I need to be given the
-- `Matrixy` constraint when I use these operations.  An alternative data type
-- declaration may be able to help with this, for instance from constrained-categories.
class AbelianCat (cat :: k -> k -> Type) where
  type Constrained cat (x :: k) :: Constraint
  zero :: (Constrained cat a, Constrained cat b) => cat a b
  (⊕)  :: (Constrained cat a, Constrained cat b) => cat a b -> cat a b -> cat a b
  (⊖)  :: (Constrained cat a, Constrained cat b) => cat a b -> cat a b -> cat a b
  iden :: Constrained cat a => cat a a
  (∘)  :: (Constrained cat a, Constrained cat b, Constrained cat c) => cat b c -> cat a b -> cat a c
  mmm  :: (Constrained cat a, Constrained cat b, Constrained cat c) => cat a b -> cat b c -> cat a c
  mmm = flip (∘)


--------------------------------------------------------------------------------
-- Matrix Data Type
--------------------------------------------------------------------------------

-- Finally, I define the Matrix type.  It's basically just composition, where
-- we assume that we have a few constraints on `f` and `g`.
newtype Matrix a f g = Matrix { unMatrix :: f (g a) }
  deriving (Show, Eq)

-- It's convenient to have some constraints on the `f` and `g` from `Matrix`.  Whenever
-- I use them, I'll typically ask for `f` and `g` to be `Matrixy`.
type Matrixy f = (Representable f, Foldable f, HasFin (Rep f))
type Matrixy2 f g = (Matrixy f, Matrixy g)
type Matrixy3 f g h = (Matrixy f, Matrixy g, Matrixy h)

-- Shorthand to get the cardinality of f, or the finite of the cardinatlity of f.
type CardOf f = Card (Rep f)
type FinOf f = Finite (CardOf f)

constMatrix :: forall a f g. (Matrixy2 f g) => a -> Matrix a f g
constMatrix = Matrix . pureRep . pureRep

pointwise :: forall f g a b c. (Matrixy2 f g) => (a -> b -> c) -> Matrix a f g -> Matrix b f g -> Matrix c f g
pointwise f (Matrix a) (Matrix b) = Matrix $ liftR2 (liftR2 f) a b

buildMatrix :: forall a f g. (Matrixy2 f g) => (Rep f -> Rep g -> a) -> Matrix a f g
buildMatrix f = Matrix $ tabulate $ tabulate . f

buildMatrixFinite :: forall a f g. (Matrixy2 f g)
  => (FinOf f -> FinOf g -> a) -> Matrix a f g
buildMatrixFinite f = buildMatrix $ \frep grep -> f (isoFwd fin frep) (isoFwd fin grep)

underMatrixIso :: f (g a) ≌ f' (g' a') -> Matrix a f g ≌ Matrix a' f' g'
underMatrixIso i = inv coerceIso . i . coerceIso


--------------------------------------------------------------------------------
-- Strassen
--------------------------------------------------------------------------------
-- Our first look at the Strassen algorithm.  Here, we require that the inputs be
-- 2x2 matrices of matrices.
--
-- Note that the inner "multiplications" use the `AbelianCat` instance for
-- `Matrix a`.  When we're done, that instance will itself call `strassen` when
-- appropriate, so we will get recursive strassen multiplication.
strassen
  :: (Matrixy3 f g h, AbelianCat (Matrix a))
  => Matrix (Matrix a f g) Pair Pair -> Matrix (Matrix a g h) Pair Pair -> Matrix (Matrix a f h) Pair Pair
strassen (Matrix ((a11 :# a12) :# (a21 :# a22))) (Matrix ((b11 :# b12) :# (b21 :# b22))) =
  Matrix ((m1⊕m4⊖m5⊕m7 :# m3⊕m5) :# (m2⊕m4 :# m1⊖m2⊕m3⊕m6))
  where
    m1 = (a11⊕a22) `mmm` (b11⊕b22)
    m2 = (a21⊕a22) `mmm` b11
    m3 = a11 `mmm` (b12⊖b22)
    m4 = a22 `mmm` (b21⊖b11)
    m5 = (a11⊕a12) `mmm` b22
    m6 = (a21⊖a11) `mmm` (b11⊕b12)
    m7 = (a12⊖a22) `mmm` (b21⊕b22)


--------------------------------------------------------------------------------
-- Matrix Block Isomorphisms
--------------------------------------------------------------------------------

-- A Matrix of matrices is can be flattened to a matrix and vice versa.  This
-- isomorphism witnesses this.
--
-- Recall that a `Matrix a f g` is essentially just a `f (g a)`.  So, a matrix
-- of matrices is a `f (g (f' (g' a)))`.  By swapping the order of `g` and `f'`,
-- we end up grouping the `f` and `f'` as well as the `g` and `g'` together.  We
-- can then compose those two pairs, and we're left with a flattened matrix.
joinMatrixIso
  :: (Functor f, Representable f', Representable g)
  => Matrix (Matrix a f' g') f g ≌ Matrix a (f :.: f') (g :.: g')
joinMatrixIso = joinMatrix :⇆ flatMatrix
  where
    joinMatrix (Matrix x) = Matrix $ Comp1 $ fmap Comp1 . distribute . fmap unMatrix <$> x
    flatMatrix (Matrix (Comp1 x)) = Matrix $ fmap Matrix . distribute . fmap unComp1 <$> x


-- Now let's take the idea of a matrix of matrices one step further into the
-- realm of cardinalities.  This isomorphism says that if the cardinalities of f
-- and g can each be factored and there exists f' and f'' as well as g' and g''
-- with the factors of the cardinalities of f and g respectively, then we can
-- convert an fxg matrix into a block matrix.
blockMatrixIso
  :: forall f f' f'' g g' g'' a.
    ((CardOf f' * CardOf f'') ~ CardOf f,
     (CardOf g' * CardOf g'') ~ CardOf g,
     Matrixy3 f f' f'', Matrixy3 g g' g'')
  => Matrix a f g ≌ Matrix a (f' :.: f'') (g' :.: g'')
blockMatrixIso = underMatrixIso $ fmapIso (cardRepIso @g @(g' :.: g'')) . (cardRepIso @f @(f' :.: f''))


-- A convenient shorthand for saying that the size of y is half the size of x.
type HalfCard x y = (2 * CardOf y) ~ CardOf x

-- | This is simply `blockMatrixIso` specialized to `Pair` to yield a 2x2 block.
pairsMatrixIso
  :: forall f g f' g' a.
    (HalfCard f f', HalfCard g g', Matrixy2 f g, Matrixy2 f' g')
  => Matrix a f g ≌ Matrix a (Pair :.: f') (Pair :.: g')
pairsMatrixIso = blockMatrixIso @f @Pair @f' @g @Pair @g'


--------------------------------------------------------------------------------
-- Generalized Strassen and Matrix Composition
--------------------------------------------------------------------------------

-- We now have a more general form of Strassen.  Here, we don't care what `f`, `g`, and `h`
-- are so long as we're provided `f'`, `g'`, and `h'` that are half their cardinalities
-- respectively.
strassen' :: forall f g h f' g' h' a.
  (Matrixy3 f g h, Matrixy3 f' g' h', HalfCard f f', HalfCard g g', HalfCard h h', AbelianCat (Matrix a))
  => Matrix a f g -> Matrix a g h -> Matrix a f h
strassen' a b = isoRev (pairsMatrixIso @f @h @f' @h') $ isoFwd joinMatrixIso $ strassen
  (isoRev joinMatrixIso $ isoFwd (pairsMatrixIso @f @g @f' @g') a)
  (isoRev joinMatrixIso $ isoFwd (pairsMatrixIso @g @h @g' @h') b)


-- With our generalized Strassen, we can now write a generalized matrix composition
-- function that will use Strassen when possible and do the naive set of multiplications
-- otherwise.
--
-- Note that we're not pattern matching in the traditional sense on the _form_ of
-- the input matrices.  Rather, we're matching on the _cardinalities_ of the dimensions
-- of the input matrices.
matrixCompose :: forall f g h a.
  (Matrixy3 f g h, Num a) -- Really only need Semiring a
  => Matrix a g h -> Matrix a f g -> Matrix a f h
matrixCompose = case (anyOnes, isEven @(CardOf f), isEven @(CardOf g), isEven @(CardOf h)) of
  -- In this first case, we know that the cardinality of `f`, `g`, or `h` is 1.  This is
  -- the base case, and it means that we should do naive multiplication.
  (True,_,_,_) -> \(Matrix b) (Matrix a) ->
    Matrix $ flip fmap (distribute b) . (\x y -> sum $ liftR2 (*) x y) <$> a
  -- In this second case, we know that the cardinalities of `f`, `g`, and `h` are
  -- all even.  This means we can use Strassen, so we do.
  (False, Just (IsEven (Proxy :: Proxy i)), Just (IsEven (Proxy :: Proxy j)), Just (IsEven (Proxy :: Proxy k))) ->
    flip $ strassen' @f @g @h @(Vector i) @(Vector j) @(Vector k)
  -- In the following three cases, we find that one of the three cardinalities is
  -- not even.  In each case, we extend that dimension by one row/column of zeros,
  -- perform a recursive composition call, and then strip out the added row/column.
  (False, Nothing, _, _) -> \a (Matrix fga) ->
    (\(Matrix (fha :*: _)) -> Matrix fha) $
    matrixCompose a (Matrix $ (fga :*: (Par1 $ pureRep 0))) -- add a row of zeros to `b` so that it will be even
    \\ knownNatSum @(CardOf f) @1
  (False, _, Nothing, _) -> \(Matrix gha) (Matrix fga) ->
    matrixCompose (Matrix $ (gha :*: (Par1 $ pureRep 0))) (Matrix $ (:*: Par1 0) <$> fga)
    \\ knownNatSum @(CardOf g) @1
  (False, _, _, Nothing) -> \(Matrix gha) b ->
    (\(Matrix fh'a) -> Matrix $ (\(fha :*: _) -> fha) <$> fh'a) $
    matrixCompose (Matrix $ (:*: Par1 0) <$> gha) b
    \\ knownNatSum @(CardOf h) @1
  where
    -- The base case is when any dimension is length 1
    anyOnes = natVal @(CardOf f) Proxy <= 1
           || natVal @(CardOf g) Proxy <= 1
           || natVal @(CardOf h) Proxy <= 1


-- With composition defined, we can now write our AbelianCat instance for `Matrix`.
-- We need `Num` for `+`, `-`, `*`, `fromInteger 0`, and `fromInteger 1`.  Perhaps
-- we should make our own type classes to represent these concepts.
instance Num a => AbelianCat (Matrix a) where
  type Constrained (Matrix a) x = Matrixy x
  zero = constMatrix 0
  (⊕)  = pointwise (+)
  (⊖)  = pointwise (-)
  iden = buildMatrixFinite $ (bool 0 1 .) . (==)
  (∘)  = matrixCompose


--------------------------------------------------------------------------------
-- Relation to TYM and Conal's LinAlg
--------------------------------------------------------------------------------

-- Our main effort is done, and in this section, I'll just play around with some
-- isomorphisms between this representation and one that uses more explicit
-- forks and joins.

forkProd :: (Matrix a f g, Matrix a f' g) ≌ Matrix a (f :*: f') g
forkProd = fwd :⇆ rev
  where
    fwd (Matrix fga, Matrix f'ga) = Matrix $ fga :*: f'ga
    rev (Matrix (x :*: y)) = (Matrix x, Matrix y)

joinProd :: Representable f => (Matrix a f g, Matrix a f g') ≌ Matrix a f (g :*: g')
joinProd = fwd :⇆ rev
  where
    fwd (Matrix fga, Matrix fg'a) = Matrix $ liftR2 (:*:) fga fg'a
    rev (Matrix x) = (Matrix $ fstP <$> x, Matrix $ sndP <$> x)
    fstP (x :*: _) = x
    sndP (_ :*: y) = y

forkComp :: Functor f => f (Matrix a f' g) ≌ Matrix a (f :.: f') g
forkComp = fwd :⇆ rev
  where
    fwd = Matrix . Comp1 . fmap unMatrix
    rev = fmap Matrix . unComp1 . unMatrix

joinComp :: (Distributive g, Distributive f) => g (Matrix a f g') ≌ Matrix a f (g :.: g')
joinComp = fwd :⇆ rev
  where
    fwd = Matrix . fmap Comp1 . distribute . fmap unMatrix
    rev = fmap Matrix . distribute . fmap unComp1 . unMatrix

isZero :: (Eq a, Num a, Foldable f, Foldable g) => Matrix a f g -> Bool
isZero (Matrix x) = all (== 0) (Comp1 x)


-- While we're playing around, here's a nice and quick definition of kronecker
-- multiplication.  It's more like `pointwise` than `composeMatrix`, which means
-- it may not have any denotational meaning for linear maps.  However, it does
-- have meaning for matrices.
kronecker :: (Matrixy2 f g, Matrixy2 f' g')
  => (a -> b -> c) -> Matrix a f g -> Matrix b f' g' -> Matrix c (f :.: f') (g :.: g')
kronecker op (Matrix x) (Matrix y) =
  Matrix $ Comp1 $ fmap Comp1 . distribute . fmap (\a -> fmap (op a) <$> y) <$> x


--------------------------------------------------------------------------------
-- Matrix with existential shape parameters
--------------------------------------------------------------------------------

-- Our ultimate definition of `matrixCompose` didn't actually need to pattern
-- match on `f` or `g`.  Indeed, the only things we care about in `Matrix a f g`
-- are the cardinalities of `f` and `g`.  This thinking inspires this
-- new data type, which has an existential `f` and `g` and exposes the
-- cardinalities only.
data MatrixNM a n m where
  MatrixNM :: forall a f g. Matrixy2 f g => f (g a) -> MatrixNM a (CardOf f) (CardOf g)

-- | This is isomorphic to any `Matrix` with the right cardinalities.
matrixNMIso :: forall f g n m a. (Matrixy2 f g, CardOf f ~ n, CardOf g ~ m) => MatrixNM a n m ≌ Matrix a f g
matrixNMIso = (:⇆)
  { isoFwd = \(MatrixNM x) -> Matrix (isoFwd (fmapIso cardRepIso . cardRepIso) x)
  , isoRev = \(Matrix   x) -> MatrixNM x
  }

-- | A version of `matrixNMIso` specialized to `Vector` matrices, to ease type inference.
vectorMatrixNMIso :: (KnownNat n, KnownNat m) => MatrixNM a n m ≌ Matrix a (Vector n) (Vector m)
vectorMatrixNMIso = matrixNMIso

instance Eq a => Eq (MatrixNM a n m) where
  MatrixNM x == y = and $
    liftR2 (==) (Comp1 x) (Comp1 $ unMatrix $ isoFwd matrixNMIso y)

instance (KnownNat n, KnownNat m, Show a) => Show (MatrixNM a n m) where
  show = show . isoFwd vectorMatrixNMIso

-- Because we have an isomorphism between MatrixNM and Matrix, we don't need to
-- do any extra work to get instances like `AbelianCat`.
instance Num a => AbelianCat (MatrixNM a) where
  type Constrained (MatrixNM a) x = KnownNat x
  zero  = isoRev vectorMatrixNMIso zero
  x ⊕ y = isoRev vectorMatrixNMIso $ isoFwd vectorMatrixNMIso x ⊕ isoFwd vectorMatrixNMIso y
  x ⊖ y = isoRev vectorMatrixNMIso $ isoFwd vectorMatrixNMIso x ⊖ isoFwd vectorMatrixNMIso y
  iden  = isoRev vectorMatrixNMIso iden
  x ∘ y = isoRev vectorMatrixNMIso $ isoFwd vectorMatrixNMIso x ∘ isoFwd vectorMatrixNMIso y

buildMatrixNM :: forall n m a. (KnownNat n, KnownNat m)
  => (Finite n -> Finite m -> a) -> MatrixNM a n m
buildMatrixNM = isoRev vectorMatrixNMIso . buildMatrixFinite



--------------------------------------------------------------------------------
-- Type Arithmetic axioms
--------------------------------------------------------------------------------

-- The following code is some hacking to get around GHC's limitations with
-- type level arithmetic.

-- A value of type `IsEven n` provides proof of evenness in the form of n/2.
data IsEven n where
  IsEven :: forall n n'. (KnownNat n', (2 * n') ~ n) => Proxy n' -> IsEven n

-- A value level version of `IsEven`.
isEven :: forall n. KnownNat n => Maybe (IsEven n)
isEven = case natVal @n Proxy of
  x | even x -> case fromJust $ someNatVal (x `div` 2) of
    SomeNat (p :: Proxy n') -> withDict (proof @n') $ Just $ IsEven p
  _ -> Nothing
  where
    -- This proof is generally bogus (note the unsafeCoerce), but true where we use it.
    proof :: forall n'. Dict ((2 * n') ~ n)
    proof = unsafeCoerce $ Dict @()

-- | If n and m are KnownNats, then surely n+m is a KnownNat.
knownNatSum :: forall n m. (KnownNat n, KnownNat m) :- KnownNat (n+m)
knownNatSum = Sub $ case fromJust $ someNatVal $ (natVal @n Proxy) + (natVal @m Proxy) of
  SomeNat (_ :: Proxy n') -> withDict (proof @n') Dict
  where
    -- This proof is generally bogus (note the unsafeCoerce), but true where we use it.
    proof :: forall n'. Dict ((n + m) ~ n')
    proof = unsafeCoerce $ Dict @()


--------------------------------------------------------------------------------
-- Tests and examples
--------------------------------------------------------------------------------

-- test and shouldBe are a couple simple test helpers.

test :: String -> String -> IO ()
test a b = putStrLn $ a <> ": " <> b

shouldBe :: Show a => a -> String -> String
shouldBe a b = show a <> " should be " <> b



-- First, a quick test that our `IsEven` code works properly.
isEvenTest :: forall n. KnownNat n => String
isEvenTest = case isEven @n of
  Nothing         -> "Not Even"
  Just (IsEven p) -> show $ natVal p

-- | A row-vector [1,2,3,4,5]
vec5 :: MatrixNM Integer 1 5
vec5 = buildMatrixNM $ \_ c -> 1 + F.getFinite c

-- A matrix that when composed with a vector will sum all elements in the vector.
-- Also known as a matrix where every element is 1.
sumMatrix :: forall n a. (Num a, KnownNat n) => MatrixNM a n n
sumMatrix = buildMatrixNM $ \_ _ -> 1

main :: IO ()
main = do
  test "isEvenTest @1" $ isEvenTest @1 `shouldBe` show "Not Even"
  test "isEvenTest @6" $ isEvenTest @6 `shouldBe` show "3"
  test "iden @_ @(MatrixNM Int) @5" $ show $ iden @_ @(MatrixNM Int) @5
  test "1x5 vector [1,2,3,4,5]" $ show vec5
  test "1x5 times a 5x5 identity" $ show $ iden ∘ vec5
  test "1x1 identity times 1x5" $ show $ vec5 ∘ iden
  test "5x5 sumMatrix times 5x5 identity" $ show $ sumMatrix @5 @Int ∘ iden
  test "1x5 vector times 5x5 sumMatrix" $ show $ sumMatrix ∘ vec5

-- I don't know of a test that can show that strassen is going on under the hood,
-- but it is.  One simple method to show this is to use some trace statements
-- to follow execution.
