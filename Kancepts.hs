{-# OPTIONS_GHC -fwarn-incomplete-patterns #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE StandaloneKindSignatures #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
module Kancepts where

import           Data.Kind
import           Prelude hiding (Functor, (.))

--------------------------------------------------------------------------------
-- Category
--------------------------------------------------------------------------------

class Category cat where
  src :: cat a b -> Obj cat a
  tgt :: cat a b -> Obj cat b
  (.) :: cat b c -> cat a b -> cat a c

-- Identify objects with their identity morphism
type Obj cat a = cat a a

-- Category with a single object
data One a b where
  One :: One () ()

instance Category One where
  src One = One
  tgt One = One
  One . One = One

data ElemA = ElemA
data ElemB = ElemB
-- Discrete category of two objects
data Two a b where
  A :: Two ElemA ElemA
  B :: Two ElemB ElemB

instance Category Two where
  src A = A
  src B = B
  tgt A = A
  tgt B = B
  A . A = A
  B . B = B

-- the Hask category
instance Category (->) where
  src _ = id
  tgt _ = id
  f . g = \x -> f (g x)

-- The category of categories. Morphisms are functors
type Cat :: (Type -> Type -> Type) -> (Type -> Type -> Type) -> Type
data Cat a b where
  Cat :: (Functor ftag, Dom ftag ~ a, Cod ftag ~ b)
      => ftag
      -> Cat a b

instance Category Cat where
  src (Cat f) = Cat Identity
  tgt (Cat f) = Cat Identity
  Cat f . Cat g = Cat (Comp f g)

--------------------------------------------------------------------------------
-- Functor
--------------------------------------------------------------------------------

class (Category (Dom ftag), Category (Cod ftag)) => Functor ftag where
  type Dom ftag :: Type -> Type -> Type
  type Cod ftag :: Type -> Type -> Type

  type (:%) ftag a :: Type

  (%) :: ftag
      -> Dom ftag a b
      -> Cod ftag (ftag :% a) (ftag :% b)

infixr 4 %

-- Functor composition
data g :.: f =
  Comp g f

instance (Functor f, Functor g, Cod f ~ Dom g) => Functor (g :.: f) where
  type Dom (g :.: f) = Dom f
  type Cod (g :.: f) = Cod g

  type (g :.: f) :% a = g :% (f :% a)

  Comp g f % m = g % (f % m)

-- Identity functor
data Identity (c :: Type -> Type -> Type) = Identity

instance Category c => Functor (Identity c) where
  type Dom (Identity c) = c
  type Cod (Identity c) = c

  type Identity c :% a = a

  Identity % m = m

-- Functor pre-composition
data Precomp e k where
  Precomp :: Functor k
          => k
          -> Precomp e k

instance Functor (Precomp (e :: Type -> Type -> Type) k) where

  type Dom (Precomp e k) = Nat (Cod k) e
  type Cod (Precomp e k) = Nat (Dom k) e

  type Precomp e k :% a = a :.: k

  Precomp k % m = whiskerLeft m k

--------------------------------------------------------------------------------
-- Natural Transformation
--------------------------------------------------------------------------------

type Nat :: (Type -> Type -> Type) -- Domain category
         -> (Type -> Type -> Type) -- Codomain category
         -> Type -> Type -> Type
data Nat d c f g where
  Nat :: (Functor f, Functor g, c ~ Cod f, c ~ Cod g, d ~ Dom f, d ~ Dom g)
      => f -> g -> (forall z. Obj d z -> c (f :% z) (g :% z)) -> Nat d c f g

type f ~> g = (Cod f ~ Cod g, Dom f ~ Dom g) => Nat (Dom f) (Cod f) f g

-- The identity natural transformation
idNat :: (Functor f, Dom f ~ d, Cod f ~ c)
      => f -> Nat d c f f
idNat f = Nat f f (f %)

-- Vertical composition of natural transformations forms a category
vertComp :: Nat d c g h -> Nat d c f g -> Nat d c f h
vertComp (Nat _ h n1) (Nat f _ n2) = Nat f h $ \o -> n1 o . n2 o

instance Category (Nat d c) where
  src (Nat d _ _) = idNat d
  tgt (Nat _ c _) = idNat c
  (.) = vertComp

whiskerLeft :: (Functor h, Dom h ~ e, Cod h ~ d)
            => Nat d c f g -> h -> Nat e c (f :.: h) (g :.: h)
whiskerLeft (Nat f g c) h = Nat (Comp f h) (Comp g h) $ \o -> c $ h % o

whiskerRight :: (Functor h, Cod h ~ e, Dom h ~ c)
             => Nat d c f g -> h -> Nat d e (h :.: f) (h :.: g)
whiskerRight (Nat f g c) h = Nat (Comp h f) (Comp h g) $ \o -> h % c o

-- Horizontal composition also yields a category but we can't express it here
horizComp :: Nat c e h i -> Nat d c f g -> Nat d e (h :.: f) (i :.: g)
horizComp n1@(Nat h _ _) n2@(Nat _ g _) =
  whiskerLeft n1 g . whiskerRight n2 h

rightUnitNT :: (Functor f, Dom f ~ d, Cod f ~ c)
            => f
            -> Nat d c (f :.: Identity d) f
rightUnitNT f = Nat (Comp f Identity) f (f %)

rightUnitNTInv :: (Functor f, Dom f ~ d, Cod f ~ c)
               => f
               -> Nat d c f (f :.: Identity d)
rightUnitNTInv f = Nat f (Comp f Identity) (f %)

associativeNT :: (Functor f, Functor g, Functor h, Cod h ~ Dom g, Cod g ~ Dom f
                 , Dom h ~ c, Cod f ~ d
                 )
              => f -> g -> h -> Nat c d ((f :.: g) :.: h) (f :.: (g :.: h))
associativeNT f g h = Nat (Comp (Comp f g) h) (Comp f (Comp g h)) (Comp f (Comp g h) %)

associativeNTInv :: (Functor f, Functor g, Functor h, Cod h ~ Dom g, Cod g ~ Dom f
                    , Dom h ~ c, Cod f ~ d
                    )
                 => f -> g -> h -> Nat c d (f :.: (g :.: h)) ((f :.: g) :.: h)
associativeNTInv f g h = Nat (Comp f (Comp g h)) (Comp (Comp f g) h) (Comp f (Comp g h) %)

--------------------------------------------------------------------------------
-- Adjunction
--------------------------------------------------------------------------------

-- This formulation of adjunctions is defined by a pair of natural
-- transformations rather than an isomorphism of hom-sets.
data Adjunction f u where
  Adjunction :: (Functor f, Functor u, Dom f ~ c, Cod f ~ d, Dom u ~ d, Cod u ~ c)
             => f -- left adjoint functor
             -> u -- right adjoint functor
             -> Nat c c (Identity c) (u :.: f) -- unit
             -> Nat d d (f :.: u) (Identity d) -- counit
             -> Adjunction f u

-- Given an adjunction F -| U, U* -| F* where U* is precomposition with U is
-- also an adjunction.
precompAdj :: (Cod f ~ c, Dom g ~ c, Dom f ~ Cod g)
           => Adjunction f u
           -> Adjunction (Precomp c u) (Precomp c f)
precompAdj (Adjunction f u unit counit) =
  Adjunction (Precomp u) (Precomp f) unit' counit'
    where
      unit' = Nat Identity (Comp (Precomp f) (Precomp u)) $ \(Nat z _ _) ->
        associativeNTInv z u f . whiskerRight unit z . rightUnitNTInv z
      counit' = Nat (Comp (Precomp u) (Precomp f)) Identity $ \(Nat z _ _) ->
        rightUnitNT z . whiskerRight counit z . associativeNT z f u

--------------------------------------------------------------------------------
-- Kan Extensions
--------------------------------------------------------------------------------

-- Universal property of left kan extensions. Needs to be a newtype to avoid
-- impredicative polymorphism errors.
newtype LanUP f k lan =
  LanUP (forall g. (Functor g, Dom g ~ Dom lan, Cod g ~ Cod lan)
      => f ~> (g :.: k)
      -> lan ~> g
        )

data LeftKanExt k f lan where
  Lan :: (Functor lan, Dom lan ~ Cod k, Cod lan ~ Cod f)
      => lan
      -> f ~> (lan :.: k)
      -> LanUP f k lan
      -> LeftKanExt k f lan

-- Universal property of right kan extensions
newtype RanUP f k ran =
  RanUP (forall g. (Functor g, Dom g ~ Dom ran, Cod g ~ Cod ran)
      => (g :.: k) ~> f
      -> g ~> ran
        )

data RightKanExt k f ran where
  Ran :: (Functor ran, Dom ran ~ Cod k, Cod ran ~ Cod f)
      => ran
      -> (ran :.: k) ~> f
      -> RanUP f k ran
      -> RightKanExt k f ran

--------------------------------------------------------------------------------
-- (Co)limits
--------------------------------------------------------------------------------

-- The left kan extension of a functor F : C -> D along the unique functor
-- ! : C -> 1 is the colimit of F in D, each existing iff the other does.

type ConstOne :: (Type -> Type -> Type) -> Type
data ConstOne c = ConstOne

instance Category c => Functor (ConstOne c) where
  type Dom (ConstOne c) = c
  type Cod (ConstOne c) = One
  type ConstOne c :% a = ()
  ConstOne % _ = One

colimit :: (Functor colimit, Cod colimit ~ Cod f, Dom colimit ~ One)
        => colimit
        -> Nat (Dom f) (Cod f) f (colimit :.: ConstOne (Dom f))
        -> LanUP f (ConstOne (Dom f)) colimit
        -> LeftKanExt (ConstOne (Dom f)) f colimit
colimit = Lan

-- The colimit of 2 in Set is the coproduct Either in Hask

data TwoToHask = TwoToHask

instance Functor TwoToHask where
  type Dom TwoToHask = Two
  type Cod TwoToHask = (->)
  type TwoToHask :% a = a
  TwoToHask % A = id
  TwoToHask % B = id

-- A constant functor from 1 to Hask selecting the coproduct of 2 objects
data Coproduct = Coproduct

instance Functor Coproduct where
  type Dom Coproduct = One
  type Cod Coproduct = (->)
  type Coproduct :% a = Either ElemA ElemB
  Coproduct % One = id

coproduct :: LeftKanExt (ConstOne Two) TwoToHask Coproduct
coproduct = colimit Coproduct eta sigma
  where
    eta :: Nat Two (->) TwoToHask (Coproduct :.: ConstOne Two)
    eta = Nat TwoToHask (Comp Coproduct ConstOne) $ \case
      A -> Left
      B -> Right

    sigma :: LanUP TwoToHask (ConstOne Two) Coproduct
    sigma = LanUP $ \case
      Nat TwoToHask (Comp g ConstOne) c ->
        Nat Coproduct g $ \case
          One -> either (c A) (c B)

-- Likewise, the right kan extension defines the limit

limit :: (Functor limit, Cod limit ~ Cod f, Dom limit ~ One)
      => limit
      -> Nat (Dom f) (Cod f) (limit :.: ConstOne (Dom f)) f
      -> RanUP f (ConstOne (Dom f)) limit
      -> RightKanExt (ConstOne (Dom f)) f limit
limit = Ran

-- Constant functor from 1 to Hask selecting the product of 2 objects
data Product = Product

instance Functor Product where
  type Dom Product = One
  type Cod Product = (->)
  type Product :% a = (ElemA, ElemB)
  Product % One = id

product :: RightKanExt (ConstOne Two) TwoToHask Product
product = limit Product mu delta
  where
    mu :: Nat Two (->) (Product :.: ConstOne Two) TwoToHask
    mu = Nat (Comp Product ConstOne) TwoToHask $ \two (a, b) ->
      case two of
        A -> a
        B -> b

    delta :: RanUP TwoToHask (ConstOne Two) Product
    delta = RanUP $ \case
      Nat (Comp g ConstOne) TwoToHask c ->
        Nat g Product $ \One z ->
          (c A z, c B z)

--------------------------------------------------------------------------------
-- Adjunctions of precomposition with K
--------------------------------------------------------------------------------

-- If, for a fixed K : C -> D and E, the left and right kan extensions of any
-- functor F : C -> E along K exist, then these define left and right adjoints
-- to the pre-composition functor K* : E^D -> E^C

-- Given a functor K : A -> B, if for any functor F : A -> E we know how to
-- build a left kan extension of F along K, then the functor LanK is the
-- mapping from all F's to their corresponding left kan extensions along K.
data LanK k (e :: Type -> Type -> Type) toLan where
  LanK :: (forall f. f -> LeftKanExt k f (toLan f))
       -> LanK k e toLan

instance Functor (LanK k e toLan) where
  type Dom (LanK k e toLan) = Nat (Dom k) e
  type Cod (LanK k e toLan) = Nat (Cod k) e

  type LanK k e toLan :% f = toLan f

  LanK mkLan % aToB@(Nat a b _) =
    case mkLan a of
      Lan _ _ (LanUP up) ->
        case mkLan b of
          Lan _ bToLK _ -> up $ bToLK . aToB

leftAdjointToPrecomposition
  :: (Functor k, Cod k ~ e)
  => LanK k e toLan
  -> k
  -> Adjunction (LanK k e toLan) (Precomp e k)
leftAdjointToPrecomposition l@(LanK mkLan) k =
  Adjunction l preK eta epsilon
    where
      eta = Nat Identity (Comp preK l) $ \(Nat f _ _) ->
        case mkLan f of
          Lan _ nat _ -> nat

      epsilon = Nat (Comp l preK) Identity $ \(Nat f _ _) ->
        case mkLan (Comp f k) of
          Lan _ _ (LanUP up) ->
            up $ idNat (Comp f k)

      preK = Precomp k

data RanK k (e :: Type -> Type -> Type) toRan where
  RanK :: (forall f. f -> RightKanExt k f (toRan f))
       -> RanK k e toRan

instance Functor (RanK k e toRan) where
  type Dom (RanK k e toRan) = Nat (Dom k) e
  type Cod (RanK k e toRan) = Nat (Cod k) e

  type RanK k e toRan :% f = toRan f

  RanK mkRan % aToB@(Nat a b _) =
    case mkRan a of
      Ran _ rkToA _ ->
        case mkRan b of
          Ran _ _ (RanUP bUP) -> bUP $ aToB . rkToA

rightAdjointToPrecomposition
  :: (Functor k, Cod k ~ e)
  => RanK k e toRan
  -> k
  -> Adjunction (Precomp e k) (RanK k e toRan)
rightAdjointToPrecomposition r@(RanK mkRan) k =
  Adjunction preK r eta epsilon
    where
      eta = Nat Identity (Comp r preK) $ \(Nat f _ _) ->
        case mkRan (Comp f k) of
          Ran _ _ (RanUP rUP) ->
            rUP $ idNat (Comp f k)

      epsilon = Nat (Comp preK r) Identity $ \(Nat f _ _) ->
        case mkRan f of
          Ran _ nat _ -> nat

      preK = Precomp k

--------------------------------------------------------------------------------
-- Adjunctions as Kan extensions
--------------------------------------------------------------------------------

-- If F is left-adjoint to G with unit : 1 => GF and counit : FG => 1, then
-- (G, unit) is the left kan extension of the identity functor along F, and
-- (F, counit) is the right kan extension of the identity functor along G.
-- Conversely, if (G, unit) is a left kan extension of the identity functor
-- along F and if F preserves this Kan extension then F -| G.

leftKanFromAdjunction :: (Cod g ~ e, Dom f ~ e)
                      => Adjunction f g
                      -> LeftKanExt f (Identity e) g
leftKanFromAdjunction (Adjunction _ g unit counit) =
  Lan g unit up
    where
      up = LanUP $ \(Nat Identity (Comp x _) c1) ->
        Nat g x $ \o ->
          case whiskerRight counit x of
            Nat _ _ c2 ->
              c2 o . c1 (g % o)

leftKanToAdjunction :: (Functor f, Cod g ~ e, Dom f ~ e)
                    => LeftKanExt f (Identity e) g
                    -> LeftKanExt f f (f :.: g) -- it's preserved by F
                    -> Adjunction f g
leftKanToAdjunction (Lan _ unit _)
                    (Lan (Comp f g) _ (LanUP up)) =
  Adjunction f g unit counit
    where
      counit = up (Nat f (Comp Identity f) (f %))

rightKanFromAdjunction :: (Dom g ~ e, Cod f ~ e)
                       => Adjunction f g
                       -> RightKanExt g (Identity e) f
rightKanFromAdjunction (Adjunction f _ unit counit) =
  Ran f counit up
    where
      up = RanUP $ \nat@(Nat (Comp x _) Identity _) ->
        Nat x f $ \o ->
          case whiskerRight unit x of
            Nat _ _ c2 ->
              case whiskerLeft nat f of
                Nat _ _ c3 ->
                  c3 o . c2 o . (x % o)

rightKanToAdjunction :: (Functor g, Dom g ~ e, Cod f ~ e)
                     => RightKanExt g (Identity e) f
                     -> RightKanExt g g (g :.: f)
                     -> Adjunction f g
rightKanToAdjunction (Ran _ counit _)
                     (Ran (Comp g f) _ (RanUP up)) =
  Adjunction f g unit counit
    where
      unit = up (Nat (Comp Identity g) g (g %))

--------------------------------------------------------------------------------
-- Generalization of Yoneda Lemma
--------------------------------------------------------------------------------
