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

--------------------------------------------------------------------------------
-- Adjunction
--------------------------------------------------------------------------------

data Adjunction f u where
  Adjunction :: (Functor f, Functor u, Dom f ~ c, Cod f ~ d, Dom u ~ d, Cod u ~ c)
             => f -> u
             -> Nat c c (Identity c) (u :.: f) -- eta
             -> Nat d d (f :.: u) (Identity d) -- epsilon
             -> Adjunction f u

--------------------------------------------------------------------------------
-- Kan Extensions
--------------------------------------------------------------------------------

-- Universal property of left kan extensions. Needs to be a newtype to avoid
-- impredicative polymorphism errors.
newtype LanUP f k lan =
  LanUP (forall g. Functor g
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
  RanUP (forall g. Functor g
      => (g :.: k) ~> f
      -> g ~> ran
        )

data RightKanExt k f ran where
  Ran :: ran
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

limit :: limit
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

precomp :: Cod k ~ e
        => LanK k e toLan
        -> Precomp e k
        -> Adjunction (LanK k e toLan) (Precomp e k)
precomp l@(LanK mkLan) preK@(Precomp k) =
  Adjunction l preK eta epsilon
    where
      eta = Nat Identity (Comp preK l) $ \(Nat f _ c) ->
        case mkLan f of
          Lan _ nat _ -> nat

      epsilon = Nat (Comp l preK) Identity $ \(Nat f _ c) ->
        case mkLan (Comp f k) of
          Lan _ _ (LanUP up) ->
            up $ idNat (Comp f k)

