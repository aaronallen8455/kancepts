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

type Category :: (k -> k -> Type) -> Constraint
class Category cat where
  src :: cat a b -> Obj cat a
  tgt :: cat a b -> Obj cat b
  (.) :: cat b c -> cat a b -> cat a c

type Obj cat a = cat a a

-- Category with a single object
data One a b where
  One :: One () ()

instance Category One where
  src One = One
  tgt One = One
  One . One = One

-- Discrete category of two objects
data ElemA = ElemA
data ElemB = ElemB
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

--------------------------------------------------------------------------------
-- Functor
--------------------------------------------------------------------------------

class (Category (Dom ftag), Category (Cod ftag)) => Functor ftag where
  type Dom ftag :: Type -> Type -> Type
  type Cod ftag :: Type -> Type -> Type

  type (:%) ftag a :: Type

  (%) :: ftag -> Dom ftag a b -> Cod ftag (ftag :% a) (ftag :% b)

data g :.% f =
  Comp g f

instance (Functor f, Functor g, Cod f ~ Dom g) => Functor (g :.% f) where
  type Dom (g :.% f) = Dom f
  type Cod (g :.% f) = Cod g

  type (g :.% f) :% a = g :% (f :% a)

  Comp g f % m = g % (f % m)

data Identity (c :: Type -> Type -> Type) = Identity

instance Category c => Functor (Identity c) where
  type Dom (Identity c) = c
  type Cod (Identity c) = c

  type Identity c :% a = a

  Identity % m = m

--------------------------------------------------------------------------------
-- Natural Transformation
--------------------------------------------------------------------------------

type Nat :: (Type -> Type -> Type) -- Codomain category
         -> (Type -> Type -> Type) -- Domain category
         -> Type -> Type -> Type
data Nat c d g f where
  Nat :: (Functor f, Functor g, c ~ Cod f, c ~ Cod g, d ~ Dom f, d ~ Dom g)
      => g -> f -> (forall z. Obj d z -> c (f :% z) (g :% z)) -> Nat c d g f

type f ~> g = (Cod f ~ Cod g, Dom f ~ Dom g) => Nat (Cod f) (Dom f) g f

vertComp :: Nat c d h g -> Nat c d g f -> Nat c d h f
vertComp (Nat h _ n1) (Nat _ f n2) = Nat h f $ \o -> n1 o . n2 o

instance Category (Nat c d) where
  src (Nat _ d _) = Nat d d _
  tgt _ = undefined -- Nat Identity Identity _
  (.) = undefined

whiskerLeft :: (Functor h, Dom h ~ e, Cod h ~ d)
            => Nat c d g f -> h -> Nat c e (g :.% h) (f :.% h)
whiskerLeft (Nat g f c) h = Nat (Comp g h) (Comp f h) $ \o -> c $ h % o

whiskerRight :: (Functor h, Cod h ~ e, Dom h ~ c)
             => Nat c d g f -> h -> Nat e d (h :.% g) (h :.% f)
whiskerRight (Nat g f c) h = Nat (Comp h g) (Comp h f) $ \o -> h % c o

horizComp :: Nat e c i h -> Nat c d g f -> Nat e d (i :.% g) (h :.% f)
horizComp n1@(Nat _ h _) n2@(Nat g _ _) =
  vertComp (whiskerLeft n1 g) (whiskerRight n2 h)

--------------------------------------------------------------------------------
-- Kan Extensions
--------------------------------------------------------------------------------

-- Universal property of left kan extension
newtype LanUP f k lan =
  LanUP (forall g. Functor g
      => f ~> (g :.% k)
      -> lan ~> g
        )

data LeftKanExt k f lan where
  Lan :: lan
      -> Nat (Cod f) (Dom f) (lan :.% k) f -- f ~> (lan :.% k)
      -> LanUP f k lan
      -> LeftKanExt k f lan

-- Universal property of right kan extension
newtype RanUP f k ran =
  RanUP (forall g. Functor g
      => (g :.% k) ~> f
      -> g ~> ran
        )

data RightKanExt k f ran where
  Ran :: ran
      -> Nat (Cod f) (Dom f) f (ran :.% k)
      -> RanUP f k ran
      -> RightKanExt k f ran

--------------------------------------------------------------------------------
-- (Co)limits
--------------------------------------------------------------------------------

-- The left kan extension of a functor F : C -> D along the unique functor
-- ! : C -> 1 is the colimit of F in D, each existing if only the other does.

type ConstOne :: (Type -> Type -> Type) -> Type
data ConstOne c = ConstOne

instance Category c => Functor (ConstOne c) where
  type Dom (ConstOne c) = c
  type Cod (ConstOne c) = One
  type ConstOne c :% a = ()
  ConstOne % _ = One

colimit :: colimit
        -> Nat (Cod f) (Dom f) (colimit :.% ConstOne (Dom f)) f
        -> LanUP f (ConstOne (Dom f)) colimit
        -> LeftKanExt (ConstOne (Dom f)) f colimit
colimit = Lan

-- The colimit of 2 in Set is a coproduct, Either in Hask

data TwoToHask = TwoToHask

instance Functor TwoToHask where
  type Dom TwoToHask = Two
  type Cod TwoToHask = (->)
  type TwoToHask :% a = a
  TwoToHask % A = id
  TwoToHask % B = id

-- A constant functor from 1 to Hask selecting the coproduct of the elements of 2
data Coproduct = Coproduct

instance Functor Coproduct where
  type Dom Coproduct = One
  type Cod Coproduct = (->)
  type Coproduct :% a = Either ElemA ElemB
  Coproduct % One = id

coproduct :: LeftKanExt (ConstOne Two) TwoToHask Coproduct
coproduct = colimit Coproduct eta sigma
  where
    eta :: Nat (->) Two (Coproduct :.% ConstOne Two) TwoToHask
    eta = Nat (Comp Coproduct ConstOne) TwoToHask $ \case
      A -> const $ Left ElemA
      B -> const $ Right ElemB

    sigma :: LanUP TwoToHask (ConstOne Two) Coproduct
    sigma = LanUP $ \case
      Nat (Comp g ConstOne) TwoToHask c -> Nat g Coproduct $ \case
        One -> either (c A) (c B)

-- Likewise, the right kan extension defines the limit

limit :: limit
      -> Nat (Cod f) (Dom f) f (limit :.% ConstOne (Dom f))
      -> RanUP f (ConstOne (Dom f)) limit
      -> RightKanExt (ConstOne (Dom f)) f limit
limit = Ran

-- Constant functor from 1 to Hask selecting the product of the elements of 2
data Product = Product

instance Functor Product where
  type Dom Product = One
  type Cod Product = (->)
  type Product :% a = (ElemA, ElemB)
  Product % One = id

product :: RightKanExt (ConstOne Two) TwoToHask Product
product = limit Product mu delta
  where
    mu :: Nat (->) Two TwoToHask (Product :.% ConstOne Two)
    mu = Nat TwoToHask (Comp Product ConstOne) $ \two (a, b) ->
      case two of
        A -> a
        B -> b

    delta :: RanUP TwoToHask (ConstOne Two) Product
    delta = RanUP $ \case
      Nat TwoToHask (Comp g ConstOne) c -> Nat Product g $ \One z ->
        (c A z, c B z)
