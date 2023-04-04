{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}

module Vector (
  Vec (Nil),
  pattern (:|>),
  pattern (:<|),
  generate,
  reverse,
  zipWithSame,
  fromList,
  proofSuccDistributes,
)
where

import Prelude hiding (reverse)

import Data.Foldable
import Data.Type.Equality
import Data.Type.Nat

proofSuccDistributes :: forall n m. SNat n -> SNat m -> (Plus n ('S m) :~: 'S (Plus n m))
proofSuccDistributes SZ _ = Refl
proofSuccDistributes (SS @k) m = gcastWith (proofSuccDistributes (snat @k) m) Refl

-- Vectors
data Vec (n :: Nat) a where
  Nil :: Vec 'Z a
  Cons :: forall m a. a -> Vec m a -> Vec ('S m) a

infixl 4 :|>
pattern (:|>) :: Vec n a -> a -> Vec ('S n) a
pattern as :|> a = Cons a as

infixr 4 :<|
pattern (:<|) :: a -> Vec n a -> Vec ('S n) a
pattern a :<| as = Cons a as

{-# COMPLETE Nil, (:|>) #-}
{-# COMPLETE Nil, (:<|) #-}

instance (SNatI n, Show a) => Show (Vec n a) where
  show = show . toList

newtype FoldInduction a b (n :: Nat) = FoldInduction {runFold :: (a -> b -> b) -> b -> Vec n a -> b}

instance SNatI n => Foldable (Vec n) where
  foldr :: forall a b. (a -> b -> b) -> b -> Vec n a -> b
  foldr = runFold (induction @n base ind)
    where
      base :: FoldInduction a b 'Z
      base = FoldInduction (\_ e Nil -> e)

      ind :: forall m. FoldInduction a b m -> FoldInduction a b ('S m)
      ind (FoldInduction recurse) = FoldInduction (\f e (Cons a as) -> f a (recurse f e as))

generate :: forall n a. SNatI n => (Nat -> a) -> Vec n a
generate f = induction1 base ind
  where
    base :: Vec 'Z a
    base = Nil

    ind :: forall k. SNatI k => Vec k a -> Vec ('S k) a
    ind = Cons (f (snatToNat (snat @k)))

sNatSucc :: SNat n -> SNat ('S n)
sNatSucc SZ = SS
sNatSucc SS = SS

reverse :: forall n a. SNatI n => Vec n a -> Vec n a
reverse = case proofPlusNZero @n of
  Refl -> reverse' SZ (snat @n) Nil
  where
    reverse' :: forall m k. SNat m -> SNat k -> Vec m a -> Vec k a -> Vec (Plus k m) a
    reverse' _ SZ v Nil = v
    reverse' vm SS v (Cons @l a as) =
      case proofSuccDistributes (snat @l) vm of
        Refl -> reverse' (sNatSucc vm) (snat @l) (Cons a v) as

zipWithSame :: (a -> b -> c) -> Vec n a -> Vec n b -> Vec n c
zipWithSame _ Nil Nil = Nil
zipWithSame f (Cons a as) (Cons b bs) = Cons (f a b) (zipWithSame f as bs)

newtype FromListInduction a (n :: Nat) = FromListInduction {runFromList :: [a] -> Maybe (Vec n a)}

fromList :: forall n a. SNatI n => [a] -> Maybe (Vec n a)
fromList = runFromList (induction @n base ind)
  where
    base :: FromListInduction a 'Z
    base = FromListInduction (\_ -> Just Nil)

    ind :: forall m. FromListInduction a m -> FromListInduction a ('S m)
    ind (FromListInduction recurse) = FromListInduction rec'
      where
        rec' :: [a] -> Maybe (Vec ('S m) a)
        rec' [] = Nothing
        rec' (a : as) = Cons a <$> recurse as
