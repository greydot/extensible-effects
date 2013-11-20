{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE EmptyDataDecls #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE MultiParamTypeClasses, FlexibleInstances, FlexibleContexts #-}
{-# LANGUAGE OverlappingInstances #-}
{-# LANGUAGE UndecidableInstances #-}

-- | Original work at: http://okmij.org/ftp/Haskell/extensible/OpenUnion1.hs.
-- Open unions (type-indexed co-products) for extensible effects.
-- This implementation relies on _closed_ overlapping instances
-- (or closed type function overlapping soon to be added to GHC).

module Data.OpenUnion1( Union
                      , inj
                      , prj
                      , prjForce
                      , decomp
                      , Member
                      , (:>)
                      , (<?>)
                      , unsafeReUnion
                      ) where

import Control.Applicative ((<$>))
import Data.Typeable

infixl 4 <?>

-- | infix form of `fromMaybe`.
(<?>) :: Maybe a -> a -> a
Just a <?> _ = a
_ <?> a = a

-- for the sake of gcast1
newtype Id a = Id { runId :: a }

-- | Where `r` is `t1 :> t2 ... :> tn`, `Union r v` can be constructed with a
-- value of type `ti v`.
-- Ideally, we should be be able to add the constraint `Member t r`.
data Union r v = forall t. (Functor t, Typeable1 t) => Union (t v)

instance Functor (Union r) where
    {-# INLINE fmap #-}
    fmap f (Union v) = Union (fmap f v)

-- | A sum data type, for `composing' effects
-- In GHC 7.4, we should make it a list
-- (:>) :: (* -> *) -> (* -> List) -> List
infixr 1 :>
data ((a :: * -> *) :> b)

class Member (t :: * -> *) r
instance Member t (t :> r)
instance Member t r => Member t (t' :> r)

{-# INLINE inj #-}
-- | Construct a Union.
inj :: (Functor t, Typeable1 t, Member t r) => t v -> Union r v
inj = Union

{-# INLINE prj #-}
-- | Try extracting the contents of a Union as a specific type.
prj :: (Typeable1 t, Member t r) => Union r v -> Maybe (t v)
prj (Union v) = runId <$> gcast1 (Id v)

{-# INLINE prjForce #-}
-- Like `prj`, but returns an error if the cast fails.
prjForce :: (Typeable1 t, Member t r) => Union r v -> (t v -> a) -> a
prjForce u f = f <$> prj u <?> error "prjForce Nothing"

{-# INLINE decomp #-}
decomp :: (Typeable1 t, Member t (t :> r)) => Union (t :> r) v -> Either (Union r v) (t v)
decomp u = Right <$> prj u <?> Left (unsafeReUnion u)

{-# INLINE unsafeReUnion #-}
-- | Juggle types for a Union. Use cautiously.
unsafeReUnion :: Union r w -> Union t w
unsafeReUnion (Union v) = Union v
