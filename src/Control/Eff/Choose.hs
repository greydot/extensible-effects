{-# LANGUAGE TypeFamilies #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE Safe #-}
-- The following is needed to define MonadPlus instance. It is decidable
-- (there is no recursion!), but GHC cannot see that.
{-# LANGUAGE UndecidableInstances #-}

-- | Nondeterministic choice effect
module Control.Eff.Choose ( Choose (..)
                          , choose
                          , makeChoice
                          , mzero'
                          , mplus'
                          , module Control.Eff.Logic
                          ) where

import Control.Eff
import Control.Eff.Extend
import Control.Eff.Lift
import Control.Eff.Logic
      
import Control.Applicative
import Control.Monad
import Control.Monad.Base
import Control.Monad.Trans.Control

-- ------------------------------------------------------------------------
-- | Non-determinism (choice)
--
-- choose lst non-deterministically chooses one value from the lst
-- choose [] thus corresponds to failure
-- Unlike Reader, Choose is not a GADT because the type of values
-- returned in response to a (Choose a) request is just a, without
-- any constraints.
newtype Choose a = Choose [a]

instance ( MonadBase m m
         , SetMember Lift (Lift m) r
         , MonadBaseControl m (Eff r)
         ) => MonadBaseControl m (Eff (Choose ': r)) where
    type StM (Eff (Choose ': r)) a = StM (Eff r) [a]
    liftBaseWith f = raise $ liftBaseWith $ \runInBase ->
                       f (runInBase . makeChoice)
    restoreM x = do lst <- raise (restoreM x)
                    choose lst

-- | choose lst non-deterministically chooses one value from the lst
-- choose [] thus corresponds to failure
choose :: Member Choose r => [a] -> Eff r a
choose lst = send $ Choose lst

-- | MonadPlus-like operators are expressible via choose
mzero' :: Member Choose r => Eff r a
mzero' = choose []

-- | MonadPlus-like operators are expressible via choose
mplus' :: Member Choose r => Eff r a -> Eff r a -> Eff r a
mplus' m1 m2 = join $ choose [m1,m2]

-- | MonadPlus-like operators are expressible via choose
instance Member Choose r => Alternative (Eff r) where
  empty = mzero'
  (<|>) = mplus'

instance Member Choose r => MonadPlus (Eff r) where
  mzero = empty
  mplus = (<|>)

-- | Run a nondeterministic effect, returning all values.
makeChoice :: forall a r. Eff (Choose ': r) a -> Eff r [a]
makeChoice = handle_relay
  (return . (:[]))
  (\k (Choose lst) -> handle k lst)
  where
    handle :: (t -> Eff r [a]) -> [t] -> Eff r [a]
    handle _  [] = return []
    handle k [x] = k x
    handle k lst = fmap concat $ mapM k lst

instance Member Choose r => MSplit (Eff r) where
  msplit = interpose (\a -> return (Just (a, mzero)))
           (\k (Choose lst) -> handle k lst)
    where
      handle :: Arr r v (Maybe (a, Eff r a))
             -> [v] -> Eff r (Maybe (a, Eff r a))
      handle _ [] = return Nothing
      handle k (h:t) = k h >>= \r -> case r of
        Nothing -> handle k t
        Just (a, m) -> return (Just (a, m <|> (handle k t >>= reflect)))
