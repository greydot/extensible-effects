{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeOperators #-}
-- {-# LANGUAGE Safe #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE PatternSynonyms #-}
-- | Exception-producing and exception-handling effects
module Control.Eff.Exception ( Exc (..)
                            , exc
                            , withException
                            , Fail
                            , throwError
                            , throwError_
                            , die
                            , runError
                            , runFail
                            , catchError
                            , onFail
                            , rethrowError
                            , liftEither
                            , liftEitherM
                            , liftMaybe
                            , liftMaybeM
                            , ignoreFail
                            , Result
                            , pattern Error
                            , pattern Result
                            ) where

import Control.Eff
import Control.Eff.Extend

import Control.Monad (void)
import Control.Monad.Base
import Control.Monad.Trans.Control

import Data.Function (fix)
import Data.Proxy

import GHC.TypeNats
import Haskus.Utils.Variant.VEither (V, VEither, pattern VLeft, pattern VRight)

import Unsafe.Coerce (unsafeCoerce)

-- ------------------------------------------------------------------------
-- | Exceptions
--
-- exceptions of the type e; no resumption
newtype Exc e v = Exc e

-- | Embed a pure value
withException :: Monad m => a -> m (Either e a)
withException = return . Right
-- | Throw an error
exc :: Monad m => e -> m (Either e a)
exc = return . Left
-- | Given a callback, and an 'Exc' request, respond to it.
instance Monad m => Handle (Exc e) r a (m (Either e a)) where
  handle _ _ (Exc e) = exc e

instance ( MonadBase m m
         , LiftedBase m r
         ) => MonadBaseControl m (Eff (Exc e ': r)) where
    type StM (Eff (Exc e ': r)) a = StM (Eff r) (Either e a)
    liftBaseWith f = raise $ liftBaseWith $ \runInBase ->
                       f (runInBase . runError)
    restoreM x = do r :: Either e a <- raise (restoreM x)
                    liftEither r

type Fail = Exc ()

-- | Throw an exception in an effectful computation. The type is inferred.
throwError :: (Member (Exc e) r) => e -> Eff r a
throwError e = send (Exc e)
{-# INLINE throwError #-}

-- | Throw an exception in an effectful computation. The type is unit,
--   which suppresses the ghc-mod warning "A do-notation statement
--   discarded a result of type"
throwError_ :: (Member (Exc e) r) => e -> Eff r ()
throwError_ = throwError
{-# INLINE throwError_ #-}

-- | Makes an effect fail, preventing future effects from happening.
die :: Member Fail r => Eff r a
die = throwError ()
{-# INLINE die #-}

-- | Run a computation that might produce an exception.
runError :: Eff (Exc e ': r) a -> Eff r (Either e a)
runError = fix (handle_relay withException)

-- | Runs a failable effect, such that failed computation return 'Nothing', and
--   'Just' the return value on success.
runFail :: Eff (Fail ': r) a -> Eff r (Maybe a)
runFail = fmap (either (const Nothing) Just) . runError
{-# INLINE runFail #-}

-- | Run a computation that might produce exceptions, and give it a way to deal
-- with the exceptions that come up. The handler is allowed to rethrow the
-- exception
catchError :: Member (Exc e) r =>
        Eff r a -> (e -> Eff r a) -> Eff r a
catchError m h = fix (respond_relay' (\_ _ (Exc e) -> h e) return) m

-- | Add a default value (i.e. failure handler) to a fallible computation.
-- This hides the fact that a failure happened.
onFail :: Eff (Fail ': r) a -- ^ The fallible computation.
       -> Eff r a           -- ^ The computation to run on failure.
       -> Eff r a
onFail e handle_ = runFail e >>= maybe handle_ return
{-# INLINE onFail #-}

-- | Run a computation until it produces an exception,
-- and convert and throw that exception in a new context.
rethrowError :: (Member (Exc e') r)
           => (e -> e')
           -> Eff (Exc e ': r) a
           -> Eff r a
rethrowError t e = runError e >>= either (throwError . t) return

-- | Treat Lefts as exceptions and Rights as return values.
liftEither :: (Member (Exc e) r) => Either e a -> Eff r a
liftEither = either throwError return
{-# INLINE liftEither #-}

-- | `liftEither` in a lifted Monad
liftEitherM :: (Member (Exc e) r, Lifted m r)
            => m (Either e a)
            -> Eff r a
liftEitherM m = lift m >>= liftEither
{-# INLINE liftEitherM #-}

-- | Lift a maybe into the 'Fail' effect, causing failure if it's 'Nothing'.
liftMaybe :: Member Fail r => Maybe a -> Eff r a
liftMaybe = maybe die return
{-# INLINE liftMaybe #-}

-- | `liftMaybe` in a lifted Monad
liftMaybeM :: (Member Fail r, Lifted m r)
           => m (Maybe a)
           -> Eff r a
liftMaybeM m = lift m >>= liftMaybe
{-# INLINE liftMaybeM #-}

-- | Ignores a failure event. Since the event can fail, you cannot inspect its
--   return type, because it has none on failure. To inspect it, use 'runFail'.
ignoreFail :: Eff (Fail ': r) a
           -> Eff r ()
ignoreFail e = void e `onFail` return ()
{-# INLINE ignoreFail #-}

-- | Result is similar to 'Either' but with a polymorphic variant type on the left.
-- FIXME: Consider rewriting this instead of using haskus packages to avoid dependency bloat.
type Result errs a = VEither errs a

pattern Error :: forall (errs :: [*]) a. V errs -> Result errs a
pattern Error e <- VLeft e

pattern Result :: forall (errs :: [*]) a. a -> Result errs a
pattern Result a <- VRight a

type family Exceptions xs where
  Exceptions '[] = '[]
  Exceptions (Exc e ': xs) = (e ': Exceptions xs)

type family NonExceptions xs where
  NonExceptions '[] = '[]
  NonExceptions (Exc e ': xs) = NonExceptions xs
  NonExceptions (x ': xs) = (x ': NonExceptions xs)

type family Length xs :: Nat where
  Length '[] = 0
  Length (x ': xs) = 1 + Length xs

type family (++) xs ys where
  (++) '[] ys = ys
  (++) (x ': xs) ys = x ': (xs ++ ys)

type family Reverse xs where
  Reverse '[] = '[]
  Reverse (x ': xs) = Reverse xs ++ '[x]

type family ConstructEithers es a where
  ConstructEithers '[] a = a
  ConstructEithers (e ': es) a = Either e (ConstructEithers es a)

type family ConstructResult es where
  ConstructResult (Either e (Either e' a)) = a
  -- FIXME: Add inner loop

runErrors :: forall rest numErrs errs r a.
           ( rest ~ NonExceptions r
           , errs ~ Exceptions r
           , numErrs ~ Length errs
           , KnownNat numErrs
           ) => Eff r a -> Eff rest (Result errs a)
runErrors = undefined
  where chain :: Eff r a -> Eff rest (ConstructEithers (Reverse errs) a)
        chain = foldr (.) id (replicate n runError)
        n = fromIntegral $ natVal (Proxy :: Proxy numErrs)
