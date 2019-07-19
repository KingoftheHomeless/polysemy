{-# LANGUAGE AllowAmbiguousTypes  #-}
{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE MonoLocalBinds       #-}
{-# LANGUAGE UndecidableInstances #-}

{-# OPTIONS_GHC -fno-warn-orphans #-}
{-# OPTIONS_HADDOCK not-home #-}

module Polysemy.Internal
  ( Sem (..)
  , Member
  , Members
  , send
  , embed
  , run
  , runM
  , raise
  , raiseUnder
  , raiseUnder2
  , raiseUnder3
  , Embed (..)
  , usingSem
  , liftSem
  , hoistSem
  , (.@)
  , (.@@)
  ) where

import Control.Applicative
import Control.Monad
import Control.Monad.Fail
import Control.Monad.Fix
import Control.Monad.IO.Class
import Data.Functor.Identity
import Data.Kind
import Polysemy.Internal.Fixpoint
import Polysemy.Embed.Type
import Polysemy.Internal.NonDet
import Polysemy.Internal.Union



------------------------------------------------------------------------------
-- | Like 'runSem' but flipped for better ergonomics sometimes.
usingSem
    :: Monad m
    => (∀ x. Union r (Sem r) x -> m x)
    -> Sem r a
    -> m a
usingSem k m = runSem m k
{-# INLINE usingSem #-}




instance (Member NonDet r) => Alternative (Sem r) where
  empty = send Empty
  {-# INLINE empty #-}
  a <|> b = send (Choose a b)
  {-# INLINE (<|>) #-}

-- | @since 0.2.1.0
instance (Member NonDet r) => MonadPlus (Sem r) where
  mzero = empty
  mplus = (<|>)

-- | @since 0.2.1.0
instance (Member NonDet r) => MonadFail (Sem r) where
  fail = const empty


------------------------------------------------------------------------------
-- | This instance will only lift 'IO' actions. If you want to lift into some
-- other 'MonadIO' type, use this instance, and handle it via the
-- 'Polysemy.IO.runIO' interpretation.
instance (Member (Embed IO) r) => MonadIO (Sem r) where
  liftIO = embed
  {-# INLINE liftIO #-}

instance Member Fixpoint r => MonadFix (Sem r) where
  mfix f = send $ Fixpoint f
  {-# INLINE mfix #-}


liftSem :: Union r (Sem r) a -> Sem r a
liftSem u = Sem $ \k -> k u
{-# INLINE liftSem #-}


hoistSem
    :: (∀ x. Union r (Sem r) x -> Union r' (Sem r') x)
    -> Sem r a
    -> Sem r' a
hoistSem nat (Sem m) = Sem $ \k -> m $ \u -> k $ nat u
{-# INLINE hoistSem #-}

------------------------------------------------------------------------------
-- | Introduce an effect into 'Sem'. Analogous to
-- 'Control.Monad.Class.Trans.lift' in the mtl ecosystem
raise :: ∀ e r a. Sem r a -> Sem (e ': r) a
raise = hoistSem $ hoist raise . weaken
{-# INLINE raise #-}


------------------------------------------------------------------------------
-- | Like 'raise', but introduces a new effect underneath the head of the
-- list.
raiseUnder :: ∀ e2 e1 r a. Sem (e1 ': r) a -> Sem (e1 ': e2 ': r) a
raiseUnder = hoistSem $ hoist raiseUnder . weakenUnder
  where
    weakenUnder :: ∀ m x. Union (e1 ': r) m x -> Union (e1 ': e2 ': r) m x
    weakenUnder (Union SZ a) = Union SZ a
    weakenUnder (Union (SS n) a) = Union (SS (SS n)) a
    {-# INLINE weakenUnder #-}
{-# INLINE raiseUnder #-}


------------------------------------------------------------------------------
-- | Like 'raise', but introduces two new effects underneath the head of the
-- list.
raiseUnder2 :: ∀ e2 e3 e1 r a. Sem (e1 ': r) a -> Sem (e1 ': e2 ': e3 ': r) a
raiseUnder2 = hoistSem $ hoist raiseUnder2 . weakenUnder2
  where
    weakenUnder2 ::  ∀ m x. Union (e1 ': r) m x -> Union (e1 ': e2 ': e3 ': r) m x
    weakenUnder2 (Union SZ a) = Union SZ a
    weakenUnder2 (Union (SS n) a) = Union (SS (SS (SS n))) a
    {-# INLINE weakenUnder2 #-}
{-# INLINE raiseUnder2 #-}


------------------------------------------------------------------------------
-- | Like 'raise', but introduces two new effects underneath the head of the
-- list.
raiseUnder3 :: ∀ e2 e3 e4 e1 r a. Sem (e1 ': r) a -> Sem (e1 ': e2 ': e3 ': e4 ': r) a
raiseUnder3 = hoistSem $ hoist raiseUnder3 . weakenUnder3
  where
    weakenUnder3 ::  ∀ m x. Union (e1 ': r) m x -> Union (e1 ': e2 ': e3 ': e4 ': r) m x
    weakenUnder3 (Union SZ a) = Union SZ a
    weakenUnder3 (Union (SS n) a) = Union (SS (SS (SS (SS n)))) a
    {-# INLINE weakenUnder3 #-}
{-# INLINE raiseUnder3 #-}


------------------------------------------------------------------------------
-- | Embed an effect into a 'Sem'. This is used primarily via
-- 'Polysemy.makeSem' to implement smart constructors.
send :: Member e r => e (Sem r) a -> Sem r a
send = liftSem . inj
{-# INLINE[3] send #-}


------------------------------------------------------------------------------
-- | Embed a monadic action @m@ in 'Sem'.
--
-- TODO(sandy): @since
embed :: Member (Embed m) r => m a -> Sem r a
embed = send . Embed
{-# INLINE embed #-}


------------------------------------------------------------------------------
-- | Run a 'Sem' containing no effects as a pure value.
run :: Sem '[] a -> a
run (Sem m) = runIdentity $ m absurdU
{-# INLINE run #-}


------------------------------------------------------------------------------
-- | Lower a 'Sem' containing only a single lifted 'Monad' into that
-- monad.
runM :: Monad m => Sem '[Embed m] a -> m a
runM (Sem m) = m $ \z ->
  case extract z of
    Weaving e s _ _ f _ -> do
      a <- unEmbed e
      pure $ f $ a <$ s
{-# INLINE runM #-}


------------------------------------------------------------------------------
-- | Some interpreters need to be able to lower down to the base monad (often
-- 'IO') in order to function properly --- some good examples of this are
-- 'Polysemy.Error.lowerError' and 'Polysemy.Resource.lowerResource'.
--
-- However, these interpreters don't compose particularly nicely; for example,
-- to run 'Polysemy.Resource.lowerResource', you must write:
--
-- @
-- runM . lowerError runM
-- @
--
-- Notice that 'runM' is duplicated in two places here. The situation gets
-- exponentially worse the more intepreters you have that need to run in this
-- pattern.
--
-- Instead, '.@' performs the composition we'd like. The above can be written as
--
-- @
-- (runM .@ lowerError)
-- @
--
-- The parentheses here are important; without them you'll run into operator
-- precedence errors.
--
-- __Warning:__ This combinator will __duplicate work__ that is intended to be
-- just for initialization. This can result in rather surprising behavior. For
-- a version of '.@' that won't duplicate work, see the @.\@!@ operator in
-- <http://hackage.haskell.org/package/polysemy-zoo/docs/Polysemy-IdempotentLowering.html polysemy-zoo>.
(.@)
    :: Monad m
    => (∀ x. Sem r x -> m x)
       -- ^ The lowering function, likely 'runM'.
    -> (∀ y. (∀ x. Sem r x -> m x)
          -> Sem (e ': r) y
          -> Sem r y)
    -> Sem (e ': r) z
    -> m z
f .@ g = f . g f
infixl 8 .@


------------------------------------------------------------------------------
-- | Like '.@', but for interpreters which change the resulting type --- eg.
-- 'Polysemy.Error.lowerError'.
(.@@)
    :: Monad m
    => (∀ x. Sem r x -> m x)
       -- ^ The lowering function, likely 'runM'.
    -> (∀ y. (∀ x. Sem r x -> m x)
          -> Sem (e ': r) y
          -> Sem r (f y))
    -> Sem (e ': r) z
    -> m (f z)
f .@@ g = f . g f
infixl 8 .@@

