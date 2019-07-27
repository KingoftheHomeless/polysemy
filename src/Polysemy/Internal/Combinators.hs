{-# LANGUAGE AllowAmbiguousTypes   #-}
{-# LANGUAGE RecursiveDo   #-}
{-# LANGUAGE BangPatterns   #-}

{-# OPTIONS_HADDOCK not-home #-}

module Polysemy.Internal.Combinators
  ( -- * First order
    interpret
  , intercept
  , reinterpret
  , reinterpret2
  , reinterpret3

    -- * Higher order
  , interpretH
  , interceptH
  , reinterpretH
  , reinterpret2H
  , reinterpret3H

    -- * Statefulness
  , stateful
  , lazilyStateful
  , backwardsStateful
  , lazilyBackwardsStateful
  ) where

import           Control.Monad
import           Control.Monad.Fix
import qualified Control.Monad.Trans.State.Lazy as LS
import qualified Control.Monad.Trans.State.Strict as S
import           Polysemy.Internal.Fixpoint
import           Polysemy.Internal
import           Polysemy.Internal.CustomErrors
import           Polysemy.Internal.Tactics
import           Polysemy.Internal.Union


------------------------------------------------------------------------------
-- | A lazier version of 'Data.Tuple.swap'.
swap :: (a, b) -> (b, a)
swap ~(a, b) = (b, a)


firstOrder
    :: ((forall m x. e m x -> Tactical e m r x) -> t)
    -> (forall m x. e m x -> Sem r x)
    -> t
firstOrder higher f = higher $ \(e :: e m x) -> liftT @m $ f e
{-# INLINE firstOrder #-}


------------------------------------------------------------------------------
-- | The simplest way to produce an effect handler. Interprets an effect @e@ by
-- transforming it into other effects inside of @r@.
interpret
    :: FirstOrder e "interpret"
    => (∀ x m. e m x -> Sem r x)
       -- ^ A natural transformation from the handled effect to other effects
       -- already in 'Sem'.
    -> Sem (e ': r) a
    -> Sem r a
-- TODO(sandy): could probably give a `coerce` impl for `runTactics` here
interpret = firstOrder interpretH
{-# INLINE interpret #-}


------------------------------------------------------------------------------
-- | Like 'interpret', but for higher-order effects (ie. those which make use of
-- the @m@ parameter.)
--
-- See the notes on 'Tactical' for how to use this function.
interpretH
    :: (∀ x m . e m x -> Tactical e m r x)
       -- ^ A natural transformation from the handled effect to other effects
       -- already in 'Sem'.
    -> Sem (e ': r) a
    -> Sem r a
interpretH f (Sem m) = m $ \u ->
  case decomp u of
    Left  x -> liftSem $ hoist (interpretH f) x
    Right (Weaving e s d y v) -> do
      a <- runTactics s d v $ f e
      pure $ y a
{-# INLINE interpretH #-}


------------------------------------------------------------------------------
-- | A highly-performant combinator for interpreting an effect statefully. See
-- 'stateful' for a more user-friendly variety of this function.
interpretInStateT
    :: (∀ x m. e m x -> S.StateT s (Sem r) x)
    -> s
    -> Sem (e ': r) a
    -> Sem r (s, a)
interpretInStateT f s (Sem m) = Sem $ \k ->
  fmap swap $ flip S.runStateT s $ m $ \u ->
    case decomp u of
        Left x -> S.StateT $ \s' ->
          k . fmap swap
            . weave (s', ())
                    (uncurry $ interpretInStateT f)
                    (Just . snd)
            $ x
        Right (Weaving e z _ y _) ->
          fmap (y . (<$ z)) $ S.mapStateT (usingSem k) $ f e
{-# INLINE interpretInStateT #-}

newtype RevStateT s m a = RevStateT { runRevStateT :: s -> m (s, a) }
  deriving (Functor)

instance MonadFix m => Applicative (RevStateT s m) where
  pure a = RevStateT $ \s -> pure (s, a)
  (<*>) = ap

instance MonadFix m => Monad (RevStateT s m) where
  m >>= f = RevStateT $ \s -> do
    rec
      (s'', a) <- runRevStateT m s'
      (s', b)  <- runRevStateT (f a) s
    return (s'', b)


newtype LazyRevStateT s m a = LazyRevStateT { runLazyRevStateT :: s -> m (s, a) }
  deriving (Functor)

instance MonadFix m => Applicative (LazyRevStateT s m) where
  pure a = LazyRevStateT $ \s -> pure (s, a)
  (<*>) = ap

instance MonadFix m => Monad (LazyRevStateT s m) where
  m >>= f = LazyRevStateT $ \s -> do
    rec
      ~(s'', a) <- runLazyRevStateT m s'
      ~(s', b)  <- runLazyRevStateT (f a) s
    return (s'', b)

interpretInRevStateT
    :: Member Fixpoint r
    => (∀ x m. e m x -> RevStateT s (Sem r) x)
    -> s
    -> Sem (e ': r) a
    -> Sem r (s, a)
interpretInRevStateT f s (Sem sem) = (`runRevStateT` s) $
  sem $ \u -> case decomp u of
  Left x -> RevStateT $ \s' ->
      liftSem $
        weave
        (s', ())
        (uncurry $ interpretInRevStateT f)
        (Just . snd)
        x
  Right (Weaving e z _ y _) ->
    y . (<$ z) <$> f e
{-# INLINE interpretInRevStateT #-}


interpretInLazyRevStateT
    :: Member Fixpoint r
    => (∀ x m. e m x -> LazyRevStateT s (Sem r) x)
    -> s
    -> Sem (e ': r) a
    -> Sem r (s, a)
interpretInLazyRevStateT f s (Sem sem) = (`runLazyRevStateT` s) $
  sem $ \u -> case decomp u of
  Left x -> LazyRevStateT $ \s' ->
      liftSem $
        weave
        (s', ())
        (uncurry $ interpretInLazyRevStateT f)
        (Just . snd)
        x
  Right (Weaving e z _ y _) ->
    y . (<$ z) <$> f e
{-# INLINE interpretInLazyRevStateT #-}

------------------------------------------------------------------------------
-- | A highly-performant combinator for interpreting an effect statefully. See
-- 'stateful' for a more user-friendly variety of this function.
interpretInLazyStateT
    :: (∀ x m. e m x -> LS.StateT s (Sem r) x)
    -> s
    -> Sem (e ': r) a
    -> Sem r (s, a)
interpretInLazyStateT f s (Sem m) = Sem $ \k ->
  fmap swap $ flip LS.runStateT s $ m $ \u ->
    case decomp u of
        Left x -> LS.StateT $ \s' ->
          k . fmap swap
            . weave (s', ())
                    (uncurry $ interpretInLazyStateT f)
                    (Just . snd)
            $ x
        Right (Weaving e z _ y _) ->
          fmap (y . (<$ z)) $ LS.mapStateT (usingSem k) $ f e
{-# INLINE interpretInLazyStateT #-}


------------------------------------------------------------------------------
-- | Like 'interpret', but with access to an intermediate state @s@.
stateful
    :: (∀ x m. e m x -> s -> Sem r (s, x))
    -> s
    -> Sem (e ': r) a
    -> Sem r (s, a)
stateful f = interpretInStateT $ \e -> S.StateT $ \s -> do
  (!s', a) <- f e s
  return (a, s')
{-# INLINE[3] stateful #-}

------------------------------------------------------------------------------
-- | Like 'interpret', but with access to an intermediate state @s@.
lazilyStateful
    :: (∀ x m. e m x -> s -> Sem r (s, x))
    -> s
    -> Sem (e ': r) a
    -> Sem r (s, a)
lazilyStateful f = interpretInLazyStateT $ \e -> LS.StateT $ fmap swap . f e
{-# INLINE[3] lazilyStateful #-}


------------------------------------------------------------------------------
-- | Like 'interpret', but with access to an intermediate state @s@ which
-- is processed /backwards/, from last action to first.
backwardsStateful
    :: Member Fixpoint r
    => (∀ x m. e m x -> s -> Sem r (s, x))
    -> s
    -> Sem (e ': r) a
    -> Sem r (s, a)
backwardsStateful f = interpretInRevStateT $ \s -> RevStateT (f s)
{-# INLINE[3] backwardsStateful #-}

------------------------------------------------------------------------------
-- | Like 'interpret', but with access to an intermediate state @s@ which
-- is processed /backwards/, from last action to first.
lazilyBackwardsStateful
    :: Member Fixpoint r
    => (∀ x m. e m x -> s -> Sem r (s, x))
    -> s
    -> Sem (e ': r) a
    -> Sem r (s, a)
lazilyBackwardsStateful f = interpretInLazyRevStateT $ \s -> LazyRevStateT (f s)
{-# INLINE[3] lazilyBackwardsStateful #-}



------------------------------------------------------------------------------
-- | Like 'reinterpret', but for higher-order effects.
--
-- See the notes on 'Tactical' for how to use this function.
reinterpretH
    :: forall e1 e2 r a
     . (∀ m x. e1 m x -> Tactical e1 m (e2 ': r) x)
       -- ^ A natural transformation from the handled effect to the new effect.
    -> Sem (e1 ': r) a
    -> Sem (e2 ': r) a
reinterpretH f (Sem m) = Sem $ \k -> m $ \u ->
  case decompCoerce u of
    Left x  -> k $ hoist (reinterpretH f) $ x
    Right (Weaving e s d y v) -> do
      a <- usingSem k $ runTactics s (raiseUnder . d) v $ f e
      pure $ y a
{-# INLINE[3] reinterpretH #-}
-- TODO(sandy): Make this fuse in with 'stateful' directly.


------------------------------------------------------------------------------
-- | Like 'interpret', but instead of removing the effect @e@, reencodes it in
-- some new effect @f@. This function will fuse when followed by
-- 'Polysemy.State.runState', meaning it's free to 'reinterpret' in terms of
-- the 'Polysemy.State.State' effect and immediately run it.
reinterpret
    :: forall e1 e2 r a
     . FirstOrder e1 "reinterpret"
    => (∀ m x. e1 m x -> Sem (e2 ': r) x)
       -- ^ A natural transformation from the handled effect to the new effect.
    -> Sem (e1 ': r) a
    -> Sem (e2 ': r) a
reinterpret = firstOrder reinterpretH
{-# INLINE[3] reinterpret #-}
-- TODO(sandy): Make this fuse in with 'stateful' directly.


------------------------------------------------------------------------------
-- | Like 'reinterpret2', but for higher-order effects.
--
-- See the notes on 'Tactical' for how to use this function.
reinterpret2H
    :: forall e1 e2 e3 r a
     . (∀ m x. e1 m x -> Tactical e1 m (e2 ': e3 ': r) x)
       -- ^ A natural transformation from the handled effect to the new effects.
    -> Sem (e1 ': r) a
    -> Sem (e2 ': e3 ': r) a
reinterpret2H f (Sem m) = Sem $ \k -> m $ \u ->
  case decompCoerce u of
    Left x  -> k $ weaken $ hoist (reinterpret2H f) $ x
    Right (Weaving e s d y v) -> do
      a <- usingSem k $ runTactics s (raiseUnder2 . d) v $ f e
      pure $ y a
{-# INLINE[3] reinterpret2H #-}


------------------------------------------------------------------------------
-- | Like 'reinterpret', but introduces /two/ intermediary effects.
reinterpret2
    :: forall e1 e2 e3 r a
     . FirstOrder e1 "reinterpret2"
    => (∀ m x. e1 m x -> Sem (e2 ': e3 ': r) x)
       -- ^ A natural transformation from the handled effect to the new effects.
    -> Sem (e1 ': r) a
    -> Sem (e2 ': e3 ': r) a
reinterpret2 = firstOrder reinterpret2H
{-# INLINE[3] reinterpret2 #-}


------------------------------------------------------------------------------
-- | Like 'reinterpret3', but for higher-order effects.
--
-- See the notes on 'Tactical' for how to use this function.
reinterpret3H
    :: forall e1 e2 e3 e4 r a
     . (∀ m x. e1 m x -> Tactical e1 m (e2 ': e3 ': e4 ': r) x)
       -- ^ A natural transformation from the handled effect to the new effects.
    -> Sem (e1 ': r) a
    -> Sem (e2 ': e3 ': e4 ': r) a
reinterpret3H f (Sem m) = Sem $ \k -> m $ \u ->
  case decompCoerce u of
    Left x  -> k . weaken . weaken . hoist (reinterpret3H f) $ x
    Right (Weaving e s d y v) -> do
      a <- usingSem k $ runTactics s (raiseUnder3 . d) v $ f e
      pure $ y a
{-# INLINE[3] reinterpret3H #-}


------------------------------------------------------------------------------
-- | Like 'reinterpret', but introduces /three/ intermediary effects.
reinterpret3
    :: forall e1 e2 e3 e4 r a
     . FirstOrder e1 "reinterpret3"
    => (∀ m x. e1 m x -> Sem (e2 ': e3 ': e4 ': r) x)
       -- ^ A natural transformation from the handled effect to the new effects.
    -> Sem (e1 ': r) a
    -> Sem (e2 ': e3 ': e4 ': r) a
reinterpret3 = firstOrder reinterpret3H
{-# INLINE[3] reinterpret3 #-}


------------------------------------------------------------------------------
-- | Like 'interpret', but instead of handling the effect, allows responding to
-- the effect while leaving it unhandled. This allows you, for example, to
-- intercept other effects and insert logic around them.
intercept
    :: ( Member e r
       , FirstOrder e "intercept"
       )
    => (∀ x m. e m x -> Sem r x)
       -- ^ A natural transformation from the handled effect to other effects
       -- already in 'Sem'.
    -> Sem r a
       -- ^ Unlike 'interpret', 'intercept' does not consume any effects.
    -> Sem r a
intercept f = interceptH $ \(e :: e m x) -> liftT @m $ f e
{-# INLINE intercept #-}


------------------------------------------------------------------------------
-- | Like 'interceptH', but for higher-order effects.
--
-- See the notes on 'Tactical' for how to use this function.
interceptH
    :: Member e r
    => (∀ x m. e m x -> Tactical e m r x)
       -- ^ A natural transformation from the handled effect to other effects
       -- already in 'Sem'.
    -> Sem r a
       -- ^ Unlike 'interpretH', 'interceptH' does not consume any effects.
    -> Sem r a
interceptH f (Sem m) = Sem $ \k -> m $ \u ->
  case prj u of
    Just (Weaving e s d y v) ->
      usingSem k $ fmap y $ runTactics s (raise . d) v $ f e
    Nothing -> k $ hoist (interceptH f) u
{-# INLINE interceptH #-}
