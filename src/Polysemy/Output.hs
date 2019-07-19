{-# LANGUAGE TemplateHaskell #-}

module Polysemy.Output
  ( -- * Effect
    Output (..)

    -- * Actions
  , output

    -- * Interpretations
  , runOutputList
  , runOutputMonoid
  , ignoreOutput
  , runOutputBatched
  ) where

import Data.Bifunctor (first)
import Data.Typeable
import Polysemy
import Polysemy.State
import Control.Monad (when)


------------------------------------------------------------------------------
-- | An effect capable of sending messages. Useful for streaming output and for
-- logging.
data Output o m a where
  Output :: o -> Output o m ()

makeSem ''Output


------------------------------------------------------------------------------
-- | Run an 'Output' effect by transforming it into a list of its values.
runOutputList
    :: forall o r a
     . Typeable o
    => Sem (Output o ': r) a
    -> Sem r ([o], a)
runOutputList = fmap (first reverse) . runState [] . reinterpret
  (\case
      Output o -> modify (o :)
  )
{-# INLINE runOutputList #-}

------------------------------------------------------------------------------
-- | Run an 'Output' effect by transforming it into a monoid.
runOutputMonoid
    :: forall o m r a
     . (Monoid m, Typeable m)
    => (o -> m)
    -> Sem (Output o ': r) a
    -> Sem r (m, a)
runOutputMonoid f = runState mempty . reinterpret
  (\case
      Output o -> modify (`mappend` f o)
  )
{-# INLINE runOutputMonoid #-}


------------------------------------------------------------------------------
-- | Run an 'Output' effect by ignoring it.
ignoreOutput :: Sem (Output o ': r) a -> Sem r a
ignoreOutput = interpret $ \case
  Output _ -> pure ()
{-# INLINE ignoreOutput #-}


------------------------------------------------------------------------------
-- | Accumulate 'output's so they are delayed until they reach at least size
-- @size@.
--
-- If @size@ is 0, this interpretation will not emit anything in the resulting
-- 'Output' effect.
--
-- @since 0.1.2.0
runOutputBatched
    :: forall o r a
     . (Member (Output [o]) r, Typeable o)
    => Int
    -> Sem (Output o ': r) a
    -> Sem r a
runOutputBatched 0 m = ignoreOutput m
runOutputBatched size m = do
  ((c, res), a) <-
    runState (0 :: Int, [] :: [o]) $ reinterpret (\case
      Output o -> do
        (count, acc) <- get
        let newCount = 1 + count
            newAcc = o : acc
        if newCount < size
          then put (newCount, newAcc)
          else do
            output (reverse newAcc)
            put (0 :: Int, [] :: [o])
    ) m
  when (c > 0) $ output @[o] (reverse res)
  pure a

