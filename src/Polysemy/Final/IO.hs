-- | Useful higher-order 'IO' actions lifted to @'Polysemy.Final.Final' 'IO'@.
--
-- This module is intended to be imported qualified.
module Polysemy.Final.IO
  ( -- * Actions
    catch
  , bracket
  , bracketOnError
  , mask
  , onException
  , finally
  ) where

import Polysemy
import Polysemy.Final

import qualified Control.Exception as X

mask :: forall r a
      . Member (Final IO) r
     => ((forall x. Sem r x -> Sem r x) -> Sem r a)
     -> Sem r a
mask main = withWeavingToFinal $ \s wv _ -> X.mask $ \restore ->
  let
    restore' :: forall x. Sem r x -> Sem r x
    restore' = \m -> withWeavingToFinal $ \s' wv' _ -> restore (wv' (m <$ s'))
    {-# INLINE restore' #-}
  in
    wv (main restore' <$ s)


------------------------------------------------------------------------------
-- | The second branch will execute if the first fails for any reason, be it
-- an 'IO' exception or an exception of a purely-interpreted effect.
onException
  :: Member (Final IO) r
  => Sem r a
  -> Sem r b
  -> Sem r a
onException m h = withStrategicToFinal $ do
  m'  <- runS m
  h'  <- runS h
  ins <- getInspectorS
  pure $ do
    res <- m' `X.onException` h'
    case inspect ins res of
      Just _ -> pure res
      _      -> res <$ h'

finally
  :: Member (Final IO) r
  => Sem r a
  -> Sem r b
  -> Sem r a
finally m h = mask $ \restore -> do
  res <- restore m `onException` h
  res <$ h


bracket
  :: Member (Final IO) r
  => Sem r a
  -> (a -> Sem r b)
  -> (a -> Sem r c)
  -> Sem r c
bracket alloc dealloc use = mask $ \restore -> do
  a   <- alloc
  res <- restore (use a) `onException` dealloc a
  res <$ dealloc a

------------------------------------------------------------------------------
-- | The deallocation action will execute if the use of the resource fails for
-- any reason, be it an 'IO' exception or a purely-interpreted effect.
bracketOnError
  :: Member (Final IO) r
  => Sem r a
  -> (a -> Sem r b)
  -> (a -> Sem r c)
  -> Sem r c
bracketOnError alloc dealloc use = mask $ \restore -> do
  a   <- alloc
  restore (use a) `onException` dealloc a

catch
  :: (X.Exception e, Member (Final IO) r)
  => Sem r a
  -> (e -> Sem r a)
  -> Sem r a
catch m h = withStrategicToFinal $ do
  m' <- runS m
  h' <- bindS h
  s  <- getInitialStateS
  pure $ m' `X.catch` \e -> h' (e <$ s)
