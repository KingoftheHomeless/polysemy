{-# LANGUAGE TemplateHaskell, NumDecimals, AllowAmbiguousTypes #-}
module Polysemy.Fork where

import           Data.Functor
import           Data.Typeable
import           Control.Concurrent
import qualified Control.Concurrent.Async as A
import           Polysemy
import           Polysemy.Trace
import           Polysemy.Error
import           Polysemy.State
import           Polysemy.Internal
import           Polysemy.Internal.Union
import           Polysemy.Final


data Ref r a where
  Ref :: A.Async a -> (a -> Sem r b) -> Ref r b

deriving instance Functor (Ref r)

data Fork ref m a where
  Fork :: m a -> Fork ref m (ref (Maybe a))
  Join :: ref a -> Fork ref m a

makeSem ''Fork

forkToFinal :: (Member (Final IO) r, Typeable r)
            => Sem (Fork (Ref r) ': r) a
            -> Sem r a
forkToFinal = usingSem $ \u -> case decomp u of
  Right (Weaving e s wv _ ex ins) -> fmap (ex . (<$ s)) $
      case e of
        Fork m -> withWeaving $ \s' wv' r' -> do
          a <- A.async $ wv' (forkToFinal (wv (m <$ s)) <$ s')
          pure $ Ref a (fmap (>>= ins) . r') <$ s'
        Join (Ref a c) -> embedFinal (A.wait a) >>= c
  Left g -> liftSem $ hoist forkToFinal g

-- Dirty tests
arke :: forall ref r
     .  (Member (Fork ref) r, Member (Error String) r)
     => Sem r (Maybe ())
arke = do
  r <- fork @ref $ throw "Yup"
  join r

test :: IO (Either String (Maybe ()))
test =
    runFinal
  . runError
  . forkToFinal $ do
  arke @(Ref '[Error String, Final IO, Embed IO])


test2 :: IO (String, Maybe String)
test2 =
    runFinal
  . traceToIO
  . runState "hello"
  . forkToFinal $ do
  let message :: Member Trace r => Int -> String -> Sem r ()
      message n msg = trace $ mconcat
        [ show n, "> ", msg ]

  a1 <- fork @(Ref '[State String, Trace, Final IO, Embed IO]) $ do
      v <- get @String
      message 1 v
      put $ reverse v

      embed $ threadDelay 1e5
      get >>= message 1

      embed $ threadDelay 1e5
      get @String

  void $ fork @(Ref '[State String, Trace, Final IO, Embed IO]) $ do
      embed $ threadDelay 5e4
      get >>= message 2
      put "pong"

  Polysemy.Fork.join a1 <* put "final"
