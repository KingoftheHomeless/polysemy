module Polysemy.Final where

import Polysemy
import Polysemy.Internal
import Polysemy.Internal.Union

import Data.Typeable

data Final m z a where
  WithWeaving :: Typeable r =>
                 (   forall f
                  .  Functor f
                  => f ()
                  -> (forall x. f (Sem r x) -> m (f x))
                  -> (forall x. f x -> Sem r (Maybe x))
                  -> m (f a)
                 )
              -> proxy r
              -> Final m (Sem r) a

withWeaving :: forall m a r
            .  (Member (Final m) r, Typeable r)
            => (   forall f
                .  Functor f
                => f ()
                -> (forall x. f (Sem r x) -> m (f x))
                -> (forall x. f x -> Sem r (Maybe x))
                -> m (f a)
                )
            -> Sem r a
withWeaving wv = send (WithWeaving wv (Proxy :: Proxy r))

runFinal :: Monad m => Sem '[Final m, Embed m] a -> m a
runFinal = usingSem $ \u -> case decomp u of
  Right (Weaving (WithWeaving act pr) s wv rc ex _) ->
    ex <$> act s (runFinal . wv) (rc pr)
  Left g -> case extract g of
    Weaving (Embed m) s _ _ ex _ -> ex . (<$ s) <$> m

embedFinal :: forall m a r
           .  (Member (Final m) r, Typeable r, Functor m)
           => m a
           -> Sem r a
embedFinal m = withWeaving $ \s _ _ -> fmap (<$ s) m
