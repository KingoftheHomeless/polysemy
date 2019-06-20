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
  , sendM
  , run
  , runM
  , raise
  , raiseUnder
  , raiseUnder2
  , raiseUnder3
  , Lift (..)
  , usingSem
  , liftSem
  , hoistSem
  ) where

import Control.Applicative
import Control.Monad
import Control.Monad.Fail
import Control.Monad.Fix
import Control.Monad.IO.Class
import Data.Functor.Identity
import Data.Kind
import Polysemy.Internal.Fixpoint
import Polysemy.Internal.Lift
import Polysemy.Internal.NonDet
import Polysemy.Internal.PluginLookup
import Polysemy.Internal.Union


------------------------------------------------------------------------------
-- | The 'Sem' monad handles computations of arbitrary extensible effects.
-- A value of type @Sem r@ describes a program with the capabilities of
-- @r@. For best results, @r@ should always be kept polymorphic, but you can
-- add capabilities via the 'Member' constraint.
--
-- The value of the 'Sem' monad is that it allows you to write programs
-- against a set of effects without a predefined meaning, and provide that
-- meaning later. For example, unlike with mtl, you can decide to interpret an
-- 'Polysemy.Error.Error' effect tradtionally as an 'Either', or instead
-- significantly faster as an 'IO' 'Control.Exception.Exception'. These
-- interpretations (and others that you might add) may be used interchangably
-- without needing to write any newtypes or 'Monad' instances. The only
-- change needed to swap interpretations is to change a call from
-- 'Polysemy.Error.runError' to 'Polysemy.Error.runErrorInIO'.
--
-- The effect stack @r@ can contain arbitrary other monads inside of it. These
-- monads are lifted into effects via the 'Lift' effect. Monadic values can be
-- lifted into a 'Sem' via 'sendM'.
--
-- A 'Sem' can be interpreted as a pure value (via 'run') or as any
-- traditional 'Monad' (via 'runM'). Each effect @E@ comes equipped with some
-- interpreters of the form:
--
-- @
-- runE :: 'Sem' (E ': r) a -> 'Sem' r a
-- @
--
-- which is responsible for removing the effect @E@ from the effect stack. It
-- is the order in which you call the interpreters that determines the
-- monomorphic representation of the @r@ parameter.
--
-- After all of your effects are handled, you'll be left with either
-- a @'Sem' '[] a@ or a @'Sem' '[ 'Lift' m ] a@ value, which can be
-- consumed respectively by 'run' and 'runM'.
--
-- ==== Examples
--
-- As an example of keeping @r@ polymorphic, we can consider the type
--
-- @
-- 'Member' ('Polysemy.State.State' String) r => 'Sem' r ()
-- @
--
-- to be a program with access to
--
-- @
-- 'Polysemy.State.get' :: 'Sem' r String
-- 'Polysemy.State.put' :: String -> 'Sem' r ()
-- @
--
-- methods.
--
-- By also adding a
--
-- @
-- 'Member' ('Polysemy.Error' Bool) r
-- @
--
-- constraint on @r@, we gain access to the
--
-- @
-- 'Polysemy.Error.throw' :: Bool -> 'Sem' r a
-- 'Polysemy.Error.catch' :: 'Sem' r a -> (Bool -> 'Sem' r a) -> 'Sem' r a
-- @
--
-- functions as well.
--
-- In this sense, a @'Member' ('Polysemy.State.State' s) r@ constraint is
-- analogous to mtl's @'Control.Monad.State.Class.MonadState' s m@ and should
-- be thought of as such. However, /unlike/ mtl, a 'Sem' monad may have
-- an arbitrary number of the same effect.
--
-- For example, we can write a 'Sem' program which can output either
-- 'Int's or 'Bool's:
--
-- @
-- foo :: ( 'Member' ('Polysemy.Output.Output' Int) r
--        , 'Member' ('Polysemy.Output.Output' Bool) r
--        )
--     => 'Sem' r ()
-- foo = do
--   'Polysemy.Output.output' @Int  5
--   'Polysemy.Output.output' True
-- @
--
-- Notice that we must use @-XTypeApplications@ to specify that we'd like to
-- use the ('Polysemy.Output.Output' 'Int') effect.
--
-- @since 0.1.2.0
newtype Sem r f a = Sem
  { runSem
        :: ∀ m
         . Monad m
        => (∀ x. Union r f (Sem r f) x -> m x)
        -> m a
  }


------------------------------------------------------------------------------
-- | Due to a quirk of the GHC plugin interface, it's only easy to find
-- transitive dependencies if they define an orphan instance. This orphan
-- instance allows us to find "Polysemy.Internal" in the polysemy-plugin.
instance PluginLookup Plugin


------------------------------------------------------------------------------
-- | Makes constraints of functions that use multiple effects shorter by
-- translating single list of effects into multiple 'Member' constraints:
--
-- @
-- foo :: 'Members' \'[ 'Polysemy.Output.Output' Int
--                 , 'Polysemy.Output.Output' Bool
--                 , 'Polysemy.State' String
--                 ] r
--     => 'Sem' r ()
-- @
--
-- translates into:
--
-- @
-- foo :: ( 'Member' ('Polysemy.Output.Output' Int) r
--        , 'Member' ('Polysemy.Output.Output' Bool) r
--        , 'Member' ('Polysemy.State' String) r
--        )
--     => 'Sem' r ()
-- @
--
-- @since 0.1.2.0
type family Members es r :: Constraint where
  Members '[]       r = ()
  Members (e ': es) r = (Member e r, Members es r)


------------------------------------------------------------------------------
-- | Like 'runSem' but flipped for better ergonomics sometimes.
usingSem
    :: Monad m
    => (∀ x. Union r f (Sem r f) x -> m x)
    -> Sem r f a
    -> m a
usingSem k m = runSem m k
{-# INLINE usingSem #-}


instance Functor (Sem r f) where
  fmap f (Sem m) = Sem $ \k -> fmap f $ m k
  {-# INLINE fmap #-}


instance Applicative (Sem r f) where
  pure a = Sem $ const $ pure a
  {-# INLINE pure #-}

  Sem f <*> Sem a = Sem $ \k -> f k <*> a k
  {-# INLINE (<*>) #-}


instance Monad (Sem r f) where
  return = pure
  {-# INLINE return #-}

  Sem ma >>= f = Sem $ \k -> do
    z <- ma k
    runSem (f z) k
  {-# INLINE (>>=) #-}


instance (Member NonDet r) => Alternative (Sem r Identity) where
  empty = send Empty
  {-# INLINE empty #-}
  a <|> b = do
    send (Choose id) >>= \case
      False -> a
      True  -> b
  {-# INLINE (<|>) #-}

-- | @since 0.2.1.0
instance (Member NonDet r) => MonadPlus (Sem r Identity) where
  mzero = empty
  mplus = (<|>)

-- | @since 0.2.1.0
instance (Member NonDet r) => MonadFail (Sem r Identity) where
  fail = const empty


------------------------------------------------------------------------------
-- | This instance will only lift 'IO' actions. If you want to lift into some
-- other 'MonadIO' type, use this instance, and handle it via the
-- 'Polysemy.IO.runIO' interpretation.
instance (Member (Lift IO) r) => MonadIO (Sem r Identity) where
  liftIO = sendM
  {-# INLINE liftIO #-}

instance Member Fixpoint r => MonadFix (Sem r Identity) where
  mfix f = send $ Fixpoint f
  {-# INLINE mfix #-}


liftSem :: Union r f (Sem r f) a -> Sem r f a
liftSem u = Sem $ \k -> k u
{-# INLINE liftSem #-}


hoistSem
    :: (∀ x. Union r f (Sem r f) x -> Union r' f (Sem r' f) x)
    -> Sem r f a
    -> Sem r' f a
hoistSem nat (Sem m) = Sem $ \k -> m $ \u -> k $ nat u
{-# INLINE hoistSem #-}

------------------------------------------------------------------------------
-- | Introduce an effect into 'Sem'. Analogous to
-- 'Control.Monad.Class.Trans.lift' in the mtl ecosystem
raise :: ∀ e f r a. Sem r f a -> Sem (e ': r) f a
raise = hoistSem $ hoist raise_b . weaken
{-# INLINE raise #-}


raise_b :: Sem r f a -> Sem (e ': r) f a
raise_b = raise
{-# NOINLINE raise_b #-}


------------------------------------------------------------------------------
-- | Like 'raise', but introduces a new effect underneath the head of the
-- list.
raiseUnder :: ∀ e2 e1 r f a. Sem (e1 ': r) f a -> Sem (e1 ': e2 ': r) f a
raiseUnder = hoistSem $ hoist raiseUnder_b . weakenUnder
  where
    weakenUnder :: ∀ m x. Union (e1 ': r) f m x -> Union (e1 ': e2 ': r) f m x
    weakenUnder (Union SZ a) = Union SZ a
    weakenUnder (Union (SS n) a) = Union (SS (SS n)) a
    {-# INLINE weakenUnder #-}
{-# INLINE raiseUnder #-}


raiseUnder_b :: Sem (e1 ': r) f a -> Sem (e1 ': e2 ': r) f a
raiseUnder_b = raiseUnder
{-# NOINLINE raiseUnder_b #-}


------------------------------------------------------------------------------
-- | Like 'raise', but introduces two new effects underneath the head of the
-- list.
raiseUnder2 :: ∀ e2 e3 e1 f r a. Sem (e1 ': r) f a -> Sem (e1 ': e2 ': e3 ': r) f a
raiseUnder2 = hoistSem $ hoist raiseUnder2_b . weakenUnder2
  where
    weakenUnder2 ::  ∀ m x. Union (e1 ': r) f m x -> Union (e1 ': e2 ': e3 ': r) f m x
    weakenUnder2 (Union SZ a) = Union SZ a
    weakenUnder2 (Union (SS n) a) = Union (SS (SS (SS n))) a
    {-# INLINE weakenUnder2 #-}
{-# INLINE raiseUnder2 #-}


raiseUnder2_b :: Sem (e1 ': r) f a -> Sem (e1 ': e2 ': e3 ': r) f a
raiseUnder2_b = raiseUnder2
{-# NOINLINE raiseUnder2_b #-}


------------------------------------------------------------------------------
-- | Like 'raise', but introduces two new effects underneath the head of the
-- list.
raiseUnder3
    :: ∀ e2 e3 e4 e1 f r a
     . Sem (e1 ': r) f a
    -> Sem (e1 ': e2 ': e3 ': e4 ': r) f a
raiseUnder3 = hoistSem $ hoist raiseUnder3_b . weakenUnder3
  where
    weakenUnder3 ::  ∀ m x. Union (e1 ': r) f m x -> Union (e1 ': e2 ': e3 ': e4 ': r) f m x
    weakenUnder3 (Union SZ a) = Union SZ a
    weakenUnder3 (Union (SS n) a) = Union (SS (SS (SS (SS n)))) a
    {-# INLINE weakenUnder3 #-}
{-# INLINE raiseUnder3 #-}


raiseUnder3_b :: Sem (e1 ': r) f a -> Sem (e1 ': e2 ': e3 ': e4 ': r) f a
raiseUnder3_b = raiseUnder3
{-# NOINLINE raiseUnder3_b #-}


------------------------------------------------------------------------------
-- | Lift an effect into a 'Sem'. This is used primarily via
-- 'Polysemy.makeSem' to implement smart constructors.
send :: Member e r => e (Sem r Identity) a -> Sem r Identity a
send = liftSem . inj
{-# INLINE[3] send #-}


------------------------------------------------------------------------------
-- | Lift a monadic action @m@ into 'Sem'.
sendM :: Member (Lift m) r => m a -> Sem r Identity a
sendM = send . Lift
{-# INLINE sendM #-}


------------------------------------------------------------------------------
-- | Run a 'Sem' containing no effects as a pure value.
run :: Sem '[] f a -> a
run (Sem m) = runIdentity $ m absurdU
{-# INLINE run #-}


------------------------------------------------------------------------------
-- | Lower a 'Sem' containing only a single lifted 'Monad' into that
-- monad.
runM :: (Functor f, Monad m) => Sem '[Lift m] f a -> m a
runM (Sem m) = m $ \z ->
  case extract z of
    Yo e s _ f _ -> do
      a <- unLift e
      pure $ f $ a <$ s
{-# INLINE runM #-}

infect :: Functor f => Sem r Identity a -> Sem r f a
infect (Sem m) = Sem $ \k -> m $ \u -> k $ infect2 $ hoist infect u

infect2 :: Functor f => Union r Identity (Sem r f) x  -> Union r f (Sem r f) x
infect2 (Union w (Yo a b c d e)) = Union w $ Yo a undefined undefined undefined _
