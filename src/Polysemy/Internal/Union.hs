{-# LANGUAGE AllowAmbiguousTypes     #-}
{-# LANGUAGE CPP                     #-}
{-# LANGUAGE ConstraintKinds         #-}
{-# LANGUAGE FlexibleInstances       #-}
{-# LANGUAGE FunctionalDependencies  #-}
{-# LANGUAGE MultiParamTypeClasses   #-}
{-# LANGUAGE StrictData              #-}
{-# LANGUAGE TypeFamilies            #-}
{-# LANGUAGE PolyKinds               #-}
{-# LANGUAGE UndecidableInstances    #-}
{-# LANGUAGE UndecidableSuperClasses #-}

{-# OPTIONS_HADDOCK not-home #-}

module Polysemy.Internal.Union
  (
    Sem (..)
  , Union (..)
  , Weaving (..)
  , Member
  , MemberWithError
  , weave
  , weaveR
  , hoist
  -- * Building Unions
  , inj
  , weaken
  -- * Using Unions
  , decomp
  , prj
  , extract
  , absurdU
  , decompCoerce
  -- * Witnesses
  , SNat (..)
  , Nat (..)
  , LastMember (..)
  , Recovery (..)
  , Members
  ) where

import Polysemy.Internal.PluginLookup
import Data.Bifunctor
import Data.Traversable
import Control.Monad
import Data.Functor.Compose
import Data.Functor.Identity
import Data.Kind
import Data.Typeable
import Data.Type.Equality
import Polysemy.Internal.Kind

import Unsafe.Coerce
import GHC.Exts (Any)

#ifndef NO_ERROR_MESSAGES
import Polysemy.Internal.CustomErrors
#endif


------------------------------------------------------------------------------
-- | An extensible, type-safe union. The @r@ type parameter is a type-level
-- list of effects, any one of which may be held within the 'Union'.
data Union (r :: EffectRow) (m :: Type -> Type) a where
  Union
      :: -- A proof that the effect is actually in @r@.
         SNat n
         -- The effect to wrap. The functions 'prj' and 'decomp' can help
         -- retrieve this value later.
      -> Weaving (IndexOf r n) m a
      -> Union r m a

instance Functor (Union r m) where
  fmap f (Union w t) = Union w $ fmap f t
  {-# INLINE fmap #-}


data Weaving e m a where
  Weaving
    :: Functor f
    =>   { weaveEffect :: e m a
         -- ^ The original effect GADT originally lifted via
         -- 'Polysemy.Internal.send'. There is an invariant that @m ~ Sem r0@,
         -- where @r0@ is the effect row that was in scope when this 'Weaving'
         -- was originally created.
       , weaveState :: f ()
         -- ^ A piece of state that other effects' interpreters have already
         -- woven through this 'Weaving'. @f@ is a 'Functor', so you can always
         -- 'fmap' into this thing.
       , weaveDistrib :: forall x. f (m x) -> n (f x)
         -- ^ Distribute @f@ by transforming @m@ into @n@. We have invariants
         -- on @m@ and @n@, which means in actuality this function looks like
         -- @f ('Polysemy.Sem' (Some ': Effects ': r) x) -> 'Polysemy.Sem' r (f
         -- x)@.
       , weaveRestore :: forall r x proxy
                      .  (m ~ Sem r, Typeable r)
                      => proxy r
                      -> f x
                      -> Sem r (Maybe x)
         -- ^ Absolute lunacy
       , weaveResult :: f a -> b
         -- ^ Even though @f a@ is the moral resulting type of 'Weaving', we
         -- can't expose that fact; such a thing would prevent 'Polysemy.Sem'
         -- from being a 'Monad'.
       , weaveInspect :: forall x. f x -> Maybe x
         -- ^ A function for attempting to see inside an @f@. This is no
         -- guarantees that such a thing will succeed (for example,
         -- 'Polysemy.Error.Error' might have 'Polysemy.Error.throw'n.)
       }
    -> Weaving e n b

instance Functor (Weaving e m) where
  fmap f (Weaving e s d r f' v) = Weaving e s d r (f . f') v
  {-# INLINE fmap #-}

weave
    :: (Functor s, Functor m, Functor n)
    => s ()
    -> (∀ x. s (m x) -> n (s x))
    -> (∀ x. s x -> Maybe x)
    -> Union r m a
    -> Union r n (s a)
weave s' d v' (Union w (Weaving e s nt r f v)) = Union w $
    Weaving e (Compose $ s <$ s')
              (fmap Compose . d . fmap nt . getCompose)
              (\pr (Compose sf) -> maybe (pure Nothing) (r pr) (v' sf))
              (fmap f . getCompose)
              (v <=< v' . getCompose)
{-# INLINE weave #-}

-- | weave, and provide a function which allows to
-- reify the functorial state into the existentially
-- hidden monad given that the hidden monad has the effects
-- @effs@.
weaveR
    :: (Functor s, Functor m, Functor n, Typeable effs)
    => s ()
    -> (∀ x. s (m x) -> n (s x))
    -> (∀ x. s x -> Maybe x)
    -> proxy effs
    -> (∀ x r'. Members effs r' => s x -> Sem r' x)
    -> Union r m a
    -> Union r n (s a)
weaveR s' d v' pr ac (Union w (Weaving e s nt r f v)) = Union w $
    Weaving e (Compose $ s <$ s')
              (fmap Compose . d . fmap nt . getCompose)
              (\pr' (Compose sf) -> case attempt pr pr' (ac sf) of
                  Just g -> do
                    res <- g
                    r pr' res
                  _ -> maybe (pure Nothing) (r pr') (v' sf)
              )
              (fmap f . getCompose)
              (v <=< v' . getCompose)
{-# INLINE weaveR #-}

------------------------------------------------------------------------------
-- | Due to a quirk of the GHC plugin interface, it's only easy to find
-- transitive dependencies if they define an orphan instance. This orphan
-- instance allows us to find "Polysemy.Internal" in the polysemy-plugin.

-- Note: I moved this but it's probably not necessary to do so
instance PluginLookup Plugin

unlistTR :: TypeRep -> [TypeRep]
unlistTR t = case typeRepArgs t of
  []      -> []
  [x, xs] -> x : unlistTR xs
  _       -> error "unlistTR: argument not type-rep of a type-level list"

findEff :: SNat n -> TypeRep -> [TypeRep] -> Maybe Any
findEff sn e (e' : xs)
  | e == e'   = Just (unsafeCoerce ((sn, ()), ()))
  -- because Member e r ~ ((SNat, equality constraint), conditional type error)
  | otherwise = findEff (SS sn) e xs
findEff _ _ _ = Nothing


tuplesize :: [a] -> Any
tuplesize [] = unsafeCoerce ()
tuplesize (x : xs) = unsafeCoerce (x, tuplesize xs)

newtype Magic r r' a = Magic (Members r r' => Sem r' a)


-- Try to find each effect of r in r',
-- and execute the action if successful.
-- Returns Nothing if there's some effect in r that
-- isn't in r'.
attempt :: forall r r' a proxy proxy1
        .  (Typeable r, Typeable r')
        => proxy r
        -> proxy1 r'
        -> (Members r r' => Sem r' a)
        -> Maybe (Sem r' a)
attempt pr1 pr2 ac = do
  let want = unlistTR (typeRep pr1)
  let have = unlistTR (typeRep pr2)
  r <- for want $ \e -> findEff SZ e have
  return $
    unsafeCoerce (Magic ac :: Magic r r' a) (tuplesize r)

hoist
    :: ( Functor m
       , Functor n
       )
    => (∀ x. m x -> n x)
    -> Union r m a
    -> Union r n a
hoist f' (Union w (Weaving e s nt r f v)) = Union w $ Weaving e s (f' . nt) r f v
{-# INLINE hoist #-}


------------------------------------------------------------------------------
-- | A proof that the effect @e@ is available somewhere inside of the effect
-- stack @r@.
type Member e r = MemberNoError e r

type MemberWithError e r =
  ( MemberNoError e r
#ifndef NO_ERROR_MESSAGES
    -- NOTE: The plugin explicitly pattern matches on
    -- `WhenStuck (IndexOf r _) _`, so if you change this, make sure to change
    -- the corresponding implementation in
    -- Polysemy.Plugin.Fundep.solveBogusError
  , WhenStuck (IndexOf r (Found r e)) (AmbiguousSend r e)
#endif
  )

type MemberNoError e r =
  ( Find r e
  , e ~ IndexOf r (Found r e)
  )


------------------------------------------------------------------------------
-- | The kind of type-level natural numbers.
data Nat = Z | S Nat


------------------------------------------------------------------------------
-- | A singleton for 'Nat'.
data SNat :: Nat -> Type where
  SZ :: SNat 'Z
  SS :: SNat n -> SNat ('S n)

instance TestEquality SNat where
  testEquality SZ     SZ     = Just Refl
  testEquality (SS _) SZ     = Nothing
  testEquality SZ     (SS _) = Nothing
  testEquality (SS n) (SS m) =
    case testEquality n m of
      Nothing -> Nothing
      Just Refl -> Just Refl
  {-# INLINE testEquality #-}


type family IndexOf (ts :: [k]) (n :: Nat) :: k where
  IndexOf (k ': ks) 'Z = k
  IndexOf (k ': ks) ('S n) = IndexOf ks n


type family Found (ts :: [k]) (t :: k) :: Nat where
#ifndef NO_ERROR_MESSAGES
  Found '[]       t = UnhandledEffect t
#endif
  Found (t ': ts) t = 'Z
  Found (u ': ts) t = 'S (Found ts t)


class Find (r :: [k]) (t :: k) where
  finder :: SNat (Found r t)

instance {-# OVERLAPPING #-} Find (t ': z) t where
  finder = SZ
  {-# INLINE finder #-}

instance ( Find z t
         , Found (_1 ': z) t ~ 'S (Found z t)
         ) => Find (_1 ': z) t where
  finder = SS $ finder @_ @z @t
  {-# INLINE finder #-}


------------------------------------------------------------------------------
-- | Decompose a 'Union'. Either this union contains an effect @e@---the head
-- of the @r@ list---or it doesn't.
decomp :: Union (e ': r) m a -> Either (Union r m a) (Weaving e m a)
decomp (Union p a) =
  case p of
    SZ   -> Right a
    SS n -> Left $ Union n a
{-# INLINE decomp #-}


------------------------------------------------------------------------------
-- | Retrieve the last effect in a 'Union'.
extract :: Union '[e] m a -> Weaving e m a
extract (Union SZ a) = a
extract _ = error "impossible"
{-# INLINE extract #-}


------------------------------------------------------------------------------
-- | An empty union contains nothing, so this function is uncallable.
absurdU :: Union '[] m a -> b
absurdU = absurdU


------------------------------------------------------------------------------
-- | Weaken a 'Union' so it is capable of storing a new sort of effect.
weaken :: forall e r m a. Union r m a -> Union (e ': r) m a
weaken (Union n a) = Union (SS n) a
{-# INLINE weaken #-}



------------------------------------------------------------------------------
-- | Lift an effect @e@ into a 'Union' capable of holding it.
inj :: forall r e a m. (Functor m , Member e r) => e m a -> Union r m a
inj e = Union (finder @_ @r @e) $
  Weaving e (Identity ())
            (fmap Identity . runIdentity)
            (\_ s -> pure (Just (runIdentity s)))
            runIdentity
            (Just . runIdentity)
{-# INLINE inj #-}


------------------------------------------------------------------------------
-- | Attempt to take an @e@ effect out of a 'Union'.
prj :: forall e r a m
     . ( Member e r
       )
    => Union r m a
    -> Maybe (Weaving e m a)
prj (Union sn a) =
  case testEquality sn (finder @_ @r @e) of
    Nothing -> Nothing
    Just Refl -> Just a
{-# INLINE prj #-}


------------------------------------------------------------------------------
-- | Like 'decomp', but allows for a more efficient
-- 'Polysemy.Interpretation.reinterpret' function.
decompCoerce
    :: Union (e ': r) m a
    -> Either (Union (f ': r) m a) (Weaving e m a)
decompCoerce (Union p a) =
  case p of
    SZ -> Right a
    SS n -> Left (Union (SS n) a)
{-# INLINE decompCoerce #-}


------------------------------------------------------------------------------
-- | A proof that @end@ is the last effect in the row.
--
-- @since 0.5.0.0
class MemberNoError end r => LastMember end r | r -> end where
  decompLast
      :: Union r m a
      -> Either (Union r m a) (Union '[end] m a)

instance {-# OVERLAPPABLE #-} (LastMember end r, MemberNoError end (eff ': r))
      => LastMember end (eff ': r) where
  decompLast (Union SZ u)     = Left $ Union SZ u
  decompLast (Union (SS n) u) = first weaken $ decompLast $ Union n u

instance LastMember end '[end] where
  decompLast = Right


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
-- 'Polysemy.Error.runError' to 'Polysemy.Error.lowerError'.
--
-- The effect stack @r@ can contain arbitrary other monads inside of it. These
-- monads are lifted into effects via the 'Embed' effect. Monadic values can be
-- lifted into a 'Sem' via 'embed'.
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
-- a @'Sem' '[] a@ or a @'Sem' '[ 'Embed' m ] a@ value, which can be
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
newtype Sem r a = Sem
  { runSem
        :: ∀ m
         . Monad m
        => (∀ x. Union r (Sem r) x -> m x)
        -> m a
  }

instance Functor (Sem f) where
  fmap f (Sem m) = Sem $ \k -> fmap f $ m k
  {-# INLINE fmap #-}


instance Applicative (Sem f) where
  pure a = Sem $ const $ pure a
  {-# INLINE pure #-}

  Sem f <*> Sem a = Sem $ \k -> f k <*> a k
  {-# INLINE (<*>) #-}


instance Monad (Sem f) where
  return = pure
  {-# INLINE return #-}

  Sem ma >>= f = Sem $ \k -> do
    z <- ma k
    runSem (f z) k
  {-# INLINE (>>=) #-}

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

newtype Recovery e f = Recovery { runRecovery :: forall x r. Member e r => f x -> Sem r x }
