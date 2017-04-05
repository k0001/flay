{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}

module Data.Functor.Flay
 ( Flay
 -- * Flayable
 , Flayable(flay)
 -- ** Generics
 , gflay
 , GFlay
 , GFlay'(gflay')
 -- ** Utils
 , Trivial
 , trivial
 , trivial'
 , collect
 , collect'
 -- ** Re-exports
 , Constraint
 , Dict(Dict)
 ) where

import Data.Functor.Const (Const(Const, getConst))
import Data.Constraint (Constraint, Dict(Dict))
import qualified GHC.Generics as G

--------------------------------------------------------------------------------

-- | @'Flay' c m s t f g@ allows converting @s@ to @t@ by replacing
-- ocurrences of @f@ with @g@ by applicatively applying a function
-- @(forall a. c a => f a -> m (g a))@ to targeted occurences of @f a@ inside
-- @s@.
--
-- /to flay: tr. v., to strip off the skin or surface of./
--
-- Example:
--
-- @
-- data Foo f = Foo (f 'Int') (f 'Bool')
--
-- flayFoo :: ('Applicative' m, c 'Int', c 'Bool') => 'Flay' c m (Foo f) (Foo g) f g
-- flayFoo h (Foo a b) = Foo \<$> h 'Dict' a \<*> h 'Dict' b
-- @
--
-- Identity law 1:
--
-- @
-- forall ('fl' :: 'Flay' c m s t g).
--   'Data.Functor.Identity.runIdentity' . 'trivial'' fl 'pure'
--      = 'id' :: s -> s
-- @
--
-- Identity law 2:
--
-- @
-- forall ('fl' :: 'Flay' c m m m m). 'Monad' m =>
--   'join' . 'trivial'' fl 'pure'
--      = 'id' :: m -> m
-- @
type Flay (c :: * -> Constraint) m s t f g
  = (forall a. Dict (c a) -> f a -> m (g a)) -> s -> m t

--------------------------------------------------------------------------------

-- | Default 'Flay' implementation for @s@ and @t@.
--
-- When defining 'Flayable' instances, you will usually leave @c@, @m@, @f@, and
-- @g@ polymomrphic.
class Applicative m => Flayable c m s t f g | s -> f, t -> g, s g -> t, t f -> s where
  flay :: Flay c m s t f g
  -- | If @s@ and @g@ are instances of 'G.Generic', then 'flay' gets a default
  -- implementation.
  --
  -- @
  -- data Foo f = Foo (f Int) (f Bool)
  --   deriving (Generic)
  --
  -- instance ('Applicative' m, c 'Int', c 'Bool') => 'Flayable' c m (Foo f) (Foo g) f g
  -- @
  --
  -- Notice that while this default definition work for an @s@ having "nested
  -- 'Flayables'", GHC will prompt you for some additional constraints related
  -- to 'GFlay'' in that case.
  default flay :: GFlay c m s t f g => Flay c m s t f g
  flay = gflay
  {-# INLINE flay #-}

-- | Isomorphic to @c a => f a -> m (g a)@.
instance (Applicative m, c a) => Flayable c m (f a) (g a) f g where
  flay = \h fa -> h Dict fa
  {-# INLINE flay #-}

--------------------------------------------------------------------------------

-- | 'Constraint' trivially satisfied by every type.
--
-- This can be used as the @c@ parameter to 'Flay' or 'Flayable' in case you are
-- not interested in observing the values inside @f@.
class Trivial (a :: k)
instance Trivial (a :: k)

-- | You can use 'trivial' if you don't about the @c@ argument to 'Flay'. This
-- implies that you won't be able to observe the @a@ in @forall a. f a@.
--
-- @
-- 'trivial' fl h
--    = fl (\('Dict' :: 'Dict' ('Trivial' a)) (fa :: f a) -> h fa)
-- @
trivial'
  :: forall m s t f g
  .  Flay Trivial m s t f g
  -> (forall a. Trivial a => f a -> m (g a))
  -> s
  -> m t  -- ^
trivial' fl = \h s -> fl (\(Dict :: Dict (Trivial a)) (fa :: f a) -> h fa) s
{-# INLINE trivial' #-}

-- | Like 'trivial'', but works on a 'Flayable' instead of taking an explicit
-- 'Flay'.
--
-- @
-- 'trivial' = 'trivial'' 'flay'
-- @
trivial
  :: Flayable Trivial m s t f g
  => (forall a. Trivial a => f a -> m (g a))
  -> s
  -> m t  -- ^
trivial = trivial' flay
{-# INLINE trivial #-}

--------------------------------------------------------------------------------

-- | Convenience 'Constraint' for satisfying basic 'GFlay'' needs for @s@ and @t@.
class (G.Generic s, G.Generic t, GFlay' c m (G.Rep s) (G.Rep t) f g) => GFlay c m s t f g
instance (G.Generic s, G.Generic t, GFlay' c m (G.Rep s) (G.Rep t) f g) => GFlay c m s t f g

gflay :: GFlay c m s t f g => Flay c m s t f g
gflay = \h s -> G.to <$> gflay' h (G.from s)
{-# INLINE gflay #-}

class Applicative m => GFlay' c m s t f g where
  gflay' :: Flay c m (s p) (t p) f g

instance Applicative m => GFlay' c m G.V1 G.V1 f g where
  gflay' _ _ = undefined -- unreachable
  {-# INLINE gflay' #-}

-- Is this OK? Necessary?
instance GFlay' c m s t f g
  => GFlay' c m (G.Rec1 s) (G.Rec1 t) f g where
  gflay' h (G.Rec1 sp) = G.Rec1 <$> gflay' h sp
  {-# INLINE gflay' #-}

instance (Flayable c m (f a) (g a) f g, c a) => GFlay' c m (G.K1 r (f a)) (G.K1 r (g a)) f g where
  gflay' h (G.K1 fa) = G.K1 <$> flay h fa
  {-# INLINE gflay' #-}

instance Applicative m => GFlay' c m (G.K1 r x) (G.K1 r x) f g where
  gflay' _ x = pure x
  {-# INLINE gflay' #-}

instance GFlay' c m s t f g => GFlay' c m (G.M1 i j s) (G.M1 i j t) f g where
  gflay' h (G.M1 sp) = G.M1 <$> gflay' h sp
  {-# INLINE gflay' #-}

instance (GFlay' c m sl tl f g, GFlay' c m sr tr f g)
  => GFlay' c m (sl G.:*: sr) (tl G.:*: tr) f g where
  gflay' h (slp G.:*: srp) = (G.:*:) <$> gflay' h slp <*> gflay' h srp
  {-# INLINE gflay' #-}

instance (GFlay' c m sl tl f g, GFlay' c m sr tr f g)
  => GFlay' c m (sl G.:+: sr) (tl G.:+: tr) f g where
  gflay' h x = case x of
    G.L1 slp -> G.L1 <$> gflay' h slp
    G.R1 srp -> G.R1 <$> gflay' h srp
  {-# INLINE gflay' #-}

--------------------------------------------------------------------------------

-- | Collect all of the @f a@ of the given 'Flay' into a 'Monoid' @b@.
--
-- Example:
--
-- @
-- data Foo f = Foo (f 'Int') (f 'Bool')
--
-- flayFoo :: ('Applicative' m, c 'Int', c 'Bool') => 'Flay' c m (Foo f) (Foo g) f g
-- flayFoo h (Foo a b) = Foo \<$> h 'Dict' a \<*> h 'Dict' b
--
-- > 'collect'' flayFoo
--       (\('Dict' :: 'Dict' ('Show' a)) ('Data.Functor.Identity.Identity' (a :: a))' -> ['show' a])
--       (Foo ('pure' 4) ('pure' 'True'))
-- ["4",\"True"]
-- @
collect'
  :: Monoid b
  => Flay c (Const b) s t f (Const ())
  -> (forall a. Dict (c a) -> f a -> b)
  -> s
  -> b    -- ^
collect' fl k = \s -> getConst (fl (\d fa -> Const (k d fa)) s)
{-# INLINE collect' #-}

-- | Like 'collect'', but works on a 'Flayable' instead of an explicit 'Flay'.
collect
  :: (Monoid b, Flayable c (Const b) s t f (Const ()))
  => (forall a. Dict (c a) -> f a -> b)
  -> s
  -> b    -- ^
collect k = collect' flay k
{-# INLINE collect #-}

