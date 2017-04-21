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

-- | The most commonly used names in this module are intended to be imported
-- unqualified:
--
-- @
-- import Flay (Flay, Flayable(flay), Dict(Dict))
-- @
--
-- The rest of the names, qualified:
--
-- @
-- import qualified Flay
-- @
module Flay
 ( Flay
 , inner
 , outer
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
 , Dict(Dict)
 ) where

import Control.Monad (join)
import Data.Functor.Identity (Identity, runIdentity)
import Data.Functor.Const (Const(Const, getConst))
import Data.Constraint (Constraint, Dict(Dict))
import qualified GHC.Generics as G

--------------------------------------------------------------------------------

-- | @'Flay' c m s t f g@ allows converting @s@ to @t@ by replacing
-- ocurrences of @f@ with @g@ by applicatively applying a function
-- @(forall a. c a => f a -> m (g a))@ to targeted occurences of @f a@ inside
-- @s@.
--
-- A 'Flay' must obey the 'inner' identity law (and 'outer' identity law as
-- well, if the 'Flay' fits the type expected by 'outer').
--
-- When using a 'Flay', @m@ will be required to be a 'Functor' in case the 'Flay'
-- targets one element, or an 'Applicative' if it targets more than one. There
-- will be no constraints on the rest of the arguments to 'Flay'.
--
-- /to flay: tr. v., to strip off the skin or surface of./
--
-- Example 'Flay':
--
-- @
-- data Foo f = Foo (f 'Int') (f 'Bool')
--
-- flayFoo :: ('Applicative' m, c 'Int', c 'Bool') => 'Flay' c m (Foo f) (Foo g) f g
-- flayFoo h (Foo a b) = Foo \<$> h 'Dict' a \<*> h 'Dict' b
-- @
--
-- ==== Example 1: Removing uncertaininy
--
-- Given the 'Foo' above, consider the following values:
--
-- @
-- foo1 :: Foo 'Maybe'
-- foo1 = Foo ('Just' 1) 'Nothing'
--
-- foo2 :: Foo 'Maybe'
-- foo2 = Foo ('Just' 2) ('Just' 'True')
-- @
--
-- It is possible to remove the /uncertainty/ of the fields in 'Foo' perhaps
-- being empty ('Nothing') by converting @Foo 'Maybe'@ to @Foo 'Identity'@.
-- However, we can't just write a function of type @Foo 'Maybe' -> Foo
-- 'Identity'@ because we have the possiblity of some of the fields being
-- 'Nothing', like in @foo1@. Instead, we are looking for a function @Foo
-- 'Maybe' -> 'Maybe' (Foo 'Identity')@ which will result on 'Just' only as long
-- as all of the fields in 'Foo' is 'Just', like in @foo2@. This is exactly what
-- 'Applicative' enables us to do:
--
-- @
-- fooMaybeToIdentity :: Foo 'Maybe' -> 'Maybe' (Foo 'Identity')
-- fooMaybeToIdentity (Foo a b) = Foo \<$> 'fmap' 'Identity' a \<*> 'fmap' 'Identity' b
-- @
--
-- In fact, notice that we are not really working with 'Just' and 'Nothing'
-- directly, so we might as well leave 'Maybe' polymorphic:
--
-- @
-- fooMToIdentity :: 'Applicative' m => Foo m -> m (Foo 'Identity')
-- fooMToIdentity (Foo a b) = Foo \<$> 'fmap' 'Identity' a \<*> 'fmap' 'Identity' b
-- @
--
-- 'Flay', among other things, is intended to generalize this pattern so that
-- whatever choice of 'Foo', 'Maybe' or 'Identity' you make, you can use
-- 'Applicative' this way. The easiest way to use 'Flay' is through 'trivial'',
-- which is sufficient unless we need to enforce some constrain in the target
-- elements wrapped in @m@ inside foo (we don't need this now). With 'trivial'',
-- we could have defined @fooFToIdentity@ this way:
--
-- @
-- fooMToIdentity :: 'Applicative' m => Foo m -> m (Foo 'Identity')
-- fooMToIdentity = 'trivial'' flayFoo ('fmap' 'Identity')
-- @
--
-- Some important things to notice here are that we are reusing 'flayFoo''s
-- knowledge of 'Foo''s structure, and that the construction of the 'Identity'
-- applies to any value wrapped in @m@ ('Int' and 'Bool' in our case). Compare
-- this last fact to 'traverse', where the target type must be the same.
--
--
-- ==== Example 2: 'collect''
--
-- See the documentation for 'collect''. To sum up: for any given 'Flay', we can
-- collect all of the 'Flay''s targets into a 'Monoid', without knowing anything
-- about the targets themselves beyond the fact that they satisfy a particular
-- constraint.
--
--
-- ==== Example 3: Reusable datatype shapes
--
-- We can use a 'Flay' to repurpose a datatype while maintaining its "shape".
-- For example, given our @Foo@ example from before: @Foo 'Identity'@
-- represents the presence of two values 'Int' and 'Char', @Foo 'Maybe'@
-- represents their potential presence, @Foo []@ represents the potential for
-- zero or more 'Int's and 'Char's, while @Foo ('Const' x)@ represent the
-- presence of two values of type @x@. We can use 'flayFoo' to convert between
-- these representations. In all these cases, the shape of 'Foo' is preserved,
-- meaning we can continue to pattern match or project on it.
type Flay (c :: k -> Constraint) (m :: * -> *) s t (f :: k -> *) (g :: k -> *)
  = (forall (a :: k). Dict (c a) -> f a -> m (g a)) -> s -> m t

-- | Inner identity law:
--
-- @
-- (\\fl -> 'runIdentity' . 'trivial'' fl 'pure') = 'id'
-- @
inner :: Flay Trivial Identity s s f f -> s -> s
inner fl = runIdentity . trivial' fl pure

-- | Outer identity law:
--
-- @
-- (\\fl -> 'join' . 'trivial'' fl 'pure') = 'id'
-- @
outer :: Monad m => Flay Trivial m (m x) (m x) m m -> m x -> m x
outer fl = join . trivial' fl pure


--------------------------------------------------------------------------------

-- | Default 'Flay' implementation for @s@ and @t@.
--
-- When defining 'Flayable' instances, you will usually leave @c@, @m@, @f@, and
-- @g@ polymomrphic.

-- TODO: See if `c` can be made of kind `k -> Constraint`, probably in GHC 8.2.
class Flayable (c :: * -> Constraint) m s t f g | s -> f, t -> g, s g -> t, t f -> s where
  flay :: Flay c m s t f g
  -- | If @s@ and @g@ are instances of 'G.Generic', then 'flay' gets a default
  -- implementation. For example, provided the @Foo@ datatype shown in the
  -- documentation for 'Flay' had a 'G.Generic' instance, then the following
  -- 'Flayable' instance would get a default implementation for 'flay':
  --
  -- @
  -- instance ('Applicative' m, c 'Int', c 'Bool') => 'Flayable' c m (Foo f) (Foo g) f g
  -- @
  --
  -- Notice that while this default definition works for an @s@ having "nested
  -- 'Flayables'", GHC will prompt you for some additional constraints related
  -- to 'GFlay'' in order for it to compile.
  default flay :: (Functor m, GFlay c m s t f g) => Flay c m s t f g
  flay = gflay
  {-# INLINE flay #-}

-- | Isomorphic to @c a => f a -> m (g a)@.
instance {-# OVERLAPPABLE #-} c a => Flayable c m (f a) (g a) f g where
  flay = \h fa -> h Dict fa
  {-# INLINE flay #-}

--------------------------------------------------------------------------------

-- | 'Constraint' trivially satisfied by every type.
--
-- This can be used as the @c@ parameter to 'Flay' or 'Flayable' in case you are
-- not interested in observing the values inside @f@.
class Trivial (a :: k)
instance Trivial (a :: k)

-- | You can use 'trivial'' if you don't care about the @c@ argument to 'Flay'.
-- This implies that you won't be able to observe the @a@ in @forall a. f a@,
-- all you can do with such @a@ is pass it around.
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
class (G.Generic s, G.Generic t, GFlay' c m (G.Rep s) (G.Rep t) f g)
  => GFlay (c :: k -> Constraint) m s t f g
instance (G.Generic s, G.Generic t, GFlay' c m (G.Rep s) (G.Rep t) f g)
  => GFlay (c :: k -> Constraint) m s t f g

gflay :: (Functor m, GFlay c m s t f g) => Flay c m s t f g
gflay = \h s -> G.to <$> gflay' h (G.from s)
{-# INLINE gflay #-}

class GFlay' (c :: k -> Constraint) m s t f g where
  gflay' :: Flay c m (s p) (t p) f g

instance GFlay' c m G.V1 G.V1 f g where
  gflay' _ _ = undefined -- unreachable
  {-# INLINE gflay' #-}

-- Is this necessary?
instance (Functor m, GFlay' c m s t f g)
  => GFlay' c m (G.Rec1 s) (G.Rec1 t) f g where
  gflay' h (G.Rec1 sp) = G.Rec1 <$> gflay' h sp
  {-# INLINE gflay' #-}

instance (Functor m, Flayable c m (f a) (g a) f g) => GFlay' c m (G.K1 r (f a)) (G.K1 r (g a)) f g where
  gflay' h (G.K1 fa) = G.K1 <$> flay h fa
  {-# INLINE gflay' #-}

instance Applicative m => GFlay' c m (G.K1 r x) (G.K1 r x) f g where
  gflay' _ x = pure x
  {-# INLINE gflay' #-}

instance (Functor m, GFlay' c m s t f g)
  => GFlay' c m (G.M1 i j s) (G.M1 i j t) f g where
  gflay' h (G.M1 sp) = G.M1 <$> gflay' h sp
  {-# INLINE gflay' #-}

instance (Applicative m, GFlay' c m sl tl f g, GFlay' c m sr tr f g)
  => GFlay' c m (sl G.:*: sr) (tl G.:*: tr) f g where
  gflay' h (slp G.:*: srp) = (G.:*:) <$> gflay' h slp <*> gflay' h srp
  {-# INLINE gflay' #-}

instance (Functor m, GFlay' c m sl tl f g, GFlay' c m sr tr f g)
  => GFlay' c m (sl G.:+: sr) (tl G.:+: tr) f g where
  gflay' h x = case x of
    G.L1 slp -> G.L1 <$> gflay' h slp
    G.R1 srp -> G.R1 <$> gflay' h srp
  {-# INLINE gflay' #-}

--------------------------------------------------------------------------------

-- | Collect all of the @f a@ of the given 'Flay' into a 'Monoid' @b@.
--
-- Example usage, given 'Foo' and 'flayFoo' examples given in the documentation
-- for 'Flay':
--
-- @
-- > 'collect'' flayFoo
--       (\\('Dict' :: 'Dict' ('Show' a)) ('Identity' (a :: a)) -> ['show' a])
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
