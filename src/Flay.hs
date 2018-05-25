{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE CPP #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE UndecidableSuperClasses #-}

-- | The most commonly used names in this module are intended to be imported
-- unqualified, as necessary:
--
-- @
-- import Flay (Flay, Flayable(flay), Flayable1(flay1))
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
 -- * Flayable
 , Flayable(flay)
 , Flayable1(flay1)
 -- ** Generics
 , gflay
 , GFlay
 , GFlay'(gflay')
 -- ** Utils
 , All
 , Trivial
 , trivialize
 , trivial
 , trivial1
 , trivial'
 , collect
 , collect1
 , collect'
 , zip
 , zip1
 , unsafeZip
 , terminal
 , Terminal
 , GTerminal(gterminal)
 -- * Pump & Dump
 , Pump
 , GPump
 , pump
 , dump
 -- ** Re-exports
 , Dict(Dict)
 ) where

import Control.Monad.Trans.Class (lift)
import Control.Monad.Trans.State (StateT(StateT), runStateT)
import Control.Monad.Trans.Maybe (MaybeT(MaybeT), runMaybeT)
import Data.Constraint (Constraint, Dict(Dict))
import Data.Dynamic (Dynamic, toDyn, fromDynamic)
import Data.Functor.Product (Product(Pair))
import Data.Functor.Const (Const(Const, getConst))
import Data.Functor.Identity (Identity(runIdentity))
import Data.Typeable (Typeable)
import qualified GHC.Generics as G
import Prelude hiding (zip)

--------------------------------------------------------------------------------

-- | @'Flay' c s t f g@ allows converting @s@ to @t@ by replacing
-- ocurrences of @f@ with @g@ by applicatively applying a function
-- @(forall a. c a => f a -> m (g a))@ to targeted occurences of @f a@ inside
-- @s@.
--
-- A 'Flay' must obey the 'inner' identity law.
--
-- When defining 'Flay' values, you should leave @c@, @f@, and @g@ fully
-- polymorphic, as these are the most useful types of 'Flay's.
--
-- We use @'Dict' (c a) ->@ instead of @c a =>@ because the latter is often not
-- enough to satisfy the type checker. With this approach, one must explicitly
-- pattern match on the @'Dict' (c a)@ constructor in order to bring the @c a@
-- instance to scope.  Also, it's necessary that @c@ is explicitly given a type
-- at the 'Flay''s call site, as otherwise the type checker won't be able to
-- infer @c@ on its own.
--
-- /to flay: tr. v., to strip off the skin or surface of./
--
-- /Mnemonic for @c s t f g@: Common STandard FoG./
--
-- ==== Example 1: Removing uncertainty
--
-- Consider the following types and values:
--
-- @
-- data Foo f = Foo (f 'Int') (f 'Bool')
--
-- deriving instance ('Show' (f 'Int'), 'Show' (f 'Bool')) => 'Show' (Foo f)
-- @
--
-- @
-- flayFoo :: ('Applicative' m, c 'Int', c 'Bool') => 'Flay' c (Foo f) (Foo g) f g
-- flayFoo h (Foo a b) = Foo \<$> h 'Dict' a \<*> h 'Dict' b
-- @
--
-- @
-- foo1 :: Foo 'Maybe'
-- foo1 = Foo ('Just' 1) 'Nothing'
-- @
--
-- @
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
-- fooMaybeToIdentity (Foo a b) = Foo \<$> 'fmap' 'pure' a \<*> 'fmap' 'pure' b
-- @
--
-- Example using this in GHCi:
--
-- @
-- > fooMaybeToIdentity foo1
-- 'Nothing'
-- @
--
-- @
-- > fooMaybeToIdentity foo2
-- 'Just' (Foo ('Identity' 2) ('Identity' 'True'))
-- @
--
-- In fact, notice that we are not really working with 'Just', 'Nothing', nor
-- 'Identity' directly, so we might as well just leave 'Maybe' and 'Identity'
-- polymorphic. All we need is that they both are 'Applicative's:
--
-- @
-- fooMToG :: ('Applicative' m, 'Applicative' g) => Foo m -> m (Foo g)
-- fooMToG (Foo a b) = Foo \<$> 'fmap' 'pure' a \<*> 'fmap' 'pure' b
-- @
--
-- @fooMToG@ behaves the same as @fooMaybeToIdentity@, but more importantly, it
-- is much more flexible:
--
-- @
-- > fooMToG foo2 :: 'Maybe' (Foo [])
-- 'Just' (Foo [2] ['True'])
-- @
--
-- @
-- > fooMToG foo2 :: 'Maybe' (Foo ('Either' 'String'))
-- 'Just' (Foo ('Right' 2) ('Right' 'True'))
-- @
--
-- 'Flay', among other things, is intended to generalize this pattern, so that
-- whatever choice of 'Foo', 'Maybe' or 'Identity' you make, you can use
-- 'Applicative' this way. The easiest way to use 'Flay' is through 'trivial'',
-- which is sufficient unless we need to enforce some constraint in the target
-- elements wrapped in @m@ inside foo (we don't need this now). With 'trivial'',
-- we could have defined @fooMToG@ this way:
--
-- @
-- fooMToG :: ('Applicative' m, 'Applicative' g) => Foo m -> m (Foo g)
-- fooMToG = 'trivial'' flayFoo ('fmap' 'pure')
-- @
--
-- Some important things to notice here are that we are reusing 'flayFoo''s
-- knowledge of 'Foo''s structure, and that the construction of @g@ using 'pure'
-- applies to /any/ value wrapped in @m@ ('Int' and 'Bool' in our case). Compare
-- this last fact to 'traverse', where the types of the targets must be the
-- same, and known beforehand.
--
-- Also, notice that we inlined @flayFoo@ for convenience in this example, but
-- we could as well have taken it as an argument, illustrating even more how
-- 'Flay' decouples the shape and targets from their processing:
--
-- @
-- flayMToG :: ('Applicative' m, 'Applicative' g) => 'Flay' 'Trivial' m s t m g -> s -> m s
-- flayMToG fl = 'trivial'' fl ('fmap' 'pure')
-- @
--
-- This is the esscence of 'Flay': We can work operating on the contents of a
-- datatype @s@ targeted by a given 'Flay' /without/ knowing anything about @s@,
-- nor about the @forall x. f x@ targets of the 'Flay'. And we do this using an
-- principled approach relying on 'Applicative' and 'Functor'.
--
-- We can use a 'Flay' to repurpose a datatype while maintaining its "shape".
-- For example, given @Foo@: @Foo 'Identity'@ represents the presence of two
-- values 'Int' and 'Char', @Foo 'Maybe'@ represents their potential absence,
-- @Foo []@ represents the potential for zero or more 'Int's and 'Char's,
-- @Foo ('Const' x)@ represent the presence of two values of type @x@, and @Foo
-- 'IO'@ represents two 'IO' actions necessary to obtain values of type 'Int'
-- and 'Char'. We can use 'flayFoo' to convert between these representations. In
-- all these cases, the shape of @Foo@ is preserved, meaning we can continue to
-- pattern match or project on it. Notice that even though in this example the
-- @f@ argument to @Foo@ happens to always be a 'Functor', this is not necessary
-- at all.
--
-- ==== Example 2: Standalone @m@
--
-- In the previous example, @flayFoo@ took the type @Flay 'Trivial' (Foo m) (Foo
-- g) m g@ when it was used in @flayMToG@. That is, @m@ and @f@ were unified by
-- our use of 'fmap'. However, keeping these different opens interesting
-- possibilities. For example, let's try and convert a @Foo 'Maybe'@ to a @Foo
-- ('Either' 'String')@, prompting the user for the 'Left' side of that 'Either'
-- whenever the original target value is missing.
--
-- @
-- prompt :: 'IO' 'String'
-- prompt = do
--   'putStr' "Missing value! Error message? "
--   'getLine'
-- @
--
-- @
-- fooMaybeToEitherIO :: Foo 'Maybe' -> 'IO' (Foo ('Either' 'String'))
-- fooMaybeToEitherIO = 'trivial'' flayFoo $ \\case
--    'Nothing' -> 'fmap' 'Left' 'prompt'
--    'Just' x -> 'pure' ('Right' x)
-- @
--
-- Using this in GHCi:
--
-- @
-- > fooMaybeToEitherIO foo1
-- Missing value! Error message? /Nooooo!!!!!/
-- Foo ('Right' 1) ('Left' "Nooooo!!!!!")
-- @
--
-- @
-- > fooMaybeToEitherIO foo2
-- Foo ('Right' 2) ('Right' 'True')
-- @
--
-- ==== Example 3: Contexts
--
-- Extending the previous example we "replaced" the missing values with a
-- 'String', but wouldn't it be nice if we could somehow prompt a replacement
-- value of the original type instead? That's what the @c@ argument to 'Flay' is
-- for. Let's replace @prompt@ so that it can construct a type other than
-- 'String':
--
-- @
-- prompt :: 'Read' x => 'IO' x
-- prompt = do
--   'putStr' "Missing value! Replacement? "
--   'readLn'
-- @
--
-- Notice how @prompt@ now has a @'Read' x@ constraint. In order to be able to
-- use the result of @prompt@ as a replacement for our missing values in @Foo
-- 'Maybe'@, we will have to mention 'Read' as the @c@ argument to 'Flay',
-- which implies that 'Read' will have to be a constraint satisfied by all of
-- the targets of our 'Flay' (as seen in the constraints in 'flayFoo'). We can't
-- use 'trivial'' anymore, we need to use 'flayFoo' directly:
--
-- @
-- fooMaybeToIdentityIO :: Foo 'Maybe' -> 'IO' (Foo 'Identity')
-- fooMaybeToIdentityIO = flayFoo h
--   where h :: 'Dict' ('Read' a) -> 'Maybe' a -> 'IO' ('Identity' a)
--         h 'Dict' = \\case
--             'Nothing' -> 'fmap' 'pure' prompt
--             'Just' a -> 'pure' ('pure' a)
-- @
--
-- Notice how we had to give an explicit type to our function @h@: This is
-- because can't infer our @'Read' a@ constraint. You will always need to
-- explicitly type the received @'Dict'@ unless the @c@ argument to 'Flay' has
-- been explicitly by other means (like in the definition of 'trivial'', where
-- we don't have to explicitly type 'Dict' because @c ~ 'Trivial'@ according to
-- the top level signature of 'trivial'').
--
-- Example using this in GHCi:
--
-- @
-- > fooMaybeToIdentityIO foo1
-- Missing value! Replacement? /'True'/
-- Foo ('Identity' 1) ('Identity' 'True')
-- @
--
-- @
-- > fooMaybeToIdentityIO foo2
-- Foo ('Identity' 2) ('Identity' 'True')
-- @
--
-- Of course, as in our previous examples, 'Identity' here could have
-- generalized to any 'Applicative'. We just fixed it to 'Identity' as an
-- example.
--
-- You can mention as many constraints as you need in @c@ as long as @c@ has
-- kind @k -> 'Constraint'@ (where @k@ is the kind of @f@'s argument).  You can
-- always group together many constraints as a single new one in order to
-- achieve this. For example, if you want to require both 'Show' and 'Read' on
-- your target types, then you can introduce the following @ShowAndRead@ class,
-- and use that as your @c@.
--
-- @
-- class ('Show' a, 'Read' a) => ShowAndRead a
-- instance ('Show' a, 'Read' a) => ShowAndRead a
-- @
--
-- This is such a common scenario that the "Flay" module exports 'All', a
-- 'Constraint' you can use to apply many 'Constraint's at once. For example,
-- instead of introducing @ShowAndRead@, we could use @'All' '['Show', 'Read']@
-- as our @c@ argument to 'Flay', and the net result would be the same.
--
-- ==== Example 4: 'collect''
--
-- See the documentation for 'collect''. To sum up: for any given 'Flay', we can
-- collect all of the 'Flay''s targets into a 'Monoid', without knowing anything
-- about the targets themselves beyond the fact that they satisfy a particular
-- constraint.
--
type Flay (c :: k -> Constraint) s t (f :: k -> *) (g :: k -> *)
  = forall m. Applicative m
       => (forall (a :: k). Dict (c a) -> f a -> m (g a)) -> s -> m t

-- | Inner identity law:
--
-- @
-- (\\fl -> 'runIdentity' . 'trivial'' fl 'pure') = 'id'
-- @
inner :: Flay Trivial s s f f -> s -> s
inner fl = runIdentity . trivial' fl pure

--------------------------------------------------------------------------------

-- | Default 'Flay' implementation for @s@ and @t@.
--
-- When defining 'Flayable' instances, you should leave @c@, @f@, and @g@
-- fully polymomrphic, as these are the most useful types of 'Flayables's.
class Flayable (c :: k -> Constraint) s t (f :: k -> *) (g :: k -> *) | s -> f, t -> g, s g -> t, t f -> s where
  -- | If @s@ and @t@ are instances of 'G.Generic', then 'gflay' can be used as
  -- default implementation for 'flay'. For example, provided the @Foo@ datatype
  -- shown in the documentation for 'Flay' had a 'G.Generic' instance, then the
  -- following 'Flayable' instance would get a default implementation for
  -- 'flay':
  --
  -- @
  -- instance (c 'Int', c 'Bool') => 'Flayable' c (Foo f) (Foo g) f g where
  --   'flay' = 'gflay'
  -- @
  --
  -- Notice that 'flay' can be defined in terms of 'flay1' as well.
  --
  -- /Implementors note:/ Unfortunately, due to some strange bug in GHC, we
  -- can't use @DefaultSignatures@ to say @'flay' = 'gflay'@, because when doing
  -- that the kind of @c@ infers incorrectly.
  flay :: Flay c s t f g

--------------------------------------------------------------------------------

-- | 'Flayable1' is 'Flayable' specialized for the common case of @s ~ r f@ and
-- @t ~ r g@. The rationale for introducing this seemingly redundant class is
-- that the 'Flayable1' constraint is less verbose than 'Flayable'.
--
-- Unfortunately, we can't readily existentialize the arguments to 'Flayable',
-- which is why you'll need to specify both 'Flayable1' and 'Flayable'
-- instances. Notice, however, that 'flay1' can be defined in terms of
-- 'flay' and vice-versa, so this should be very mechanical.
class Flayable1 (c :: k -> Constraint) (r :: (k -> *) -> *) where
  -- | If @r f@ and @r g@ are instances of 'G.Generic', then 'flay1' gets a
  -- default implementation. For example, provided the @Foo@ datatype shown in
  -- the documentation for 'Flay' had a 'G.Generic' instance, then the following
  -- 'Flayable' instance would get a default implementation for 'flay1':
  --
  -- @
  -- instance (c 'Int', c 'Bool') => 'Flayable1' c Foo
  -- @
  --
  -- Notice that 'flay1' can be defined in terms of 'flay' as well.
  flay1 :: Flay c (r f) (r g) f g
  default flay1 :: GFlay c (r f) (r g) f g => Flay c (r f) (r g) f g
  flay1 = gflay
  {-# INLINE flay1 #-}

--------------------------------------------------------------------------------

-- | 'Constraint' trivially satisfied by every type.
--
-- This can be used as the @c@ parameter to 'Flay' or 'Flayable' in case you are
-- not interested in observing the values inside @f@.
class Trivial (a :: k)
instance Trivial (a :: k)

-- | Given a 'Flay' for any constraint @c@ obtain a 'Flay' for a 'Trivial'
-- constraint.
trivialize :: forall c s t f g. Flay c s t f g -> Flay Trivial s t f g
{-# INLINE trivialize #-}
trivialize fl0 = \h s ->
  fl0 (\(Dict :: Dict (c a)) (fa :: f a) -> h (Dict :: Dict (Trivial a)) fa) s

-- | You can use 'trivial'' if you don't care about the @c@ argument to 'Flay'.
-- This implies that you won't be able to observe the @a@ in @forall a. f a@,
-- all you can do with such @a@ is pass it around.
--
-- @
-- 'trivial'' fl h
--    = fl (\\('Dict' :: 'Dict' ('Trivial' a)) (fa :: f a) -> h fa)
-- @
trivial'
  :: forall m c s t f g
  .  Applicative m
  => Flay c s t f g
  -> (forall a. Trivial a => f a -> m (g a))
  -> s
  -> m t  -- ^
trivial' fl = \h -> \s -> trivialize fl (\Dict fa -> h fa) s
{-# INLINE trivial' #-}

-- | Like 'trivial'', but works on a 'Flayable' instead of taking an explicit
-- 'Flay'.
--
-- @
-- 'trivial' = 'trivial'' 'flay'
-- @
trivial
  :: forall m s t f g
  .  (Applicative m, Flayable Trivial s t f g)
  => (forall a. Trivial a => f a -> m (g a))
  -> s
  -> m t  -- ^
trivial = trivial' (flay :: Flay Trivial s t f g)
{-# INLINE trivial #-}

-- | Like 'trivial'', but works on a 'Flayable1' instead of taking an explicit
-- 'Flay'.
--
-- @
-- 'trivial' = 'trivial'' 'flay1'
-- @
trivial1
  :: forall m f g r
  .  (Applicative m, Flayable1 Trivial r)
  => (forall a. Trivial a => f a -> m (g a))
  -> (r f)
  -> m (r g)  -- ^
trivial1 = trivial' (flay1 :: Flay Trivial (r f) (r g) f g)
{-# INLINE trivial1 #-}

--------------------------------------------------------------------------------

-- | Convenience 'Constraint' for satisfying basic 'GFlay'' needs for @s@ and @t@.
class (G.Generic s, G.Generic t, GFlay' c (G.Rep s) (G.Rep t) f g)
  => GFlay (c :: k -> Constraint) s t (f :: k -> *) (g :: k -> *)
instance (G.Generic s, G.Generic t, GFlay' c (G.Rep s) (G.Rep t) f g)
  => GFlay (c :: k -> Constraint) s t (f :: k -> *) (g :: k -> *)

gflay :: GFlay c s t f g => Flay (c :: k -> Constraint) s t (f :: k -> *) (g :: k -> *)
gflay = \h s -> G.to <$> gflay' h (G.from s)
{-# INLINE gflay #-}

class GFlay' (c :: k -> Constraint) s t (f :: k -> *) (g :: k -> *) where
  gflay' :: Flay c (s p) (t p) f g

instance GFlay' c G.V1 G.V1 f g where
  gflay' _ _ = undefined -- unreachable
  {-# INLINE gflay' #-}

instance GFlay' c G.U1 G.U1 f g where
  gflay' _ _ = undefined -- unreachable
  {-# INLINE gflay' #-}

instance c a => GFlay' c (G.K1 r (f a)) (G.K1 r (g a)) f g where
  gflay' h (G.K1 fa) = G.K1 <$> h Dict fa
  {-# INLINE gflay' #-}

instance (GFlay' c s t f g)
  => GFlay' c (G.M1 i j s) (G.M1 i j t) f g where
  gflay' h (G.M1 sp) = G.M1 <$> gflay' h sp
  {-# INLINE gflay' #-}

instance (GFlay' c sl tl f g, GFlay' c sr tr f g)
  => GFlay' c (sl G.:*: sr) (tl G.:*: tr) f g where
  gflay' h (slp G.:*: srp) = (G.:*:) <$> gflay' h slp <*> gflay' h srp
  {-# INLINE gflay' #-}

instance (GFlay' c sl tl f g, GFlay' c sr tr f g)
  => GFlay' c (sl G.:+: sr) (tl G.:+: tr) f g where
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
  => Flay c s t f (Const ())
  -> (forall a. Dict (c a) -> f a -> b)
  -> s
  -> b    -- ^
collect' fl = \k -> \s -> getConst (fl (\d fa -> Const (k d fa)) s)
{-# INLINE collect' #-}

-- | Like 'collect'', but works on a 'Flayable' instead of an explicit 'Flay'.
collect
  :: (Monoid b, Flayable c s t f (Const ()))
  => (forall a. Dict (c a) -> f a -> b)
  -> s
  -> b    -- ^
collect = collect' flay
{-# INLINE collect #-}

-- | Like 'collect'', but works on a 'Flayable1' instead of an explicit 'Flay'.
collect1
  :: (Monoid b, Flayable1 c r)
  => (forall a. Dict (c a) -> f a -> b)
  -> r f
  -> b    -- ^
collect1 = collect' flay1
{-# INLINE collect1 #-}

--------------------------------------------------------------------------------

-- | Witness that @a@ is a terminal object. That is, that @a@ can always be
-- constructed out of thin air.
class Terminal a where
  terminal :: a

instance Terminal () where
  terminal = ()
  {-# INLINE terminal #-}

instance {-# OVERLAPPABLE #-} (G.Generic a, GTerminal (G.Rep a)) => Terminal a where
  terminal = G.to gterminal
  {-# INLINE terminal #-}

instance Terminal (Const () a) where
  terminal = Const ()
  {-# INLINE terminal #-}

---
class GTerminal (f :: * -> *) where
  gterminal :: f p

instance GTerminal G.U1 where
  gterminal = G.U1
  {-# INLINE gterminal #-}

instance Terminal x => GTerminal (G.K1 i x) where
  gterminal = G.K1 terminal
  {-# INLINE gterminal #-}

instance GTerminal f => GTerminal (G.M1 i c f) where
  gterminal = G.M1 gterminal
  {-# INLINE gterminal #-}

instance (GTerminal l, GTerminal r) => GTerminal (l G.:*: r) where
  gterminal = gterminal G.:*: gterminal
  {-# INLINE gterminal #-}

--------------------------------------------------------------------------------

-- | Zip two 'Flayable1's together.
--
-- Example pairing two of the 'Foo' values seen elsewhere in this file.
--
-- @
-- > let foo1 = 'Foo' ('Data.Functor.Identity.Identity' 0) ('Data.Functor.Identity.Identity' 'False')
-- >   :: 'Foo' 'Data.Functor.Identity.Identity'
--
-- > let foo2 = 'Foo' ('Just' 1) 'Nothing'
-- >   :: 'Foo' 'Maybe'
--
-- > 'zip1' (\('Dict' :: 'Dict' ('Trivial' x)) a b -> 'Data.Functor.Product.Pair' a b) foo1 foo2
-- >   :: 'Foo' ('Data.Functor.Product.Product' 'Data.Functor.Identity.Identity' 'Maybe')
-- 'Foo' ('Data.Functor.Product.Pair' ('Data.Functor.Identity.Identity' 0) ('Just' 1)) ('Data.Functor.Product.Pair' ('Data.Functor.Identity.Identity' 'False') 'Nothing')
--
-- > 'zip1' (\('Dict' :: 'Dict' ('Show' x)) ('Data.Functor.Identity.Identity' a) yb -> case yb of
-- >           'Nothing' -> 'Const' ('show' a)
-- >           'Just' b  -> 'Const' ('show' (a, b)) )
-- >      foo1 foo2
-- >   :: Foo ('Const' 'String')
-- Foo ('Const' \"(0,1)\") ('Const' \"False\")
-- @
--
-- Returns 'Nothing' in case the indivual target types do not match.
--
-- Note: 'zip1' is safer but less general than 'unsafeZip'.
zip1
  :: (Monad m, Typeable f, Flayable1 c s, Flayable1 Typeable s)
  => (forall x. Dict (c x) -> f x -> g x -> m (h x))
  -> s f
  -> s g
  -> m (Maybe (s h))  -- ^
zip1 h = unsafeZip flay1 flay1 flay1 h
{-# INLINABLE zip1 #-}

-- | Zip two 'Flayable's together.
--
-- 'zip' is like 'zip1', but for 'Flayable's.
--
-- Returns 'Nothing' in case the indivual target types do not match.
--
-- Note: 'zip' is safer but less general than 'unsafeZip'.
zip
  :: ( Monad m, Typeable f
     , Flayable Typeable s1 t1 f (Const ())
     , Flayable Typeable s2 t2 g (Product f g)
     , Flayable c t2 t3 (Product f g) h )
  => (forall x. Dict (c x) -> f x -> g x -> m (h x))
  -> s1
  -> s2
  -> m (Maybe t3)   -- ^
zip h = unsafeZip flay flay flay h
{-# INLINABLE zip #-}

-- | Unsafe version of 'zip' that doesn't guarantee that the given 'Flay's
-- target the same values. 'zip' and 'zip1' make this function safe by simply
-- using 'flay' or 'flay1' three times.
--
-- Returns 'Nothing' in case the indivual target types do not match.

-- This implementation traverses the record three times. We could make it in
-- two, but that pollutes the constraints a bit.
unsafeZip
  :: forall c s1 s2 t1 t2 t3 f g h m
  .  (Monad m, Typeable f)
  => (Flay Typeable s1 t1 f (Const ()))
  -> (Flay Typeable s2 t2 g (Product f g))
  -> (Flay c t2 t3 (Product f g) h)
  -> (forall x. Dict (c x) -> f x -> g x -> m (h x))
  -> s1
  -> s2
  -> m (Maybe t3)  -- ^
unsafeZip fl1 fl2 fl3 pair = \s1 s2 -> runMaybeT $ do
   (t2, dyns) <- runStateT (fl2 f2 s2) (collect' fl1 f1 s1)
   case dyns of
     [] -> lift (fl3 f3 t2)
     _  -> MaybeT (pure Nothing)
 where
   f1 :: Dict (Typeable a) -> f a -> [Dynamic]
   f1 = \Dict !fa -> [toDyn fa :: Dynamic]
   f2 :: Dict (Typeable a) -> g a -> StateT [Dynamic] (MaybeT m) (Product f g a)
   f2 = \Dict !ga -> StateT $ \(x:xs) -> do
      !(fa :: f a) <- MaybeT (pure (fromDynamic x))
      pure (Pair fa ga, xs)
   f3 :: Dict (c a) -> Product f g a -> m (h a)
   f3 = \Dict (Pair fa ga) -> pair Dict fa ga


--------------------------------------------------------------------------------

-- | Wrapper allowing a 'G.Generic' non 'Flayable' type to become 'Flayable'.
--
-- Most datatypes that can have useful 'Flayable' instances are often
-- parametrized by a type constructor @f :: k -> *@, and have all or some of
-- their fields wrapped in said @f@, like so:
--
-- @
-- data Foo f = Foo (f 'Int') (f 'Bool')
-- @
--
-- However, that kind of representation is not that common, and it can sometimes
-- be unconfortable to use, particularly if @f ~ 'Identity'@ due to the
-- necessary wrapping and unwrapping of values. In Haskell, it's more common to
-- use a representation like the following for records (or sums):
--
-- @
-- data Bar = Bar 'Int' 'Bool'
--   deriving ('G.Generic')
-- @
--
-- The problem with that representation, however, is that it prevents us to
-- operate on the individual fields as enabled by 'Flay'.
--
-- 'Pump' is a wrapper that converts types like 'Bar' into types like 'Foo'. In
-- our concrete case, @'Pump' 'Bar' f@ is isomorphic to @'Foo' f@. But more
-- importantly, @'Pump' 'Bar' f@ automatically gets a 'Flayable' instance of its
-- own, allowing you to use 'flay' to operate on @'Pump' 'Bar' f@ as you would
-- operate on @'Foo' f@.
--
-- To construct a 'Pump' you use 'pump', and to remove the 'Pump' wrapper you
-- use 'dump', which satisfy the following identity law:
--
-- @
-- 'dump' 'id' . 'pump' 'pure'  ==  'pure'
-- @
--
-- 'Pump' relies on Haskell's 'G.Generic's, which is why we derived
-- 'G.Generic' for our @Bar@ above. If @Bar@ didn't have a 'G.Generic' instance,
-- then you wouldn't be able to use 'Pump' and would be better served by a
-- manually written functions converting @Bar@ to @Foo@ and back.
--
-- Keep in mind that @'Pump' s f@ will only add @f@ wrappers to the immediate
-- children fields of @s@ (which could itself be a sum type or a product type),
-- but it won't recurse into the fields and add @f@ wrappers to them.
--
-- Very contrived and verbose example using all of 'pump', 'dump' and 'flay':
--
-- @
-- -- | Replaces all of the fields of the given Bar with values 'Read' from
-- -- 'System.IO.stdin', if possible.
-- qux :: Bar -> 'IO' ('Either' 'String' 'Bar')
-- qux bar0 = do
--    let pbar0 :: 'Pump' Bar 'Identity'
--        pbar0 = 'pump' 'Identity' bar0
--    let h :: 'Dict' ('Read' a) -> 'Identity' a -> 'IO' ('Maybe' a)
--        h 'Dict' ('Identity' _) = 'fmap' 'Text.readMaybe' 'getLine'
--    pbar1 :: 'Pump' Bar 'Maybe' <- 'flay' h pbar0
--    -- We convert the 'Maybe's to 'Either' just for demonstration purposes.
--    -- Using 'dump' 'id' would have been enough to make this function
--    -- return a 'Maybe' Bar.
--    let ebar1 :: 'Either' 'String' 'Bar'
--        ebar1 = 'dump' ('maybe' ('Left' \"Bad") 'Right') pbar1
--    pure ebar1
-- @
--
-- Or, written in a less verbose manner:
--
-- @
-- qux :: Bar -> 'IO' ('Either' 'String' 'Bar')
-- qux bar = 'fmap' ('dump' ('maybe' ('Left' \"Bad") 'Right'))
--                ('flay' \@'Read'
--                      (\('Dict' ('Identity' _) -> 'fmap' 'Text.readMaybe' 'getLine')
--                      ('pump' 'Identity' bar)
-- @
--
-- We can use @qux@ in GHCi as follows:
--
-- @
-- > qux (Bar 0 False)
-- /not a number/
-- /not a bool/
-- __Left \"Bad"__
--
-- > qux (Bar 0 False)
-- /1/
-- /True/
-- __Right (Bar 1 True)__
-- @
data Pump s f = forall p. Pump !(GPumped (G.Rep s) f p)

instance
  (GFlay' c (GPumped (G.Rep s) f) (GPumped (G.Rep s) g) f g)
  => Flayable c (Pump s f) (Pump s g) f g where
  flay h (Pump rep) = Pump <$> gflay' h rep
  {-# INLINE flay #-}

-- | Wrap @s@ in 'Pump' so that it can be 'flay'ed.
--
-- See the documentation for 'Pump' for more details.
pump
  :: GPump s f
  => (forall x. x -> f x)
  -- ^ How to wrap in @f@ each individual child field of @s@.
  -> s
  -> Pump s f  -- ^
pump f = \s -> Pump (gpump f (G.from s))
{-# INLINE pump #-}

-- | Remove the 'Pump' wraper around @s@.
--
-- See the documentation for 'Pump' for more details.
dump
  :: (GPump s f, Applicative m)
  => (forall a. f a -> m a)
  -- ^ How to remove the @f@ wrapper from every child field of @'Pump' s f@.
  -> Pump s f
  -> m s  -- ^
dump f = \(Pump rep) -> G.to <$> gdump f rep
{-# INLINE dump #-}

-- | This class is used to support 'pump' and 'dump' internally. We only
-- export its name so that you can use it in constraints if necessary.
class (G.Generic s, GPump' (G.Rep s) f) => GPump s f
instance (G.Generic s, GPump' (G.Rep s) f) => GPump s f

class GPump' (s :: k -> *) (f :: * -> *) where
  type GPumped s f :: k -> *
  gpump :: (forall a. a -> f a) -> s p -> GPumped s f p
  gdump :: Applicative m => (forall a. f a -> m a) -> GPumped s f p -> m (s p)

instance GPump' G.V1 f where
  type GPumped G.V1 f = G.V1
  gpump _ _ = undefined -- unreachable
  gdump _ _ = undefined -- unreachable

instance GPump' G.U1 f where
  type GPumped G.U1 f = G.U1
  gpump _ G.U1 = G.U1
  {-# INLINE gpump #-}
  gdump _ G.U1 = pure G.U1
  {-# INLINE gdump #-}

instance GPump' (G.K1 i c) f where
  type GPumped (G.K1 i c) f = G.K1 i (f c)
  gpump f (G.K1 c) = G.K1 (f c)
  {-# INLINE gpump #-}
  gdump f (G.K1 c) = G.K1 <$> f c
  {-# INLINE gdump #-}

instance GPump' s f => GPump' (G.M1 i j s) f where
  type GPumped (G.M1 i j s) f = G.M1 i j (GPumped s f)
  gpump f (G.M1 sp) = G.M1 (gpump f sp)
  {-# INLINE gpump #-}
  gdump f (G.M1 sp) = G.M1 <$> gdump f sp
  {-# INLINE gdump #-}

instance (GPump' sl f, GPump' sr f) => GPump' (sl G.:*: sr) f where
  type GPumped (sl G.:*: sr) f = GPumped sl f G.:*: GPumped sr f
  gpump f (slp G.:*: srp) = gpump f slp G.:*: gpump f srp
  {-# INLINE gpump #-}
  gdump f (slp G.:*: srp) = (G.:*:) <$> gdump f slp <*> gdump f srp
  {-# INLINE gdump #-}

instance (GPump' sl f, GPump' sr f) => GPump' (sl G.:+: sr) f where
  type GPumped (sl G.:+: sr) f = GPumped sl f G.:+: GPumped sr f
  gpump f (G.L1 slp) = G.L1 (gpump f slp)
  gpump f (G.R1 srp) = G.R1 (gpump f srp)
  {-# INLINE gpump #-}
  gdump f (G.L1 slp) = G.L1 <$> gdump f slp
  gdump f (G.R1 srp) = G.R1 <$> gdump f srp
  {-# INLINE gdump #-}

--------------------------------------------------------------------------------

-- | Ensure that @x@ satisfies all of the constraints listed in @cs@.

-- Implementation notice. @All@ and @All'@ have the same semantics, the only
-- difference is that @All@ can be partially applied, whereas @All'@ can't.
-- Thus, we only export @All@
class All' cs x => All (cs :: [k -> Constraint]) (x :: k)
instance All' cs x => All cs x
type family All' (cs :: [k -> Constraint]) (x :: k) :: Constraint where
  All' (c ': cs) x = (c x, All' cs x)
  All' '[] _ = ()

