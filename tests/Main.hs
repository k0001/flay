{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE UndecidableInstances #-}

module Main where

import Control.Monad (join)
import Data.Functor.Const (Const(Const))
import Data.Functor.Identity (Identity(Identity), runIdentity)
import GHC.Generics (Generic)
import qualified GHC.Generics as G
import qualified Test.Tasty as Tasty
import qualified Test.Tasty.Runners as Tasty
import Test.Tasty.QuickCheck ((===))
import qualified Test.Tasty.QuickCheck as QC

import Flay

--------------------------------------------------------------------------------

data Foo f = Foo (f Int) (f Bool)
  deriving (Generic)

flayFoo :: (Applicative m, c Int, c Bool) => Flay c m (Foo f) (Foo g) f g
flayFoo h (Foo a b) = Foo <$> h Dict a <*> h Dict b

instance (Applicative m, c Int, c Bool) => Flayable c m (Foo f) (Foo g) f g

deriving instance (Eq (f Int), Eq (f Bool)) => Eq (Foo f)
deriving instance (Show (f Int), Show (f Bool)) => Show (Foo f)

instance (QC.Arbitrary (f Int), QC.Arbitrary (f Bool)) => QC.Arbitrary (Foo f) where
  arbitrary = Foo <$> QC.arbitrary <*> QC.arbitrary

--------------------------------------------------------------------------------

data Bar f = Bar (f Int) Int
  deriving (Generic)

flayBar :: (Applicative m, c Int) => Flay c m (Bar f) (Bar g) f g
flayBar h (Bar a b) = Bar <$> h Dict a <*> pure b

instance (Applicative m, c Int, c Bool) => Flayable c m (Bar f) (Bar g) f g

deriving instance Eq (f Int) => Eq (Bar f)
deriving instance Show (f Int) => Show (Bar f)

instance QC.Arbitrary (f Int) => QC.Arbitrary (Bar f) where
  arbitrary = Bar <$> QC.arbitrary <*> QC.arbitrary

--------------------------------------------------------------------------------

data Qux f
  = Qux1 (f Int) Int
  | Qux2 { q2a :: (f Int), q2b :: (f Int) }
  | Qux3 (Foo f)
  deriving (Generic)

flayQux :: (Applicative m, c Int, c Bool) => Flay c m (Qux f) (Qux g) f g
flayQux h (Qux1 a b) = Qux1 <$> h Dict a <*> pure b
flayQux h (Qux2 a b) = Qux2 <$> h Dict a <*> h Dict b
flayQux h (Qux3 a) = Qux3 <$> flayFoo h a

-- TODO: See if there is a way of removing all these constraints.
instance
  ( GFlay' c m (G.K1 G.R (Foo f)) (G.K1 G.R (Foo g)) f g
  , Applicative m
  , c Int
  , c Bool
  ) => Flayable c m (Qux f) (Qux g) f g

deriving instance (Eq (f Int), Eq (Foo f)) => Eq (Qux f)
deriving instance (Show (f Int), Show (Foo f)) => Show (Qux f)

instance (QC.Arbitrary (f Int), QC.Arbitrary (Foo f)) => QC.Arbitrary (Qux f) where
  arbitrary = QC.oneof [ Qux1 <$> QC.arbitrary <*> QC.arbitrary
                       , Qux2 <$> QC.arbitrary <*> QC.arbitrary
                       , Qux3 <$> QC.arbitrary ]

--------------------------------------------------------------------------------

main :: IO ()
main = Tasty.defaultMainWithIngredients
  [ Tasty.consoleTestReporter
  , Tasty.listingTests
  ] tt

tt :: Tasty.TestTree
tt = Tasty.testGroup "main"
  [ QC.testProperty "Flayable: Foo: identity law 1" $
      QC.forAll QC.arbitrary $ \(foo :: Foo Maybe) ->
         foo === runIdentity (trivial pure foo)
  , QC.testProperty "Flayable: Bar: identity law 1" $
      QC.forAll QC.arbitrary $ \(bar :: Bar Maybe) ->
         bar === runIdentity (trivial pure bar)
  , QC.testProperty "Flayable: Qux: identity law 1" $
      QC.forAll QC.arbitrary $ \(qux :: Qux Maybe) ->
         qux === runIdentity (trivial pure qux)
  , QC.testProperty "Flayable: identity law 2" $
      QC.forAll QC.arbitrary $ \(ia :: Identity Int) ->
         ia === join (trivial pure ia)
  , QC.testProperty "collectShow: Foo: flayFoo" $
      QC.forAll QC.arbitrary $ \foo@(Foo (Identity a) (Identity b)) ->
         [show a, show b] === collectShow' flayFoo foo
  , QC.testProperty "collectShow: Foo: flay" $
      QC.forAll QC.arbitrary $ \foo@(Foo (Identity a) (Identity b)) ->
         [show a, show b] === collectShow' flay foo
  , QC.testProperty "collectShow: Bar: flayBar" $
      QC.forAll QC.arbitrary $ \bar@(Bar (Identity a) _) ->
         [show a] === collectShow' flayBar bar
  , QC.testProperty "collectShow: Bar: flay" $
      QC.forAll QC.arbitrary $ \bar@(Bar (Identity a) _) ->
         [show a] === collectShow' flay bar
  ]


collectShow'
  :: Flay Show (Const [String]) s t Identity (Const ()) -> s -> [String]
collectShow' fl = collect' fl (\Dict (Identity a) -> [show a])
