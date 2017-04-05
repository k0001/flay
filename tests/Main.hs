{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE UndecidableInstances #-}

module Main where

import Control.Monad (join)
import Data.Functor.Const (Const(Const))
import Data.Functor.Identity (Identity(Identity), runIdentity)
import GHC.Generics (Generic)
import qualified Test.Tasty as Tasty
import qualified Test.Tasty.Runners as Tasty
import Test.Tasty.QuickCheck ((===))
import qualified Test.Tasty.QuickCheck as QC

import Data.Functor.Flay

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

main :: IO ()
main = Tasty.defaultMainWithIngredients
  [ Tasty.consoleTestReporter
  , Tasty.listingTests
  ] tt

tt :: Tasty.TestTree
tt = Tasty.testGroup "main"
  [ QC.testProperty "Flayable: identity law 1" $
      QC.forAll QC.arbitrary $ \(foo :: Foo Maybe) ->
         foo === runIdentity (trivial pure foo)
  , QC.testProperty "Flayable: identity law 2" $
      QC.forAll QC.arbitrary $ \(ia :: Identity Int) ->
         ia === join (trivial pure ia)
  , QC.testProperty "collectShow: flayFoo" $
      QC.forAll QC.arbitrary $ \foo@(Foo (Identity a) (Identity b)) ->
         [show a, show b] === collectShow' flayFoo foo
  , QC.testProperty "collectShow: flay" $
      QC.forAll QC.arbitrary $ \foo@(Foo (Identity a) (Identity b)) ->
         [show a, show b] === collectShow' flay foo
  ]


collectShow'
  :: Flay Show (Const [String]) s t Identity (Const ()) -> s -> [String]
collectShow' fl = collect' fl (\Dict (Identity a) -> [show a])
