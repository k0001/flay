{ mkDerivation, base, constraints, ghc-prim, stdenv, tasty, tasty-quickcheck
}:
mkDerivation {
  pname = "flay";
  version = "0.2";
  src = ./.;
  libraryHaskellDepends = [ base constraints ghc-prim ];
  testHaskellDepends = [ base tasty tasty-quickcheck ];
  homepage = "https://github.com/k0001/flay";
  description = "Work on your datatype without knowing its shape nor its contents";
  license = stdenv.lib.licenses.bsd3;
}
