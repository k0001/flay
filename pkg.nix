{ mkDerivation, base, constraints, stdenv, tasty, tasty-quickcheck, transformers
}:
mkDerivation {
  pname = "flay";
  version = "0.3";
  src = ./.;
  libraryHaskellDepends = [ base constraints transformers ];
  testHaskellDepends = [ base tasty tasty-quickcheck ];
  homepage = "https://github.com/k0001/flay";
  description = "Work on your datatype without knowing its shape nor its contents";
  license = stdenv.lib.licenses.bsd3;
}
