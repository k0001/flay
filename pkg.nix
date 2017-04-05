{ mkDerivation, base, constraints, stdenv, tasty, tasty-quickcheck
}:
mkDerivation {
  pname = "flay";
  version = "0.1";
  src = ./.;
  libraryHaskellDepends = [ base constraints ];
  testHaskellDepends = [ base tasty tasty-quickcheck ];
  homepage = "https://github.com/k0001/flay";
  description = "Work on your datatype without knowing much about it";
  license = stdenv.lib.licenses.bsd3;
}
