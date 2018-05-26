{ mkDerivation, base, constraints, stdenv, tasty, tasty-quickcheck
, transformers
}:
mkDerivation {
  pname = "flay";
  version = "0.4";
  src = ./.;
  libraryHaskellDepends = [ base constraints transformers ];
  testHaskellDepends = [ base tasty tasty-quickcheck transformers ];
  homepage = "https://github.com/k0001/flay";
  description = "Work generically on your datatype without knowing its shape nor its contents";
  license = stdenv.lib.licenses.bsd3;
}
