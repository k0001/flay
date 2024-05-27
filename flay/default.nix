{ mkDerivation, base, constraints, lib, tasty, tasty-quickcheck
, transformers
}:
mkDerivation {
  pname = "flay";
  version = "0.5";
  src = ./.;
  libraryHaskellDepends = [ base constraints transformers ];
  testHaskellDepends = [ base tasty tasty-quickcheck transformers ];
  homepage = "https://github.com/k0001/flay";
  description = "Generic programming for higher-kinded types";
  license = lib.licenses.bsd3;
}
