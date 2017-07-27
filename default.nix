{ ghc-ver ? "821" }:
(import ./release.nix {}).${"flay-ghc" + ghc-ver}
