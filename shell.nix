{ ghc-ver ? "821" }:
(import ./default.nix { inherit ghc-ver; }).env
