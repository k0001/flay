{ compiler ? "ghc822" }:
(import ./release.nix {}).${compiler}.flay.env
