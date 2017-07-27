{ nixpkgsBootstrap ? <nixpkgs>
, nixpkgs ? (import nixpkgsBootstrap {}).fetchFromGitHub {
    owner = "NixOS";
    repo = "nixpkgs";
    rev = "8dfa4721789d10fa5387c8bddf7f1725eac0c575";
    sha256 = "0cygb2nv4xqa9dkwscvapf58qg6ibaw6ypy8srafsg0aamwxsvsh"; }
}:

let
pkgs = import nixpkgs {};

hsPackageSetConfig = self: super: {
  flay = self.callPackage (import ./pkg.nix) {};
};

ghc802 = pkgs.haskell.packages.ghc802.override {
  packageSetConfig = hsPackageSetConfig;
};

ghc821 = pkgs.haskell.packages.ghc821.override {
  packageSetConfig = hsPackageSetConfig;
};

in {
  flay-ghc802 = ghc802.flay;
  flay-ghc821 = ghc821.flay;
}
