{ nixpkgsBootstrap ? <nixpkgs>
, nixpkgs ? (import nixpkgsBootstrap {}).fetchFromGitHub {
    owner = "NixOS";
    repo = "nixpkgs";
    rev = "100919ab5b69cbbb26886421aacc692467c7fec4"; # release-17.03
    sha256 = "1nqiphqvxzszi0r4qq8w39x0g08wc7vaa9mfl7gi4a28bkv99781"; }
}:

let

pkgs = import nixpkgs {};

hsPackageSetConfig = self: super: {
  flay = self.callPackage (import ./pkg.nix) {};
};

ghc802 = pkgs.haskell.packages.ghc802.override {
  packageSetConfig = hsPackageSetConfig;
};

in { inherit (ghc802) flay; }
