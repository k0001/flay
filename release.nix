{ nixpkgsBootstrap ? <nixpkgs>
, nixpkgs ? (import nixpkgsBootstrap {}).fetchFromGitHub {
    owner = "NixOS";
    repo = "nixpkgs-channels";
    rev = "3eccd0b11d176489d69c778f2fcb544438f3ab56"; # unstable, dec 4 2017
    sha256 = "1i3p5m0pnn86lzni5y1win0sacckw3wlg9kqaw15nszhykgz22zq"; }
}:

let
pkgs = import nixpkgs {};

hsPackageSetConfig = self: super: {
  flay = self.callPackage (import ./pkg.nix) {};
};

x = {
  ghc802 = pkgs.haskell.packages.ghc802.override { packageSetConfig = hsPackageSetConfig; };
  ghc822 = pkgs.haskell.packages.ghc822.override { packageSetConfig = hsPackageSetConfig; };
};

in rec {
  ghc802 = { inherit (x.ghc802) flay; };
  ghc822 = { inherit (x.ghc822) flay; };

  everything = pkgs.releaseTools.aggregate {
    name = "everything";
    meta.description = "Every job in release.nix";
    constituents = [ ghc802.flay ghc822.flay ];
  };
}
