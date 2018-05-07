{ nixpkgs ? builtins.fetchTarball channel:nixos-18.03
}:

let
pkgs = import nixpkgs {};
ghc841 = pkgs.haskell.packages.ghc841.override {
  packageSetConfig = self: super: {
    flay = super.callPackage ./pkg.nix {};
  };
};

in { inherit (ghc841) flay; }
