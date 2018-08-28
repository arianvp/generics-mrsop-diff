{ pkgs ? import <nixpkgs> {}}:
let generics-mrsop-diff = import ./. {};
in
  generics-mrsop-diff.env.overrideAttrs (pkg : {
    nativeBuildInputs = pkg.nativeBuildInputs ++ [
      pkgs.haskellPackages.ghcid
      pkgs.cabal-install
    ];
  })
  
