{ pkgs ? import <nixpkgs> {}
, generics-mrsop ? import ../generics-mrsop  {inherit pkgs;} 
}:
pkgs.haskellPackages.callPackage ./generics-mrsop-diff.nix { inherit generics-mrsop; }
