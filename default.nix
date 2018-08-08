{ pkgs ? import ./nixpkgs.nix {}
, generics-mrsop ? import ../generics-mrsop  {inherit pkgs;} 
}:
pkgs.haskellPackages.callPackage ./generics-mrsop-diff.nix {
    generics-mrsop = pkgs.haskell.lib.dontHaddock generics-mrsop;
    hyper = pkgs.haskell.lib.doJailbreak pkgs.haskellPackages.hyper;
}
