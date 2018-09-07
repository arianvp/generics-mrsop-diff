{ pkgs ? import ./nixpkgs.nix {}
, generics-mrsop ? import ../generics-mrsop  {inherit pkgs;} 
}:
let
  generics-mrsop = pkgs.haskell.lib.dontHaddock (pkgs.haskellPackages.callPackage ./generics-mrsop.nix {});
  hyper = pkgs.haskell.lib.doJailbreak pkgs.haskellPackages.hyper;
  hs-digems = pkgs.haskellPackages.callPackage ./hs-digems.nix { inherit generics-mrsop; };
in
  { generics-mrsop-diff = pkgs.haskellPackages.callPackage ./generics-mrsop-diff.nix { inherit generics-mrsop hyper hs-digems;};
    inherit generics-mrsop;
  }
  
