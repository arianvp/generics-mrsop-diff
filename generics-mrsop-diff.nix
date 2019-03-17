{ mkDerivation, base, Cabal, filepath, generics-mrsop, graphviz
, hs-digems, hyper, language-c, language-lua, leancheck, mtl
, optparse-applicative, parsec, semigroupoids, stdenv, text
, criterion, QuickCheck
}:
mkDerivation {
  pname = "generics-mrsop-diff";
  version = "0.0.0.0";
  src = ./.;
  isLibrary = true;
  isExecutable = true;
  libraryHaskellDepends = [
    base generics-mrsop graphviz hs-digems hyper language-c
    language-lua mtl parsec semigroupoids text QuickCheck
  ];
  executableHaskellDepends = [
    base filepath generics-mrsop graphviz language-lua
    optparse-applicative text criterion
  ];
  testHaskellDepends = [ base Cabal generics-mrsop leancheck ];
  license = stdenv.lib.licenses.bsd3;
}
