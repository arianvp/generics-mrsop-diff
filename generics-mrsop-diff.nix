{ mkDerivation, base, filepath, generics-mrsop, graphviz
, language-c, language-lua, leancheck, mtl, optparse-applicative
, stdenv, text
}:
mkDerivation {
  pname = "generics-mrsop-diff";
  version = "0.0.0.0";
  src = ./.;
  isLibrary = true;
  isExecutable = true;
  libraryHaskellDepends = [
    base generics-mrsop graphviz language-c language-lua mtl text
  ];
  executableHaskellDepends = [
    base filepath generics-mrsop graphviz language-lua
    optparse-applicative text
  ];
  testHaskellDepends = [ base generics-mrsop leancheck ];
  license = stdenv.lib.licenses.bsd3;
}
