{ mkDerivation, base, generics-mrsop, graphviz, language-c
, language-lua, mtl, stdenv, text
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
  executableHaskellDepends = [ base generics-mrsop ];
  license = stdenv.lib.licenses.bsd3;
}