{ mkDerivation, base, containers, fetchgit, mtl, stdenv
, template-haskell
}:
mkDerivation {
  pname = "generics-mrsop";
  version = "1.2.1";
  src = fetchgit {
    url = "https://github.com/VictorCMiraldo/generics-mrsop";
    sha256 = "0lsc8g4hj3cz3d9030k9p35iqnbmv57q0zikj09rg01kibb02mjv";
    rev = "227cbe827ab97b8e84a3b51826c58ffd06d626e3";
  };
  libraryHaskellDepends = [ base containers mtl template-haskell ];
  description = "Generic Programming with Mutually Recursive Sums of Products";
  license = stdenv.lib.licenses.mit;
}
