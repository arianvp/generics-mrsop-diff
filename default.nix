{ mkDerivation, base, generics-mrsop, stdenv }:
mkDerivation {
  pname = "generics-mrsop-diff";
  version = "0.0.0.0";
  src = ./.;
  libraryHaskellDepends = [ base generics-mrsop ];
  license = stdenv.lib.licenses.bsd3;
}
