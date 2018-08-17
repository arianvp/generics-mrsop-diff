{ mkDerivation, base, bytestring, cmdargs, containers, cryptonite
, fetchgit, generics-mrsop, gitrev, memory, mtl, parsec, stdenv
}:
mkDerivation {
  pname = "hs-digems";
  version = "0.0.0";
  src = fetchgit {
    url = "https://github.com/VictorCMiraldo/hs-digems.git";
    sha256 = "1x6vqanc1id4v5iz7ylayvpwz2kwv44n2l393i9qkw5bjf6kl67q";
    rev = "a08f47d870cf991aec305ea5c3a8d66c3dd10c21";
  };
  isLibrary = true;
  isExecutable = true;
  libraryHaskellDepends = [
    base bytestring containers cryptonite generics-mrsop memory mtl
  ];
  executableHaskellDepends = [
    base cmdargs generics-mrsop gitrev parsec
  ];
  license = stdenv.lib.licenses.bsd3;
}
