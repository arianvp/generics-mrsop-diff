{ pkgs ? import <nixpkgs> {} }:
let url = "https://releases.nixos.org/nixpkgs/nixpkgs-${pkgs.lib.version}/nixexprs.tar.xz";
in
pkgs.writeShellScriptBin "nix-lock" ''
  sha256=$(nix-prefetch-url --unpack ${url})

  cat <<EOF 
  import (fetchTarball {
    url = ${url};
    sha256 = "$sha256";
  })
  EOF

''
