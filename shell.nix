{ pkgs ? import <nixpkgs> {} }:
pkgs.mkShell {
  buildInputs = [
    pkgs.pkg-config
    (pkgs.zstd.override { enableStatic = true; })
  ];
}
