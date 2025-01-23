{ pkgs }:
pkgs.rustPlatform.buildRustPackage {
  pname = "cera";
  version = "0.1.0";

  cargoLock.lockFile = ./Cargo.lock;

  src = pkgs.lib.cleanSource ./.;
}
