{
  description = "Euclidean Geometry - Hilbert's Axioms";

  inputs = {
    nixpkgs.follows = "lean4-nix/nixpkgs";
    flake-parts.url = "github:hercules-ci/flake-parts";
    lean4-nix.url = "github:lenianiva/lean4-nix";
  };

  outputs = inputs @ {
    nixpkgs,
    flake-parts,
    lean4-nix,
    ...
  }:
    flake-parts.lib.mkFlake {inherit inputs;} {
      systems = [
        "aarch64-darwin"
        "aarch64-linux"
        "x86_64-darwin"
        "x86_64-linux"
      ];

      perSystem = {
        system,
        pkgs,
        ...
      }: {
        _module.args.pkgs = import nixpkgs {
          inherit system;
          overlays = [(lean4-nix.readToolchainFile ./lean-toolchain)];
        };

        # nix build is broken with mathlib (proofwidgets requires network at build time,
        # blocked by nix sandbox). Use `nix develop` + `lake build` instead.
        # Tracking: https://github.com/lenianiva/lean4-nix/issues/115
        devShells.default = pkgs.mkShell {
          packages = with pkgs.lean; [lean-all];
        };
      };
    };
}
