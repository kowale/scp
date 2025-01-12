{

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable";
    lean4-nix.url = "github:lenianiva/lean4-nix";
  };

  outputs = { self, nixpkgs, ... } @ inputs:

  let
    system = "x86_64-linux";

    # TODO: fix lean4-nix (error: version 7)
    lean-toolchain = inputs.lean4-nix.readToolchainFile ./lean-toolchain;

    pkgs = import nixpkgs {
      inherit system;
      # overlays = [ lean-toolchain ];
    };

    lake2nix = inputs.lean4-nix.lake { inherit pkgs; };
    scp = lake2nix.mkPackage { src = ./.; };

  in {

    packages.${system} = {
      # default = scp.executable;
    };

    devShells.${system} = {
      default = pkgs.mkShell {
        buildInputs = with pkgs; [
          elan # lean.elan
          tectonic
        ];
        shellHook = ''
          lake exe cache get
          du -sh .lake
        '';
      };
    };
  };
}
