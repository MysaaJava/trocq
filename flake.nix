{
  description = "Trocq is a modular parametricity plugin for Coq";

  inputs = {
    nixpkgs.url = "github:nixos/nixpkgs?ref=nixos-unstable";
    coq-nix-toolbox.url = "github:MysaaJava/coq-nix-toolbox?ref=tidyup";
    coq-nix-toolbox.inputs.nixpkgs.follows = "nixpkgs";
  };

  outputs = { self, nixpkgs, coq-nix-toolbox}: {

    packages = coq-nix-toolbox.mkRocqFlakesPackages {
      src = ./.;
    };

  };
}
