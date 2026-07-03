{
  description = "Trocq, a modular parametricity plugin for Rocq";

  inputs = {
    coq-nix-toolbox.url = "github:MysaaJava/coq-nix-toolbox?ref=flakes";

    hott-91.url = "github:HoTT/Coq-HoTT?ref=V9.1";

    rocq-elpi.url = "github:LPCIC/coq-elpi?ref=ba3cc750eda486c85d94e3eb35fb0eba77609338";
    rocq-elpi.flake = false;
  };

  outputs = { self, coq-nix-toolbox, ... }@inputs: {
    packages = coq-nix-toolbox.exportOverlays self.overlays (system: {
      default = self.packages.${system}.trocq-std;
      trocq-std = self.packages.${system}.rocq91.rocqPackages.trocq.std;
      trocq-hott = self.packages.${system}.coq91.coqPackages.trocq.hott;
    });

    apps = coq-nix-toolbox.apps;

    overlays = let
      common-coq-overlay = coq-nix-toolbox.mkOverlay {
        coqPackages.coq-elpi.override.version = "ba3cc750eda486c85d94e3eb35fb0eba77609338";
        coqPackages.coq-elpi.overrideAttrs.src = inputs.rocq-elpi;      
      };
      common-rocq-overlay = coq-nix-toolbox.mkOverlay {
        rocqPackages.rocq-elpi.override.version = "ba3cc750eda486c85d94e3eb35fb0eba77609338";
        rocqPackages.rocq-elpi.overrideAttrs.src = inputs.rocq-elpi;
      };
      coq90-overlay = coq-nix-toolbox.mkOverlay {
        coqPackages.coq.override.version = "9.0";
      };
      coq91-overlay = coq-nix-toolbox.mkOverlay {
        coqPackages.coq.override.version = "9.1";
        coqPackages.HoTT.override.version = "V9.1"; # HoTT isn't available yet for 9.1
        coqPackages.HoTT.overrideAttrs.src = inputs.hott-91; # HoTT isn't available yet for 9.1
      };
      rocq90-overlay = coq-nix-toolbox.mkOverlay {
        rocqPackages.rocq-core.override.version = "9.0";
      };
      rocq91-overlay = coq-nix-toolbox.mkOverlay {
        rocqPackages.rocq-core.override.version = "9.1";
      };
      trocq-recipes-coq = (pkgs: {
        trocq.std  = pkgs.callPackage ./.nix/trocq.coq.nix { prelude = "std"; };
        trocq.hott = pkgs.callPackage ./.nix/trocq.coq.nix { prelude = "hott"; };
        trocq.examples.std = pkgs.callPackage ./.nix/trocq-examples.coq.nix { prelude = "std"; };
        trocq.examples.hott = pkgs.callPackage ./.nix/trocq-examples.coq.nix { prelude = "hott"; };
      });
      trocq-recipes = (pkgs: {
        trocq.std  = pkgs.callPackage ./.nix/trocq.nix { prelude = "std"; };
        trocq.hott = pkgs.callPackage ./.nix/trocq.nix { prelude = "hott"; };
        trocq.examples.std = pkgs.callPackage ./.nix/trocq-examples.nix { prelude = "std"; };
        trocq.examples.hott = pkgs.callPackage ./.nix/trocq-examples.nix { prelude = "hott"; };
      });
    in {
      coq90 = coq-nix-toolbox.composeOverlays [ (coq-nix-toolbox.mkCoqRecipesOverlay trocq-recipes-coq) coq90-overlay common-coq-overlay ];
      coq91 = coq-nix-toolbox.composeOverlays [ (coq-nix-toolbox.mkCoqRecipesOverlay trocq-recipes-coq) coq91-overlay common-coq-overlay ];
      rocq90 = coq-nix-toolbox.composeOverlays [ (coq-nix-toolbox.mkRocqRecipesOverlay trocq-recipes) rocq90-overlay common-rocq-overlay ];
      rocq91 = coq-nix-toolbox.composeOverlays [ (coq-nix-toolbox.mkRocqRecipesOverlay trocq-recipes) rocq91-overlay common-rocq-overlay ];
    };
  };
}
