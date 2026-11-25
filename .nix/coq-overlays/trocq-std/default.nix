{
  lib,
  mkCoqDerivation,
  rocq-helpi,
  trocq,
}:

mkCoqDerivation {
  pname = "trocq-std";
  inherit (trocq) version;

  buildFlags = [ "std" ];

  doCheck = true;
  checkTarget = [ "test-std" ];

  installTargets = [ "install-std" ];

  propagatedBuildInputs = [
    rocq-helpi
  ];
}
