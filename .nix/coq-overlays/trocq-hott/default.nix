{
  lib,
  mkCoqDerivation,
  coq-elpi,
  HoTT,
  trocq,
}:

mkCoqDerivation {
  pname = "trocq-hott";
  inherit (trocq) version;

  buildFlags = [ "hott" ];

  doCheck = true;
  checkTarget = [ "test-hott" ];

  installTargets = [ "install-hott" ];

  propagatedBuildInputs = [
    coq-elpi
    HoTT
  ];
}
