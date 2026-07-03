{
  lib,
  mkCoqDerivation,
  coq-elpi,
  HoTT,
  prelude ? "std"
}:
  lib.throwIfNot (lib.elem prelude ["std" "hott"]) "Parameter `prelude` of package `trocq` should be either \"std\" or \"hott\"" <|
mkCoqDerivation {
  pname = "trocq-${prelude}";
  version = "0.0";

  src = ./..;

  buildFlags = [ "${prelude}" ];

  doCheck = true;
  checkTarget = [ "test-${prelude}" ];

  installTargets = [ "install-${prelude}" ];

  propagatedBuildInputs = [
    coq-elpi
  ] ++ lib.optionals (prelude == "hott") [
    HoTT
  ];
}
