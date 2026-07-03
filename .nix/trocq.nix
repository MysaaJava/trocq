{
  lib,
  mkRocqDerivation,
  rocq-elpi,
  HoTT ? null,
  prelude ? "std"
}:
  lib.throwIfNot (lib.elem prelude ["std" "hott"]) "Parameter `prelude` of package `trocq` should be either \"std\" or \"hott\"" <|
mkRocqDerivation {
  pname = "trocq-${prelude}";
  version = "0.0";

  src = ./..;

  buildFlags = [ "${prelude}" ];

  doCheck = true;
  checkTarget = [ "test-${prelude}" ];

  installTargets = [ "install-${prelude}" ];

  propagatedBuildInputs = [
    rocq-elpi
  ] ++ lib.optionals (prelude == "hott") [
    HoTT
  ];
}
