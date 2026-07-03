{
  lib,
  mathcomp,
  mkRocqDerivation,
  version ? null,
  trocq,
  prelude ? "std"
}:
let
  cleanSource = source: lib.cleanSourceWith {
    filter = (
      name: type:
      let
        baseName = baseNameOf (toString name);
      in
      type != "regular"
      || !(
        baseName == ".Makefile.d"
        || baseName == "Makefile.conf"
        || lib.hasSuffix ".vo" baseName
        || lib.hasSuffix ".vok" baseName
        || lib.hasSuffix ".vos" baseName
        || lib.hasSuffix ".glob" baseName
        || lib.match "^\..*\.aux$" baseName != null
      )
    );
    src = lib.cleanSource source;
  };
in
lib.throwIfNot (lib.elem prelude ["std" "hott"]) "Parameter `prelude` of package `trocq` should be either \"std\" or \"hott\"" <|
mkRocqDerivation {
  pname = "trocq-${prelude}-examples";
  inherit (trocq.${prelude}) version;

  src = cleanSource ../examples;

  makeFlags = [
    "-C"
    "${prelude}"
  ];

  propagatedBuildInputs = [
    trocq.${prelude}
    mathcomp.boot
    mathcomp.algebra
  ];
}
