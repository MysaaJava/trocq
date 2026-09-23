(*****************************************************************************)
(*                            *                    Trocq                     *)
(*  _______                   *       Copyright (C) 2023 Inria & MERCE       *)
(* |__   __|                  *    (Mitsubishi Electric R&D Centre Europe)   *)
(*    | |_ __ ___   ___ __ _  *       Cyril Cohen <cyril.cohen@inria.fr>     *)
(*    | | '__/ _ \ / __/ _` | *       Enzo Crance <enzo.crance@inria.fr>     *)
(*    | | | | (_) | (_| (_| | *   Assia Mahboubi <assia.mahboubi@inria.fr>   *)
(*    |_|_|  \___/ \___\__, | ************************************************)
(*                        | | * This file is distributed under the terms of  *)
(*                        |_| * GNU Lesser General Public License Version 3  *)
(*                            * see LICENSE file for the text of the license *)
(*****************************************************************************)

From Trocq Require Import Stdlib Trocq.

Set Universe Polymorphism.

Section VernacRegister.

    Variable (A A' A'' B B' B'' C C' C'' D D' D'' E E' E'' F F' F'' : Type).
    
    Variable (RA1 : Param2a4.Rel A A').
    Variable (RA2 : Param33.Rel A A'').
    Variable (RB1 : Param32b.Rel B B').
    Variable (RB2 : Param14.Rel B B'').
    Variable (RC1 : Param32b.Rel C C').
    Variable (RC2 : Param14.Rel C C'').
    Variable (RD1 : Param32b.Rel D D').
    Variable (RD2 : Param14.Rel D D'').
    Variable (RE1 : Param32b.Rel E E').
    Variable (RE2 : Param14.Rel E E'').
    Variable (RF1 : Param32b.Rel F F').
    Variable (RF2 : Param14.Rel F F'').



    Variable (DB : unit).

    Trocq Usage.

    Trocq Register RA1.
    Trocq Register RA2 : DB.
    Trocq Register RB1 rel RB1.
    Trocq Register RB2 rel RB2 : DB.
    Trocq Register RC1 : C ~ C'.
    Trocq Register RC2 : C ~ C'' : DB.
    Trocq Register RD1 : D ~ D' @ (PType map3 map2b).
    Trocq Register RD2 : D ~ D'' @ (PType map1 map4) : DB.
    Trocq Register RE1 : E ~ E'.
    Trocq Register RE2 : E ~ E'' : DB.
    Trocq Register RF1 : F ~ F' @ (PType map3 map2b).
    Trocq Register RF2 : F ~ F'' @ (PType map1 map4) : DB.

    Trocq Print Translations.

    Trocq Print Translations A.
    Trocq Print Translations B.
    Trocq Print Translations C.
    Trocq Print Translations D.
    Trocq Print Translations E.
    Trocq Print Translations F.

End VernacRegister.
