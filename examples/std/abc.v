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

Require Import ssreflect.
From Trocq Require Import Trocq.
From elpi Require Import elpi.

Set Universe Polymorphism.

Definition mkParam10 {X Y : Type} (f : X -> Y) : Param10.Rel X Y
    := Param10.BuildRel X Y (fun x y => True) (Map1.BuildHas X Y _ f) (Map0.BuildHas Y X _).

Definition mkParam01 {X Y : Type} (f : X -> Y) : Param01.Rel Y X
    := Param01.BuildRel Y X (fun x y => True) (Map0.BuildHas Y X _) (Map1.BuildHas X Y _ f).

Definition mkParam11 {X Y : Type} (f : X -> Y) (g : Y -> X) : Param11.Rel X Y
    := Param11.BuildRel X Y (fun x y => True) (Map1.BuildHas X Y _ f) (Map1.BuildHas Y X _ g).

Module SimpleTest.
Section SimpleTest.

    Variable (A B : Type) (f : A -> B).

    Definition Rf := mkParam01 f.
    Trocq Use Rf.

    Definition IdA : Param01.Rel A A := mkParam01 (fun x => x).
    Trocq Use IdA.

    Goal B.
        trocq to A.
        suff x : A by [].
    Abort.

End SimpleTest.
End SimpleTest.

Module BothSidesTest.
Section BothSidesTest.

    Variable (A A' A'' B B' : Type).
    Variable (f1 : A -> A') (f2 : A'' -> A) (g1 : B -> B') (g2 : B' -> B).

    Definition RA1 : Param10.Rel A A' := mkParam10 f1.
    Definition RA2 : Param01.Rel A A'':= mkParam01 f2.
    Definition RB  : Param11.Rel B B' := mkParam11 g1 g2.

    Trocq Use RA1 RA2 RB.

    Goal A.
        trocq.
        suff x : A'' by [].
    Abort.

    Goal A -> B.
        trocq.
        suff x : (A' -> B') by [].
    Abort.

    Goal B -> A.
        trocq.
        suff x : (B' -> A'')     by [].
    Abort.

End BothSidesTest.
End BothSidesTest.

Module TwoTranslationsTest.
Section TwoTranslationsTest.

    Variable (A B C : Type).
    Variable (f1 : B -> A) (f2 : C -> A).

    Definition R1 : Param01.Rel A B := mkParam01 f1.
    Definition R2 : Param01.Rel A C := mkParam01 f2.

    Trocq RelatedWith R1 R1.
    Trocq RelatedWith R2 R2.

    Goal A.
        trocq to B with R1.
        suff x : (B) by [].
    Abort.

    Goal A.
        trocq to C with R2.
        suff x : (C) by [].
    Abort.


    

End TwoTranslationsTest.
End TwoTranslationsTest.
