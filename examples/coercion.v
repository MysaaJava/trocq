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

From Coq Require Import ssreflect.
From Trocq Require Import Trocq.
From Trocq_examples Require Import N.
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
  (* Elpi Trace. *)
  Variable (A B C : Type) (f : A -> B).

  Definition Rf := mkParam01 f.
  Trocq Use Rf.

  Definition IdA : Param01.Rel A A := mkParam01 idmap.
  Trocq Use IdA.

  Definition IdB : Param01.Rel B B := mkParam01 idmap.
  Trocq Use IdB.

  Goal B.
    elpi trocqoercion (A).
  Abort.

  Print weaken.
  Goal B.
    (*try elpi trocqoercion (B).*)
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
  elpi trocqoercion (A'').
  Abort.

  Goal A -> B.
  elpi trocqoercion (A' -> B').
  Abort.

  About True.

  Goal B -> A.
  elpi trocqoercion (B' -> A'').
  Abort.

End BothSidesTest.
End BothSidesTest.

Module DoubleTest.
Section DoubleTest.

  Variable (A A' B B' : Type) (f : A -> A') (g : B' -> B).

  Definition Rf : Param01.Rel A' A :=
    Param01.BuildRel A' A (fun b a => True) (Map0.BuildHas A' A _) (Map1.BuildHas A A' _ f).
  Trocq Use Rf.
  
  Definition Rg : Param10.Rel B' B :=
    Param10.BuildRel B' B (fun b a => True) (Map1.BuildHas B' B _ g) (Map0.BuildHas B B' _).
  Trocq Use Rg.

  Goal (B' -> A').
    elpi trocqoercion (B -> A).
  Abort.
  

End DoubleTest.
End DoubleTest.
