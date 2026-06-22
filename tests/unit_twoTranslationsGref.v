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

Section TrocqTo.

    Variable (A A' A'' : Type).
    Variable (F : A -> A -> Type) (G : A' -> A'' -> Type).

    Variable (Z : A) (Z' : A') (Z'' : A'').

    Variable (RA1 : Param01.Rel A A') (RA2 : Param01.Rel A A'').

    Trocq Register A @ (PType map0 map1) ~ A' because RA1.
    Trocq Register A @ (PType map0 map1) ~ A'' because RA2.

    Variable (RZ1 : RA1 Z Z') (RZ2 : RA2 Z Z'').

    Trocq Register Z @ (PTriple A A' RA1) ~ Z' because RZ1.
    Trocq Register Z @ (PTriple A A'' RA2) ~ Z'' because RZ2.

    Variable (RF : forall (n : A) (n' : A') (rn : RA1 n n')
        (m : A) (m' : A'') (rm : RA2 m m'), Param11.Rel (F n m) (G n' m')).

    Trocq Register F @ (PTriple A A' RA1 -> PTriple A A'' RA2 -> PType map1 map1) ~ G because RF.

    Trocq Logging trace.
    Goal F Z Z.
        trocq.
        enough (x : G Z' Z'') by exact x.
    Abort.

End TrocqTo.
