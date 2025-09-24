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

Section Transfer.
    Variable (I I' : Type) (f : I' -> I).
    Variable (p : I -> I -> I) (p' : I' -> I' -> I').

    Definition Rf := mkParam2a0 f.
    Trocq Use Rf.

    Definition Rg (m : I) (m' : I') (rm : (Rf) m' m)
        (n : I) (n' : I') (rn : (Rf) n' n)
        : (Rf) (p' n' m') (p n m).
        admit.
    Admitted.

    Trocq Use Rg.

    Trocq Logging trace.
    
    Goal forall m: I', @eq I' m (p' m m).
        trocq.
        enough (forall m n : I, m = p n n -> m = n) by exact x.
    Abort.


End Transfer.