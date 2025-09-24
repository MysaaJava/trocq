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

    Trocq Logging trace.

    Variable (I I' : Type) (f : I' -> I) (f' : I -> I').

    Definition Rf := mkParam2a0 f.
    Trocq Use Rf.
    Definition Rf' := mkParam2a0 f'.
    Trocq Use Rf'.

    Variable (pe : I -> I -> Prop) (pe' : I' -> I' -> Prop).
    Definition Rpe (m : I) (m' : I') (rm : (Rf') m m')
        (n : I) (n' : I') (rn : (Rf') n n')
        : Param01.Rel (pe n m) (pe' n' m').
        admit.
    Admitted.
    Trocq Use Rpe.

    Goal forall (m : I), pe m m.
    Proof.
    trocq.
    enough (x : forall m' : I', pe' m' m') by exact x.
    Abort.

    (*
    Variable (I I' : Type) (f : I' -> I) (f' : I -> I').
    Variable (p : I -> I -> I) (p' : I' -> I' -> I').
    Variable (pe : I -> I -> Prop) (pe' : I' -> I' -> Prop).

    Definition Rf := mkParam2a0 f.
    Trocq Use Rf.
    Definition Rf' := mkParam2a0 f'.
    Trocq Use Rf'.

    Definition Rg (m : I) (m' : I') (rm : (Rf) m' m)
        (n : I) (n' : I') (rn : (Rf) n' n)
        : (Rf) (p' n' m') (p n m).
        admit.
    Admitted.
    Trocq Use Rg.

    Definition Rp (m : I) (m' : I') (rm : (Rf) m' m)
        (n : I) (n' : I') (rn : (Rf) n' n)
        : Param00.Rel (pe' n' m') (pe n m).
        admit.
    Admitted.
    Trocq Use Rp.

    Trocq Logging trace.

    
    Goal forall m : I', pe' m m.
        trocq.
        admit.
    Admitted.
    

    Goal forall m: I', @eq I' m (p' m m).
        trocq.
        enough (forall m n : I, m = p n n -> m = n) by exact x.
    Abort.
    *)

End Transfer.
