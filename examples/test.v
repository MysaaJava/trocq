From Coq Require Import ssreflect.
(* From HoTT Require Import HoTT. *)
From Trocq Require Import Trocq.
From Trocq_examples Require Import N.

Inductive Vect (A : Type) : nat -> Type :=
    | nil : Vect A 0
    | cons : forall (n : nat) (l : Vect A n) (a : A), Vect A (S n).

Definition RN : (N <=> nat)%P := Iso.toParamSym N.of_nat_iso.
Definition RN0 : RN 0%N 0%nat. Proof. done. Defined.
Definition RNS m n : RN m n -> RN (N.succ m) (S n).
 Proof. by case: _ /. Defined.

Trocq Use RN.
Trocq Use RN0 RNS.

From Trocq.Elpi.constraints Extra Dependency "simple-graph.elpi" as simple_graph.
From Trocq.Elpi.constraints Extra Dependency "constraint-graph.elpi" as constraint_graph.
From Trocq.Elpi.constraints Extra Dependency "constraints.elpi" as constraints.

From Trocq.Elpi Extra Dependency "annot.elpi" as annot.
From Trocq.Elpi Extra Dependency "util.elpi" as util.
From Trocq.Elpi Extra Dependency "util-rocq.elpi" as util_rocq.
From Trocq.Elpi Extra Dependency "param-class-util.elpi" as param_class_util.

Elpi Command testprog.
Elpi Accumulate Db trocq.db.
Elpi Accumulate File util.
Elpi Accumulate File util_rocq.
Elpi Accumulate File annot.
Elpi Accumulate File param_class_util.
Elpi Accumulate File simple_graph.
Elpi Accumulate File constraint_graph.
Elpi Accumulate File constraints.

Elpi Query lp:{{
  param {{N}} T N NR.
}}.
