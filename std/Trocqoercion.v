From elpi Require Import elpi.
From Coq Require Import ssreflect.
Require Export Database.
Require Import HoTT_additions Hierarchy.
Require Export Param_Type Param_arrow Param_forall.

From Trocq.Elpi Extra Dependency "annot.elpi" as annot.
From Trocq.Elpi Extra Dependency "util.elpi" as util.
From Trocq.Elpi Extra Dependency "class.elpi" as class.
From Trocq.Elpi Extra Dependency "param-class-util.elpi" as param_class_util.
From Trocq.Elpi Extra Dependency "param.elpi" as param.
From Trocq.Elpi.constraints Extra Dependency "simple-graph.elpi" as simple_graph.
From Trocq.Elpi.constraints Extra Dependency "constraint-graph.elpi" as constraint_graph.
From Trocq.Elpi.constraints Extra Dependency "constraints.elpi" as constraints.
From Trocq.Elpi.constraints Extra Dependency "constraints-impl.elpi" as constraints_impl.


Elpi Tactic trocqoercion.
Elpi Accumulate lp:{{

  solve (goal Ctx _Trigger Type Proof _) _ :-
    coq.say "Goal:" Ctx "|-" Proof ":" Type.

}}.
Tactic Notation "trocqoercion" := elpi trocqoercion.

Goal forall A, A -> A.
trocqoercion.
Abort.

(* Example of coercion *)

