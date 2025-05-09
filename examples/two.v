From Coq Require Import ssreflect.
From HoTT Require Import HoTT.
From Trocq Require Import Trocq.
From Trocq_examples Require Import N.

Set Universe Polymorphism.

Inductive Two : Type :=
    | zero : Two
    | one : Two.

Record NatPair : Type := mkNatPair
    { a : nat
    ; b : nat }.
    

Definition mkTN (x y : nat): Two -> nat := fun t => match t with
    | zero => x
    | one => y
    end.

Definition pairOfTN (f : Two -> nat) : NatPair := mkNatPair (f zero) (f one).

Definition tnOfPair (pn : NatPair) : Two -> nat := mkTN (a pn) (b pn).

Axiom potK : forall (f : Two -> nat), tnOfPair (pairOfTN f) = f.
Axiom topK : forall (pn : NatPair), pairOfTN (tnOfPair pn) = pn.

Definition TwoNatPairEquiv : ((Two -> nat) <=> NatPair)%P :=
    Iso.toParamSym (Iso.Build topK potK).

Trocq Use TwoNatPairEquiv.

Definition mkE (n m : nat) : TwoNatPairEquiv (mkTN n m) (mkNatPair n m).
Proof. unfold TwoNatPairEquiv,mkTN.
Abort.

Theorem etaNatPair : forall n n' m m' : nat, mkNatPair n m = mkNatPair n' m' -> n = n'.
Proof.
    intros n n' m m' pneq.
    inversion pneq.
    reflexivity.
Defined.

Theorem etaTN : forall n n' m m' : nat, mkTN n m = mkTN n' m' -> n = n'.
Proof.
    trocq.
    exact etaNatPair.
Defined.
