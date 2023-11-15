Require Import QuantumLib.Matrix.
Require Import Relations.
Require Import Setoid.

(* some definitions used for SU(2) and SO(3) *)

(* while AB = I -> BA = I, this is much easier in a definition *)

Definition Unitary {n} (U: Matrix n n): Prop := 
  U × (U) † ≡ I n /\ (U) † × U ≡ I n.

(* determinants for 2x2 and 3x3 matrices *)

Local Open Scope nat_scope.
Definition d2_det (A: Matrix 2 2) : C := (A 0 0) * (A 1 1) - (A 1 0) * (A 0 1).

Definition d3_det (A: Matrix 3 3) : C := 
  let a := A 0 0 in
  let b := A 0 1 in
  let c := A 0 2 in
  let d := A 1 0 in
  let e := A 1 1 in
  let f := A 1 2 in
  let g := A 2 0 in
  let h := A 2 1 in
  let i := A 2 2 in
  a*e*i + b*f*g + c*d*h + - c*e*g + - b*d*i + - a*f*h
.
Local Close Scope nat_scope.

Lemma d2_det_adjoint: forall (A: Matrix 2 2), d2_det (A †) = Cconj (d2_det A).
Proof.
  intros.
  unfold adjoint, d2_det.
  lca.
Qed.  

(* setoid rewriting, mostly from https://rand.cs.uchicago.edu/vqc/Matrix.html *)

Lemma mat_equiv_refl: forall m n, reflexive (Matrix m n) mat_equiv.
Proof.
  unfold reflexive, mat_equiv.
  intros.
  reflexivity.
Qed.

Lemma mat_equiv_sym: forall m n, symmetric (Matrix m n) mat_equiv.
Proof.
  unfold symmetric, mat_equiv.
  intros.
  rewrite H.
  reflexivity.
  all: assumption.
Qed.

Lemma mat_equiv_trans: forall m n, transitive (Matrix m n) mat_equiv.
Proof.
  unfold transitive, mat_equiv.
  intros.
  rewrite H.
  rewrite H0.
  reflexivity.
  all: assumption.
Qed.

Lemma mat_equiv_equiv: forall m n, equiv (Matrix m n) mat_equiv.
Proof.
  intros.
  unfold equiv.
  repeat split.
  - apply mat_equiv_trans.
  - apply mat_equiv_sym.
Qed.    

Add Parametric Relation m n : (Matrix m n) (@mat_equiv m n)
  reflexivity proved by (mat_equiv_refl m n)
  symmetry proved by (mat_equiv_sym m n)
  transitivity proved by (mat_equiv_trans m n)
as mat_equiv_rel.

Lemma Csum_eq : forall (f g : nat -> C) (n : nat),
  (forall x, (x < n)%nat -> f x = g x) ->
  big_sum f n = big_sum g n.
  intros f g n H.
  induction n.
  + simpl. reflexivity.
  + simpl.
    rewrite H by lia.
    rewrite IHn by (intros; apply H; lia).
    reflexivity.
Qed.

Lemma Mmult_compat : forall {m n o} (A A' : Matrix m n) (B B' : Matrix n o),
  A == A' -> B == B' -> A × B == A' × B'.
Proof.
  intros m n o A A' B B' HA HB i j Hi Hj.
  unfold Mmult.
  apply Csum_eq; intros x Hx.
  rewrite HA, HB; easy.
Qed.

Add Parametric Morphism m n o : (@Mmult m n o)
  with signature mat_equiv ==> mat_equiv ==> mat_equiv as Mmult_mor.
Proof. intros. apply Mmult_compat; easy. Qed.

Lemma transpose_compat : forall {m n} (A A' : Matrix m n),
  A == A' -> A⊤ == A'⊤.
Proof.
  intros m n A A' H.
  intros i j Hi Hj.
  unfold transpose.
  rewrite H; easy.
Qed.

Add Parametric Morphism m n : (@transpose m n)
  with signature mat_equiv ==> mat_equiv as transpose_mor.
Proof. intros. apply transpose_compat; easy. Qed.

Lemma adjoint_compat : forall {m n} (A A' : Matrix m n),
  A == A' -> A† == A'†.
Proof.
  intros m n A A' H.
  intros i j Hi Hj.
  unfold adjoint.
  rewrite H; easy.
Qed.

Add Parametric Morphism m n : (@adjoint m n)
  with signature mat_equiv ==> mat_equiv as adjoint_mor.
Proof. intros. apply adjoint_compat; easy. Qed.
