Require Import QuantumLib.Complex.
Require Import QuantumLib.Matrix.
Require Import QubitIso.MatrixAux.
Require Import QubitIso.Group.

Local Open Scope nat_scope.

Definition SU2 := 
  {
    U: Matrix 2 2 
    |
    WF_Matrix U /\
    (U 0 0 = Cconj (U 1 1)   /\ U 0 1 = - Cconj (U 1 0) ) /\
    d2_det U = C1
  }.

(* show that these generators really do make unitary matrices *)

Lemma SU2_generators: forall U: Matrix 2 2,
  U 0 0 = Cconj (U 1 1) ->
  U 0 1 = - Cconj (U 1 0) ->
  d2_det U = C1 ->
  U × (U) † ≡ I 2 /\ (U) † × U ≡ I 2.
Proof.
  intros U gen_a gen_b norm.
  unfold I, adjoint, Cconj, Mmult, big_sum.
    split
  ; by_cell
  ; try rewrite <- norm
  ; unfold d2_det
  ; rewrite gen_a, gen_b
  ; lca.
Qed.  
Local Close Scope nat_scope.

(* matrix multiplication in SU(2), carrying proof of closure *)

Definition SU2_mul (A B: SU2) : SU2.
Proof.
  unfold SU2.
  destruct A as [A [WF_A [gen_A norm_A]]].
  destruct B as [B [WF_B [gen_B norm_B]]].
  exists (A × B).
  split.
  - apply WF_mult; assumption.
  - split.
    + unfold Mmult, big_sum.
      destruct gen_A as [gen_a_A gen_b_A].
      destruct gen_B as [gen_a_B gen_b_B].
      rewrite gen_a_A, gen_b_A, gen_a_B, gen_b_B.
      split; lca.
    + replace C1 with (C1 * C1) by lca.
      rewrite <- norm_A at 1.
      rewrite <- norm_B.
      unfold d2_det, Mmult, big_sum.
      simpl. 
      lca.
Defined.

(* lift matrix multiplication notation *)

Declare Scope SU2_scope.
Delimit Scope SU2_scope with SU2.
Open Scope SU2_scope.
Bind Scope SU2_scope with SU2.
Infix "×" := SU2_mul (at level 40, left associativity): SU2_scope.

(* equivalence relation for the SU2 sigma type *)

Definition SU2_equiv (U1 U2 : SU2) : Prop := 
  sigma_proj1_equiv (mat_equiv_equiv 2 2) U1 U2.
Reserved Notation "x *= y" (at level 70).
Infix "*=" := SU2_equiv: SU2_scope.

Add Parametric Relation : SU2 SU2_equiv
  reflexivity proved by (sigma_proj1_refl (mat_equiv_equiv 2 2))
  symmetry proved by (sigma_proj1_sym (mat_equiv_equiv 2 2))
  transitivity proved by (sigma_proj1_trans (mat_equiv_equiv 2 2))
as SU2_equiv_rel.

(* matrix inversion in SU(2), carrying proof of closure *)

Definition SU2_inv (A: SU2) : SU2.
Proof.
  unfold SU2.
  destruct A as [A [WF_A [[gen_a_A gen_b_A] norm_A]]].
  exists (A †).
  repeat split.
  - apply WF_adjoint. assumption.
  - unfold adjoint.
    rewrite gen_a_A.
    reflexivity.
  - unfold adjoint.
    rewrite gen_b_A.
    lca.
  - rewrite d2_det_adjoint.
    rewrite norm_A.
    lca.
Defined.

(* I_2 is the identity in SU(2) *)

Definition I2: SU2.
Proof.
  unfold SU2.
  apply exist with (I 2).
  repeat split.
  - apply WF_I.
  - unfold I. simpl. lca.
  - unfold I. simpl. lca.
  - unfold d2_det, I. simpl. lca.
Defined.

(* group proofs *)

Lemma SU2_id_left: forall U: SU2, I2 × U *= U.
Proof.
  intros.
  unfold SU2_equiv, sigma_proj1_equiv, proj1_sig.
  destruct U as [U [WF_U [[gen_a_U gen_b_U] norm_U]]].
  simpl.    
  rewrite Mmult_1_l_mat_eq.
  reflexivity.
Qed.

Lemma SU2_id_right: forall U: SU2, U × I2 *= U.
Proof.
  intros.
  unfold SU2_equiv, sigma_proj1_equiv, proj1_sig.
  destruct U as [U [WF_U [[gen_a_U gen_b_U] norm_U]]].
  simpl.    
  rewrite Mmult_1_r_mat_eq.
  reflexivity.
Qed.

Lemma SU2_assoc: forall A B C: SU2,
  A × B × C *= A × (B × C).
Proof.
  intros.
  unfold SU2_equiv, sigma_proj1_equiv, proj1_sig.
  destruct A as [A [WF_A [[gen_a_A gen_b_A] norm_A]]].
  destruct B as [B [WF_B [[gen_a_B gen_b_B] norm_B]]].
  destruct C as [C [WF_C [[gen_a_C gen_b_C] norm_C]]].
  simpl.
  rewrite Mmult_assoc.
  reflexivity.
Qed.

Lemma SU2_right_inv: forall U: SU2, U × (SU2_inv U) *= I2.
Proof.
  intros.
  unfold SU2_equiv, sigma_proj1_equiv, proj1_sig.
  destruct U as [U [WF_U [[gen_a_U gen_b_U] norm_U]]].
  unfold SU2_inv, SU2_mul.
  simpl.
  apply SU2_generators.
  all: assumption.
Qed.

(* group instance *)

#[export] Instance SU2_is_Group : Group SU2 SU2_mul SU2_equiv := {
    id             := I2
  ; inverse        := SU2_inv
  ; rel_equiv      := sigma_proj1_equiv_equiv (mat_equiv_equiv 2 2)
  ; id_left        := SU2_id_left
  ; id_right       := SU2_id_right
  ; assoc          := SU2_assoc
  ; right_inv      := SU2_right_inv
}.
