Require Import QuantumLib.Complex.
Require Import QuantumLib.Matrix.
Require Import QubitIso.MatrixAux.
Require Import QubitIso.Group.

(* 
  TODO this is nearly the same, even in the proofs, to the SU(2) group.

  Is there a way to make a general type for them???

  Also may need to tweak the orthogonal definition to be 3x3 specific

  I should really define general determinants (or check harder to see if QuantumLib has them)
*)

Definition Real_matrix {n} (U: Matrix n n): Prop := forall i j, Im (U i j) = 0.

Definition SO3 :=
  {
    U: Matrix 3 3
    |
    WF_Matrix U /\
    Real_matrix U /\
    U × (U) ⊤ ≡ I 3 /\
    (U) ⊤ × U ≡ I 3 /\
    d3_det U = C1
  }.

Definition SO3_mul (A B: SO3) : SO3.
Proof.
  unfold SO3.
  destruct A as [A [WF_A [Real_A [left_inv_A [right_inv_A norm_A]]]]].
  destruct B as [B [WF_B [Real_B [left_inv_B [right_inv_B norm_B]]]]].
  exists (A × B).
  repeat split.
  - apply WF_mult; assumption.
  - unfold Real_matrix.
    intros.
    unfold Mmult, big_sum, Im.
    simpl.
    repeat rewrite Real_A.
    repeat rewrite Real_B.
    repeat rewrite Rmult_0_l.
    repeat rewrite Rmult_0_r.
    lra.
  - rewrite Mmult_transpose.
    rewrite Mmult_assoc.
    rewrite <- (Mmult_assoc B _ _).
    rewrite left_inv_B.
    rewrite Mmult_1_l_mat_eq.
    assumption.
  - rewrite Mmult_transpose.
    rewrite Mmult_assoc.
    rewrite <- (Mmult_assoc _ A _).
    rewrite right_inv_A.
    rewrite Mmult_1_l_mat_eq.
    assumption.
  - replace C1 with (C1 * C1) by lca.
    rewrite <- norm_A at 1.
    rewrite <- norm_B.
    unfold d3_det, Mmult, big_sum.
    simpl.
    lca.
Defined.

(* lift matrix multiplication notation *)

Declare Scope SO3_scope.
Delimit Scope SO3_scope with SO3.
Open Scope SO3_scope.
Bind Scope SO3_scope with SO3.
Infix "×" := SO3_mul (at level 40, left associativity): SO3_scope.

(* equivalence relation for the SO3 sigma type *)

Definition SO3_equiv (U1 U2 : SO3) : Prop := 
  sigma_proj1_equiv (mat_equiv_equiv 3 3) U1 U2.
Reserved Notation "x *= y" (at level 70).
Infix "*=" := SO3_equiv: SO3_scope.

Add Parametric Relation : SO3 SO3_equiv
  reflexivity proved by (sigma_proj1_refl (mat_equiv_equiv 3 3))
  symmetry proved by (sigma_proj1_sym (mat_equiv_equiv 3 3))
  transitivity proved by (sigma_proj1_trans (mat_equiv_equiv 3 3))
as SO3_equiv_rel.

(* matrix inversion in SO(3), carrying proof of closure *)

Lemma d3_det_transpose: forall (A: Matrix 3 3), d3_det (A ⊤ ) = (d3_det A).
Proof.
  intros.
  unfold transpose, d3_det.
  lca.
Qed.  

Definition SO3_inv (A: SO3) : SO3.
Proof.
  unfold SO3.
  destruct A as [A [WF_A [Real_A [left_inv_A [right_inv_A norm_A]]]]].
  exists (A ⊤ ).
  repeat split.
  - apply WF_transpose. assumption.
  - unfold Real_matrix, transpose in *.
    intros.
    apply Real_A.
  - unfold transpose.
    rewrite right_inv_A.
    reflexivity.
  - unfold transpose.
    rewrite left_inv_A.
    reflexivity.
  - rewrite d3_det_transpose.
    assumption.
Defined.

(* I_3 is the identity in SO(3) *)

Definition I3: SO3.
Proof.
  unfold SO3.
  apply exist with (I 3).
  repeat split.
  - apply WF_I.
  - unfold Real_matrix, Im, I.
    intros.
    destruct (i =? j); simpl.
    + destruct (i <? 3); reflexivity.
    + reflexivity.
  - unfold transpose.
    rewrite Mmult_1_l_mat_eq.
    unfold I.
    by_cell; reflexivity.
  - unfold transpose.
    rewrite Mmult_1_r_mat_eq.
    unfold I.
    by_cell; reflexivity.
  - unfold I, d3_det. lca.
Defined.

(* group proofs *)

Lemma SO3_id_left: forall U: SO3, I3 × U *= U.
Proof.
  intros.
  unfold SO3_equiv, sigma_proj1_equiv, proj1_sig.
  destruct U as [U [WF_U [Real_U [left_inv_U [right_inv_U norm_U]]]]].
  simpl.    
  rewrite Mmult_1_l_mat_eq.
  reflexivity.
Qed.

Lemma SO3_id_right: forall U: SO3, U × I3 *= U.
Proof.
  intros.
  unfold SO3_equiv, sigma_proj1_equiv, proj1_sig.
  destruct U as [U [WF_U [Real_U [left_inv_U [right_inv_U norm_U]]]]].
  simpl.    
  rewrite Mmult_1_r_mat_eq.
  reflexivity.
Qed.

Lemma SO3_assoc: forall A B C: SO3,
  A × B × C *= A × (B × C).
Proof.
  intros.
  unfold SO3_equiv, sigma_proj1_equiv, proj1_sig.
  destruct A as [A [WF_A [Real_A [left_inv_A [right_inv_A norm_A]]]]].
  destruct B as [B [WF_B [Real_B [left_inv_B [right_inv_B norm_B]]]]].
  destruct C as [C [WF_C [Real_C [left_inv_C [right_inv_C norm_C]]]]].
  simpl.
  rewrite Mmult_assoc.
  reflexivity.
Qed.

Lemma SO3_right_inv: forall U: SO3, U × (SO3_inv U) *= I3.
Proof.
  intros.
  unfold SO3_equiv, sigma_proj1_equiv, proj1_sig.
  destruct U as [U [WF_U [Real_U [left_inv_U [right_inv_U norm_U]]]]].
  unfold SO3_inv, SO3_mul.
  simpl.
  assumption.
Qed.

(* group instance *)

#[export] Instance SO3_is_Group : Group SO3 SO3_mul SO3_equiv := {
    id             := I3
  ; inverse        := SO3_inv
  ; rel_equiv      := sigma_proj1_equiv_equiv (mat_equiv_equiv 3 3)
  ; id_left        := SO3_id_left
  ; id_right       := SO3_id_right
  ; assoc          := SO3_assoc
  ; right_inv      := SO3_right_inv
}.
