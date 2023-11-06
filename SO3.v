Require Import QuantumLib.Complex.
Require Import QuantumLib.Matrix.
Require Import QubitIso.MatrixAux.
Require Import QubitIso.Group.

Definition Real_matrix {n} (U: Matrix n n): Prop := forall i j, Im (U i j) = 0.

Inductive SO3: (Matrix 3 3) -> Prop := 
  | so3_con {U}:
      WF_Matrix U ->
      Unitary U ->
      d3_det U = C1 ->
      Real_matrix U ->
      SO3 U.

Lemma SO3_id_left: forall U, SO3 U -> (I 3) × U == U.
  intros.
  destruct H.
  rewrite Mmult_1_l.
  reflexivity.
  assumption.
Qed.

Lemma SO3_id_right: forall U, SO3 U -> U × (I 3) == U.
  intros.
  destruct H.
  rewrite Mmult_1_r.
  reflexivity.
  assumption.
Qed.

Lemma SO3_assoc: forall A B C,
  SO3 A ->
  SO3 B ->
  SO3 C ->
  A × B × C == A × (B × C).
Proof.
  intros.
  rewrite Mmult_assoc.
  reflexivity.
Qed.

Lemma SO3_right_inv: forall U, SO3 U -> U × (U †) == (I 3).
Proof. intros. destruct H as [U' _ [rinv _] _ _]. assumption. Qed.

Lemma SO3_op_closed: forall A B,
  SO3 A ->
  SO3 B ->
  SO3 (A × B).
Proof.
  intros A B HA HB.
  remember HA as HA'.
  remember HB as HB'.
  destruct HA as [A' WF_A [Uni_A_r Uni_A_l] norm_A real_A].
  destruct HB as [B' WF_B [Uni_B_r Uni_B_l] norm_B real_B].
  constructor.
  - apply WF_mult; assumption.
  - unfold Unitary in *.
    rewrite Mmult_adjoint.
    split.
    + replace (A' × B' × ((B') † × (A') †))
      with    (A' × (B' × (B') †) × (A') †) by lma.
      rewrite Uni_B_r.
      rewrite SO3_id_right.
      rewrite Uni_A_r.
      reflexivity.
      assumption.
    + replace ((B') † × (A') † × (A' × B'))
      with    ((B') † × ((A') † × A') × B') by lma.
      rewrite Uni_A_l.
      rewrite Mmult_assoc.
      rewrite SO3_id_left.
      rewrite Uni_B_l.
      reflexivity.
      assumption.
  - replace C1 with (C1 * C1) by lca.
    rewrite <- norm_A at 1.
    rewrite <- norm_B.
    unfold d3_det, Mmult, big_sum.
    simpl.
    lca.
  - unfold Real_matrix in *. intros.
    unfold Mmult, big_sum, Im.
    simpl.
    repeat rewrite real_A.
    repeat rewrite real_B.
    repeat rewrite Rmult_0_l.
    repeat rewrite Rmult_0_r.
    lra.
Qed.

Lemma d3_det_adjoint: forall (A: Matrix 3 3), d3_det (A †) = Cconj (d3_det A).
Proof.
  intros.
  unfold adjoint, d3_det.
  lca.
Qed.  

Lemma SO3_inverse_closed: forall A, SO3 A -> SO3 (A †).
Proof.
  intros A H.
  remember H as H'.
  destruct H as [A' WF_A [Uni_A_r Uni_A_l] norm_A real_A].
  constructor.
  - apply WF_adjoint. assumption.
  - unfold Unitary in *.
    rewrite adjoint_involutive.
    split; assumption.
  - rewrite d3_det_adjoint.
    rewrite norm_A.
    lca.
  - unfold Real_matrix in *.
    intros.
    unfold adjoint, Cconj, Im.
    simpl.
    rewrite real_A.
    apply Ropp_0.
Qed.

#[export] Instance SO3_is_Group : PredicateGroup := {
    id             := I 3
  ; inverse        := adjoint
  ; pred           := SO3
  ; op             := @Mmult 3 3 3
  ; rel            := mat_equiv
  ; rel_equiv      := mat_equiv_equiv 3 3
  ; id_left        := SO3_id_left
  ; id_right       := SO3_id_right
  ; assoc          := SO3_assoc
  ; right_inv      := SO3_right_inv
  ; op_closed      := SO3_op_closed
  ; inverse_closed := SO3_inverse_closed
}.
