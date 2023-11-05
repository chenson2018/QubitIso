Require Import QuantumLib.Complex.
Require Import QuantumLib.Matrix.
Require Import QubitIso.MatrixAux.
Require Import QubitIso.Group.

(* while AB = I -> BA = I, this is much easier in a definition *)

Definition Unitary {n} (U: Matrix n n): Prop := 
  U × (U) † ≡ I n /\ (U) † × U ≡ I n.

Local Open Scope nat_scope.
Definition d2_det (A: Matrix 2 2) : C := (A 0 0) * (A 1 1) - (A 1 0) * (A 0 1).
Local Close Scope nat_scope.

Inductive SU2: (Matrix 2 2) -> Prop :=
  | su2_con {U}: 
      WF_Matrix U -> 
      Unitary U -> 
      d2_det U = C1 ->
      SU2 U.

Lemma SU2_id_left: forall U, SU2 U -> (I 2) × U == U.
  intros.
  destruct H.
  rewrite Mmult_1_l.
  reflexivity.
  assumption.
Qed.

Lemma SU2_id_right: forall U, SU2 U -> U × (I 2) == U.
  intros.
  destruct H.
  rewrite Mmult_1_r.
  reflexivity.
  assumption.
Qed.

Lemma SU2_assoc: forall A B C,
  SU2 A ->
  SU2 B ->
  SU2 C ->
  A × B × C == A × (B × C).
Proof.
  intros.
  rewrite Mmult_assoc.
  reflexivity.
Qed.

Lemma SU2_right_inv: forall U, SU2 U -> U × (U †) == (I 2).
Proof. intros. destruct H as [U' _ [rinv _] _]. assumption. Qed.

Lemma SU2_op_closed: forall A B,
  SU2 A ->
  SU2 B ->
  SU2 (A × B).
Proof.
  intros A B HA HB.
  remember HA as HA'.
  remember HB as HB'.
  destruct HA as [A' WF_A [Uni_A_r Uni_A_l] norm_A].
  destruct HB as [B' WF_B [Uni_B_r Uni_B_l] norm_B].
  constructor.
  - apply WF_mult; assumption.
  - unfold Unitary in *.
    rewrite Mmult_adjoint.
    split.

    + replace (A' × B' × ((B') † × (A') †))
      with    (A' × (B' × (B') †) × (A') †) by lma.
      rewrite Uni_B_r.
      rewrite SU2_id_right.
      rewrite Uni_A_r.
      reflexivity.
      assumption.
    + replace ((B') † × (A') † × (A' × B'))
      with    ((B') † × ((A') † × A') × B') by lma.
      rewrite Uni_A_l.
      rewrite Mmult_assoc.
      rewrite SU2_id_left.
      rewrite Uni_B_l.
      reflexivity.
      assumption.
  - replace C1 with (C1 * C1) by lca.
    rewrite <- norm_A at 1.
    rewrite <- norm_B.
    unfold d2_det, Mmult, big_sum.
    simpl.
    lca.
Qed.

Lemma d2_det_adjoint: forall (A: Matrix 2 2), d2_det (A †) = Cconj (d2_det A).
Proof.
  intros.
  unfold adjoint, d2_det.
  lca.
Qed.  

Lemma SU2_inverse_closed: forall A, SU2 A -> SU2 (A †).
Proof.
  intros A H.
  remember H as H'.
  destruct H as [A' WF_A [Uni_A_r Uni_A_l] norm_A].
  constructor.
  - apply WF_adjoint. assumption.
  - unfold Unitary in *.
    rewrite adjoint_involutive.
    split; assumption.
  - rewrite d2_det_adjoint.
    rewrite norm_A.
    lca.
Qed.

#[export] Instance SU2_is_Group : PredicateGroup := {
    id := I 2
  ; inverse        := adjoint
  ; pred           := SU2
  ; op             := @Mmult 2 2 2
  ; rel            := mat_equiv
  ; rel_equiv      := mat_equiv_equiv 2 2
  ; id_left        := SU2_id_left
  ; id_right       := SU2_id_right
  ; assoc          := SU2_assoc
  ; right_inv      := SU2_right_inv
  ; op_closed      := SU2_op_closed
  ; inverse_closed := SU2_inverse_closed
}.
