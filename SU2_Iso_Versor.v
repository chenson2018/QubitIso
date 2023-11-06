Require Import QubitIso.Quaternion.
Require Import QubitIso.SU2.
Require Import QubitIso.Group.
Require Import QubitIso.MatrixAux.
Require Import QuantumLib.Matrix.

Definition f (q: Quaternion): Matrix 2 2 := 
  match q with
  | (x, y, z, w) => 
  fun row => fun col =>
  match row, col with
  | 0, 0 => (x, y)
  | 0, 1 => (z, w)
  | 1, 0 => (Ropp z, w)
  | 1, 1 => (x, Ropp y)
  | _, _ => C0
  end
  end.

Lemma Versor_SU2_hom_mul: forall x y, 
  Versor x -> 
  Versor y ->
  f (x ** y) == Mmult (f x) (f y).
Proof. 
  intros.
  destruct x as (((a1, b1), c1), d1).
  destruct y as (((a2, b3), c3), d3).
  by_cell; lca.
Qed.  

Lemma Versor_SU2_hom_f_closed: forall g,
  Versor g -> 
  SU2 (f g).
Proof.
  intros. destruct H.
  constructor.
  - unfold WF_Matrix.
    intros.
    destruct x as (((a1, b1), c1), d1).
    simpl.
    destruct x0.
    + destruct H0; inversion H0. reflexivity.
      destruct m. inversion H1. reflexivity.
    + destruct x0.
      destruct H0.
      * inversion H0. inversion H2.
      * destruct y. inversion H0. destruct y. inversion H0. inversion H2. 
        reflexivity.
      * reflexivity.
  - destruct x as (((a1, b1), c1), d1).
    unfold Unitary.
    apply pow_eq with _ _ (2%nat) in H.
    unfold Qnorm in H.
    rewrite pow2_sqrt in H.
    replace ((1^2)%R) with 1 in H by lra.
    split.
    + unfold Mmult, big_sum, adjoint, Cconj, mat_equiv, I.
      intros.
      destruct i, j.
      * simpl. rewrite Cplus_0_l.
        unfold Cmult.
        simpl. 
        unfold C1.
        rewrite <- H.
        lca.
      * simpl. destruct j.
        ** simpl. lca.
        ** simpl. lca.
      * simpl. destruct i.
        ** lca.
        ** lca.
      * simpl.
        destruct i, j.
        ** simpl. lca.
        ** simpl. lca.
        ** simpl. lca.
        ** inversion H1. inversion H3. inversion H5.
    + unfold Mmult, big_sum, adjoint, Cconj, mat_equiv, I.
      intros.
      destruct i, j.
      * simpl. rewrite Cplus_0_l.
        unfold Cmult.
        simpl. 
        unfold C1.
        rewrite <- H.
        lca.
      * simpl. destruct j.
        ** simpl. lca.
        ** simpl. lca.
      * simpl. destruct i.
        ** lca.
        ** lca.
      * simpl.
        destruct i, j.
        ** simpl. lca.
        ** simpl. lca.
        ** simpl. lca.
        ** inversion H1. inversion H3. inversion H5.
    + repeat apply Rplus_le_le_0_compat.
      all: apply pow2_ge_0.
  - destruct x as (((a1, b1), c1), d1).
    unfold d2_det.
    simpl. 
    unfold Qnorm in H.
    unfold Cmult. simpl.
    unfold C1.
    replace ((a1 * a1 - b1 * - b1)%R) with ((a1 ^ 2 + b1 ^ 2)%R) by lra.
    replace ((a1 * - b1 + b1 * a1)%R) with 0%R by lra.
    replace ((- c1 * c1 - d1 * d1)%R) with ((- (c1 ^ 2) - d1 ^ 2)%R) by lra.
    replace ((- c1 * d1 + d1 * c1)%R) with 0%R by lra.
    replace (_ - _) with ((a1 ^ 2 + b1 ^ 2 + c1 ^ 2 + d1 ^ 2)%R, 0) by lca.
    apply pow_eq with _ _ (2%nat) in H.
    rewrite pow2_sqrt in H.
    replace ((1^2)%R) with 1 in H by lra.
    rewrite H.
    reflexivity.
    repeat apply Rplus_le_le_0_compat.
    all: apply pow2_ge_0.
Qed.

#[export] Instance SU2_Homomorphism_Versor: 
  @GroupHomomorphism
    Quaternion
    (Matrix 2 2)
    Qmul
    Mmult
    eq
    mat_equiv
  := 
{
    hom_left_group  := Versor_is_Group
  ; hom_right_group := SU2_is_Group
  ; hom_f           := f
  ; hom_mul         := Versor_SU2_hom_mul
  ; hom_f_closed    := Versor_SU2_hom_f_closed
}.

Local Open Scope nat_scope.
Definition f_inv (U: Matrix 2 2) : Quaternion :=
  (Re (U 0 0), Im (U 0 0), Re (U 0 1), Im (U 0 1)).
Local Close Scope nat_scope.

Lemma SU2_Versor_iso_left_inv: forall q, Versor q -> f_inv (f q) = q.
Proof.
  intros.
  destruct q as (((a, b), c), d). 
  unfold f, f_inv, Re, Im.
  simpl.
  reflexivity.
Qed.  

Lemma SU2_generator_a: forall U, SU2 U -> (U 0%nat 0%nat) = Cconj (U 1%nat 1%nat).
Proof. Admitted.  

Lemma SU2_generator_b: forall U, SU2 U -> (U 0%nat 1%nat) = - Cconj (U 1%nat 0%nat).
Proof. Admitted.

Lemma SU2_Versor_iso_right_inv: forall U, SU2 U -> f (f_inv U) == U.
Proof.
  intros.
  by_cell; unfold Re, Im.
  - lca.
  - lca.
  - rewrite SU2_generator_b. lca. assumption.
  - rewrite SU2_generator_a. lca. assumption.
Qed.

Lemma SU2_Versor_iso_f_inv_closed: forall U, SU2 U -> Versor (f_inv U).
Proof.
  intros.
  remember H as H'.
  destruct H as [U' WF_U [Uni_U_r Uni_U_l] Uni_norm].
  constructor.
  unfold f_inv, Qnorm.
  unfold d2_det in Uni_norm.
  apply sqrt_lem_1.
  - repeat apply Rplus_le_le_0_compat.
    all: apply pow2_ge_0.
  - lra.
  - replace ((1 * 1)%R) with 1%R by lra.
    apply RtoC_inj.
    rewrite <- Uni_norm.
    rewrite SU2_generator_a.
    rewrite SU2_generator_b.
    unfold Re, Im, Cconj.
    simpl. lca.
    all: assumption.
Qed.    

#[export] Instance SU2_Isomorphism_Versor:
  @GroupIsomorphism
    Quaternion
    (Matrix 2 2)
    Qmul
    Mmult
    eq
    mat_equiv
  :=
{
    hom              := SU2_Homomorphism_Versor
  ; iso_f_inv        := f_inv
  ; iso_left_inv     := SU2_Versor_iso_left_inv
  ; iso_right_inv    := SU2_Versor_iso_right_inv
  ; iso_f_inv_closed := SU2_Versor_iso_f_inv_closed
}.
