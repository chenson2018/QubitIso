Require Import QubitIso.Quaternion.
Require Import QubitIso.SU2.
Require Import QubitIso.Group.
Require Import QubitIso.MatrixAux.
Require Import QuantumLib.Matrix.
Require Import Setoid.

Definition Versor_to_SU2 (v: Versor): SU2.
Proof.
  destruct v as [(((x, y), z), w) E].
  unfold SU2.
  exists (
    fun row => fun col =>
    match row, col with
    | 0, 0 => (x, y)
    | 0, 1 => (z, w)
    | 1, 0 => (Ropp z, w)
    | 1, 1 => (x, Ropp y)
    | _, _ => C0
    end
  ).
  unfold Qnorm in E.
  apply pow_eq with (n := 2%nat) in E.
  rewrite pow2_sqrt in E.
  replace ((1^2)%R) with 1 in E by lra.
  repeat split.
  - show_wf.
  - lca.
  - lca.
  - unfold d2_det, Cmult, Cminus, Cplus, C1.
    simpl. f_equal.
    rewrite <- E.
    all: lra.
  - repeat apply Rplus_le_le_0_compat.
    all: apply pow2_ge_0.
Defined.

Lemma Versor_SU2_hom_mul: forall v1 v2: Versor,
  Versor_to_SU2 (v1 ** v2) *= (Versor_to_SU2 v1) × (Versor_to_SU2 v2).
Proof.
  intros.
  unfold SU2_equiv, sigma_proj1_rel, proj1_sig.
  destruct v1 as [(((a1, b1), c1), d1) E1].
  destruct v2 as [(((a2, b2), c2), d2) E2].
  unfold Vmul, SU2_mul, Versor_to_SU2, Qmul, Mmult, big_sum.
  simpl.
  by_cell; lca.
Qed.

#[export] Instance Versor_Homomorphism_SU2: 
  GroupHomomorphism 
    Versor 
    SU2 
    Vmul 
    SU2_mul 
    versor_equiv 
    SU2_equiv 
    Versor_to_SU2
  := 
{
    hom_left_group  := Versor_is_Group
  ; hom_right_group := SU2_is_Group
  ; hom_mul         := Versor_SU2_hom_mul
}.

Local Open Scope nat_scope.
Definition SU2_to_Versor (U: SU2) : Versor.
Proof.
  unfold Versor.
  remember U as U'.
  destruct U as [U [WF_U [[gen_a_U gen_b_U] norm_U]]].
  exists (Re (U 0 0), Im (U 0 0), Re (U 0 1), Im (U 0 1)).
  unfold Qnorm.
  unfold d2_det in norm_U.
  apply sqrt_lem_1.
  - repeat apply Rplus_le_le_0_compat.
    all: apply pow2_ge_0.
  - lra.
  - replace ((1 * 1)%R) with 1%R by lra.
    apply RtoC_inj.
    rewrite <- norm_U.
    rewrite gen_a_U, gen_b_U.
    unfold Re, Im, Cconj.
    simpl. lca.
Defined.
Local Close Scope nat_scope.

Lemma SU2_Versor_iso_left_inv: forall v: Versor, 
  SU2_to_Versor (Versor_to_SU2 v) $= v.
Proof.
  intros.
  unfold versor_equiv, sigma_proj1_rel, proj1_sig.
  destruct v as [(((a, b), c), d) E].
  simpl.
  reflexivity.
Qed.  

Lemma SU2_Versor_iso_right_inv: forall U: SU2, 
  Versor_to_SU2 (SU2_to_Versor U) *= U.
Proof.
  intros.
  unfold SU2_equiv, sigma_proj1_rel, proj1_sig.
  destruct U as [U [WF_U [[gen_a_U gen_b_U] norm_U]]].
  simpl.
  unfold Re, Im.
  by_cell.
  - lca.
  - lca.
  - rewrite gen_b_U. lca.
  - rewrite gen_a_U. lca.
Qed.

#[export] Instance Versor_Isomorphism_SU2:
  GroupIsomorphism
    Versor
    SU2
    Vmul
    SU2_mul
    versor_equiv
    SU2_equiv
    Versor_to_SU2
    SU2_to_Versor
  :=
{
    hom              := Versor_Homomorphism_SU2
  ; iso_right_inv    := SU2_Versor_iso_right_inv
  ; iso_left_inv     := SU2_Versor_iso_left_inv
}.

Lemma SU2_Iso_to_hom: 
  GroupHomomorphism 
    SU2 
    Versor 
    SU2_mul 
    Vmul 
    SU2_equiv 
    versor_equiv 
    SU2_to_Versor.
Proof.
  apply Iso_to_Hom_inv with Versor_to_SU2.
  - apply (sigma_proj1_rel_equivalence eq_equivalence).
  - apply (sigma_proj1_rel_equivalence mat_equiv_equivalence).
  - unfold Morphisms.Proper, Morphisms.respectful.
    intros.
    rename x into v1.
    rename y into v2.
    unfold SU2_equiv, sigma_proj1_rel, proj1_sig.
    destruct v1 as [(((a1, b1), c1), d1) E1].
    destruct v2 as [(((a2, b2), c2), d2) E2].
    simpl.
      by_cell
    ; unfold versor_equiv, sigma_proj1_rel, proj1_sig in H
    ; inversion H
    ; subst
    ; reflexivity
    .
  - unfold Morphisms.Proper, Morphisms.respectful.
    intros.
    rename x into U1.
    rename y into U2.
    unfold versor_equiv, sigma_proj1_rel, proj1_sig.
    destruct U1 as [U1 [WF_U1 [[gen_a_U1 gen_b_U1] norm_U1]]].
    destruct U2 as [U2 [WF_U2 [[gen_a_U2 gen_b_U2] norm_U2]]].
    simpl.
    unfold SU2_equiv, sigma_proj1_rel, proj1_sig in H.
    unfold mat_equiv in H.
    assert (Ha: (U1 0%nat 0%nat) = (U2 0%nat 0%nat)) by (apply H; lia).
    assert (Hb: (U1 0%nat 1%nat) = (U2 0%nat 1%nat)) by (apply H; lia).
    repeat rewrite <- Ha.
    repeat rewrite <- Hb.
    reflexivity.
  - intros.
    unfold versor_equiv, sigma_proj1_rel, proj1_sig in *.
    unfold Vmul.
    destruct g1 as [(((a1, b1), c1), d1) E1].
    destruct g2 as [(((a2, b2), c2), d2) E2].
    destruct g1' as [(((a1', b1'), c1'), d1') E1'].
    destruct g2' as [(((a2', b2'), c2'), d2') E2'].
    inversion H.
    inversion H0.
    subst.
    reflexivity.
  - intros.
    unfold SU2_equiv, sigma_proj1_rel, proj1_sig in *.
    unfold SU2_mul.
    destruct h1 as [h1 [WF_h1 [[gen_a_h1 gen_b_h1] norm_h1]]].
    destruct h2 as [h2 [WF_h2 [[gen_a_h2 gen_b_h2] norm_h2]]].
    destruct h1' as [h1' [WF_h1' [[gen_a_h1' gen_b_h1'] norm_h1']]].
    destruct h2' as [h2' [WF_h2' [[gen_a_h2' gen_b_h2'] norm_h2']]].
    rewrite H, H0.
    reflexivity.
  - apply Versor_Isomorphism_SU2.
Qed.
