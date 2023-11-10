Require Import QubitIso.Quaternion.
Require Import QubitIso.SU2.
Require Import QubitIso.Group.
Require Import QubitIso.MatrixAux.
Require Import QuantumLib.Matrix.

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
  apply pow_eq with _ _ (2%nat) in E.
  rewrite pow2_sqrt in E.
  replace ((1^2)%R) with 1 in E by lra.
  repeat split.
  - show_wf.
  - lca.
  - lca.
  - unfold d2_det.
    unfold Cmult.
    simpl.
    unfold Cminus.
    unfold Cplus.
    simpl.
    unfold C1.
    f_equal.
    rewrite <- E.
    all: lra.
  - repeat apply Rplus_le_le_0_compat.
    all: apply pow2_ge_0.
Defined.

Lemma Versor_SU2_hom_mul: forall v1 v2: Versor,
  Versor_to_SU2 (v1 ** v2) *= (Versor_to_SU2 v1) × (Versor_to_SU2 v2).
Proof.
  intros.
  unfold SU2_equiv, sigma_proj1_equiv, proj1_sig.
  destruct v1 as [(((a1, b1), c1), d1) E1].
  destruct v2 as [(((a2, b2), c2), d2) E2].
  unfold Vmul, SU2_mul, Versor_to_SU2, Qmul, Mmult, big_sum.
  simpl.
  by_cell; lca.
Qed.

#[export] Instance SU2_Homomorphism_Versor: 
  @GroupHomomorphism
    Versor
    SU2
    Vmul
    SU2_mul
    versor_equiv
    SU2_equiv
  := 
{
    hom_left_group  := Versor_is_Group
  ; hom_right_group := SU2_is_Group
  ; hom_f           := Versor_to_SU2
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
  unfold versor_equiv, sigma_proj1_equiv, proj1_sig.
  destruct v as [(((a, b), c), d) E].
  simpl.
  reflexivity.
Qed.  

Lemma SU2_Versor_iso_right_inv: forall U: SU2, 
  Versor_to_SU2 (SU2_to_Versor U) *= U.
Proof.
  intros.
  unfold SU2_equiv, sigma_proj1_equiv, proj1_sig.
  destruct U as [U [WF_U [[gen_a_U gen_b_U] norm_U]]].
  simpl.
  unfold Re, Im.
  by_cell.
  - lca.
  - lca.
  - rewrite gen_b_U. lca.
  - rewrite gen_a_U. lca.
Qed.

#[export] Instance SU2_Isomorphism_Versor:
  @GroupIsomorphism
    Versor
    SU2
    Vmul
    SU2_mul
    versor_equiv
    SU2_equiv
  :=
{
    hom              := SU2_Homomorphism_Versor
  ; iso_f_inv        := SU2_to_Versor
  ; iso_right_inv    := SU2_Versor_iso_right_inv
  ; iso_left_inv     := SU2_Versor_iso_left_inv
}.
