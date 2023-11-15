Require Import QubitIso.Quaternion.
Require Import QubitIso.SO3.
Require Import QuantumLib.Matrix.
Require Import QubitIso.Group.

Definition Versor_to_SO3 (v: Versor): SO3.
Proof.
  unfold SO3.
  destruct v as [(((a, b), c), d) norm].
  exists (
    fun row => fun col => 
    match row, col with
    | 0, 0 => RtoC ( a^2 + b ^ 2 + -(c ^ 2) + -(d ^ 2))
    | 0, 1 => RtoC (2*b*c + - 2*a*d)
    | 0, 2 => RtoC (2*b*d + 2*a*c)
    | 1, 0 => RtoC (2*b*c + 2*a*d)
    | 1, 1 => RtoC ( a^2 + -(b^ 2) + c^2 + -(d^2))
    | 1, 2 => RtoC (2*c*d + - 2*a*b)
    | 2, 0 => RtoC (2*b*d + - 2*a*c)
    | 2, 1 => RtoC (2*c*d + 2*a*b)
    | 2, 2 => RtoC (a^2 + -(b^2) + -(c^2) + d^2)
    | _, _ => C0
    end     
  ).
  repeat split.
  3, 4:
      apply pow_eq with _ _ (2%nat) in norm
    ; rewrite Quaternion.norm_squared, pow1 in norm
    ; apply pow_eq with _ _ (2%nat) in norm
    ; replace  (1 ^ 2)%R with 1%R in norm by lra
    ; unfold transpose, Mmult, big_sum, I, C1, C0
    ; by_cell
    ; unfold Cplus
    ; simpl
    ; f_equal
    ; repeat rewrite Rmult_1_r
    ; try rewrite <- norm
    ; lra.
  - show_wf.
  - unfold Real_matrix, Im.
    intros.
    repeat (destruct i, j; try reflexivity).
    1, 3: repeat (destruct j; try reflexivity).
    all: repeat (destruct i; try reflexivity).
  - unfold MatrixAux.d3_det.
    simpl.
    repeat rewrite Rmult_1_r.
    apply pow_eq with _ _ (2%nat) in norm.
    rewrite Quaternion.norm_squared, pow1 in norm.
    apply pow_eq with _ _ (3%nat) in norm.
    replace (1 ^ 3)%R with 1%R in norm by lra.
    unfold C1.
    unfold Cmult, Cplus. simpl.
    f_equal.
    + rewrite <- norm. lra.
    + lra.
Defined.

Lemma Versor_SO3_hom_mul: forall v1 v2: Versor,
  Versor_to_SO3 (v1 ** v2) *= (Versor_to_SO3 v1) × (Versor_to_SO3 v2).
Proof.
  intros.
  unfold SO3_equiv, sigma_proj1_equiv, proj1_sig.
  destruct v1 as [(((a1, b1), c1), d1) E1].
  destruct v2 as [(((a2, b2), c2), d2) E2].
  unfold Versor_to_SO3, Vmul, Mmult.
  simpl.
  by_cell; lca.
Qed.

#[export] Instance Versor_Homomorphism_SO3: 
  @GroupHomomorphism
    Versor
    SO3
    Vmul
    SO3_mul
    versor_equiv
    SO3_equiv
  := 
{
    hom_left_group  := Versor_is_Group
  ; hom_right_group := SO3_is_Group
  ; hom_f           := Versor_to_SO3
  ; hom_mul         := Versor_SO3_hom_mul
}.

(* TODO could use some more work here to show this is really the kernel, surjective, etc. *)

Lemma Versor_double_covers_SO3: forall v: Versor, Versor_to_SO3 v *= Versor_to_SO3 (Vopp v).
Proof.
  intros.
  unfold SO3_equiv, sigma_proj1_equiv, proj1_sig.
  destruct v as [(((a1, b1), c1), d1) E1].
  by_cell; lca.
Qed.  
