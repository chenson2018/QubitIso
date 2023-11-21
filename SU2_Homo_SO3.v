Require Import QubitIso.Group.
Require Import QubitIso.Versor_Homo_SO3.
Require Import QubitIso.SU2_Iso_Versor.
Require Import QubitIso.SU2.
Require Import QubitIso.SO3.
Require Import QubitIso.Quaternion.
Require Import QuantumLib.Matrix.
Require Import QubitIso.MatrixAux.
Require Import Setoid.

Theorem SU2_Homomorphism_SO3:
  GroupHomomorphism
    SU2
    SO3
    SU2_mul
    SO3_mul
    SU2_equiv
    SO3_equiv
    (fun U => Versor_to_SO3 (SU2_to_Versor U)).
Proof.
  apply GroupHomomorphism_trans with versor_equiv Vmul.
  - apply (sigma_proj1_rel_equivalence eq_equivalence).
  - apply (sigma_proj1_rel_equivalence mat_equiv_equivalence).
  - unfold Morphisms.Proper, Morphisms.respectful.
    intros.
    unfold versor_equiv, SO3_equiv, sigma_proj1_rel, proj1_sig in *.
    destruct x as [(((a1, b1), c1), d1) E1].
    destruct y as [(((a2, b2), c2), d2) E2].
    by_cell; inversion H; subst; reflexivity.
  - apply SU2_Iso_to_hom.
  - apply Versor_Homomorphism_SO3.
Qed.
