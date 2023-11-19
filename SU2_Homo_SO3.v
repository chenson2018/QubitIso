Require Import QubitIso.Group.
Require Import QubitIso.Versor_Homo_SO3.
Require Import QubitIso.SU2_Iso_Versor.
Require Import QubitIso.SU2.
Require Import QubitIso.SO3.
Require Import QubitIso.Quaternion.
Require Import QuantumLib.Matrix.
Require Import QubitIso.MatrixAux.

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
  - constructor.
    + constructor.
    + apply (sigma_proj1_sym eq_equiv).
    + apply (sigma_proj1_trans eq_equiv).
  - constructor.
    + constructor.
    + apply (sigma_proj1_sym (mat_equiv_equiv 3 3)).
    + apply (sigma_proj1_trans (mat_equiv_equiv 3 3)).
  - unfold Morphisms.Proper, Morphisms.respectful.
    intros.
    unfold versor_equiv, SO3_equiv, sigma_proj1_equiv, proj1_sig in *.
    destruct x as [(((a1, b1), c1), d1) E1].
    destruct y as [(((a2, b2), c2), d2) E2].
    by_cell; inversion H; subst; reflexivity.
  - apply SU2_Iso_to_hom.
  - apply Versor_Homomorphism_SO3.
Qed.
