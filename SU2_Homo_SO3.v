Require Import QubitIso.SU2_Iso_Versor.
Require Import QubitIso.Versor_Homo_SO3.
Require Import QubitIso.SU2.
Require Import QubitIso.SO3.
Require Import QubitIso.Group.
Require Import QubitIso.Quaternion.
Require Import QuantumLib.Matrix.

(* TODO make this proof use composition of homomorphisms *)

Definition SU2_to_SO3 (su2: SU2) : SO3.
Proof.
  apply (Versor_to_SO3 (SU2_to_Versor su2)).
Defined.

Definition SU2_SO3_hom_mul: forall su2_a su2_b : SU2,
  SU2_to_SO3 (su2_a × su2_b) *= (SU2_to_SO3 su2_a) × (SU2_to_SO3 su2_b).
Proof.
Admitted.

#[export] Instance SU2_Homomorphism_SO3 : 
  @GroupHomomorphism 
    SU2
    SO3
    SU2_mul
    SO3_mul
    SU2_equiv
    SO3_equiv
  := 
{
    hom_left_group  := SU2_is_Group
  ; hom_right_group := SO3_is_Group
  ; hom_f           := SU2_to_SO3
  ; hom_mul         := SU2_SO3_hom_mul
}.
