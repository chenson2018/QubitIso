Require Import Reals.
Require Import Psatz.
Require Import QubitIso.Group.
Require Import Coq.Init.Specif.
Require Import Setoid.

Open Scope R_scope.

Definition Quaternion := (R * R * R * R)%type.

(* useful to have definitions for zero and the basis elements *)

Definition Q0 := (0, 0, 0, 0).
Definition Q1 := (1, 0, 0, 0).
Definition QI := (0, 1, 0, 0).
Definition QJ := (0, 0, 1, 0).
Definition QK := (0, 0, 0, 1).

(* notation for Quaternion multiplication *)

Declare Scope Q_scope.
Delimit Scope Q_scope with Q.
Open Scope Q_scope.
Bind Scope Q_scope with Quaternion.

Reserved Notation "x ** y" (at level 40, left associativity).

(* basic Quaternion operations *)

Definition Qmul (x y: Quaternion): Quaternion.
Proof.
  destruct x as (((a1, b1), c1), d1).
  destruct y as (((a2, b2), c2), d2).
  apply
  (a1 * a2 - b1 * b2 - c1 * c2 - d1 * d2, 
   a1 * b2 + b1 * a2 + c1 * d2 - d1 * c2, 
   a1 * c2 - b1 * d2 + c1 * a2 + d1 * b2, 
   a1 * d2 + b1 * c2 - c1 * b2 + d1 * a2).
Defined.

Infix "**" := Qmul: Q_scope.

Definition Qnorm (x: Quaternion) : R.
Proof.
  destruct x as (((a, b), c), d).
  apply (sqrt( a^2 + b^2 + c^2 + d^2 )).
Defined.

Definition Qconj (x: Quaternion): Quaternion.
Proof.
  destruct x as (((a, b), c), d).
  apply (a, -b, -c, -d).
Defined.

Definition R_to_Q (r: R): Quaternion := (r, 0, 0, 0).

Definition Qinv (x: Quaternion): Quaternion := R_to_Q (1 / (Qnorm x)^2) ** (Qconj x).

(* A couple of useful lemmas for Quaternion operations *)

Lemma scalar_q: forall (l a b c d: R), R_to_Q l ** (a, b, c, d) = (l*a, l*b, l*c, l*d).
Proof.
  intros.
  simpl.
  f_equal.
  f_equal.
  f_equal.
  all: lra.
Qed.  
  
Lemma norm_squared: forall a b c d, (Qnorm (a, b, c, d))^2 = a^2 + b^2 + c^2 + d^2.
intros.
unfold Qnorm.
rewrite pow2_sqrt.
- reflexivity.
- repeat apply Rplus_le_le_0_compat.
  all: apply pow2_ge_0.
Qed.

(* useful lemmas on real numbers *)

Lemma pow_eq: forall x y n, x = y -> x^n = y^n. Proof. intros. subst. lra. Qed.

Lemma Rdiv_diag: forall x, x <> 0 -> x / x = 1.
Proof. now unfold Rdiv; intros r H; rewrite Rinv_r. Qed.

Lemma pow2_distr: forall x y, (x * y)^2 = x^2 * y^2. Proof. intros. lra. Qed.

Lemma times_self: forall x, x * x = x^2. Proof. intros. lra. Qed.

Lemma sqrt_mul_rev: forall z1 z2 z3, 
  0 <= z1 -> 
  0 <= z2 -> 
  z1 * z2 = z3 -> 
  sqrt z1 * sqrt z2 = sqrt z3.
Proof.
  intros. 
  rewrite <- H1.
  rewrite sqrt_mult.
  reflexivity.
  all: assumption.
Qed.

(* properties of Quaternions used in the group definition *)

Lemma Qnorm_distr: forall x y, (Qnorm x) * (Qnorm y) = Qnorm (x ** y).
  intros.
  destruct x as (((a1, b1), c1), d1).
  destruct y as (((a2, b2), c2), d2).
  simpl.
  repeat rewrite Rmult_1_r.
  remember (a1 * a1 + _ + _ +  _) as z1.
  remember (a2 * a2 + _ + _ +  _) as z2.
  remember ((a1 * a2 - _ - _ - _) * _ + _ + _ + _) as z3.
  assert (H': z1 * z2 = z3).
  { subst. lra. } 
  assert (le_z1_z2: 0 <= z1 /\ 0 <= z2).
  {
    split; subst; repeat apply Rplus_le_le_0_compat.
    all: rewrite times_self.
    all: apply pow2_ge_0.
  }
  destruct le_z1_z2.
  apply sqrt_mul_rev; assumption.
Qed.

(* type for unit Quaternion *)

Definition Versor := { q | Qnorm q = 1}.

(* multiplication on Versors, carrying a proof the predicate in preserved *)

Definition Vmul (v1 v2: Versor) : Versor.
Proof.
  destruct v1 as [q1 E1].
  destruct v2 as [q2 E2].
  apply exist with (q1 ** q2).
  rewrite <- Qnorm_distr.
  rewrite E1, E2.
  lra.
Defined.

(* likewise for the inverse *)

Definition Vinv (v1: Versor) : Versor.
Proof.
  destruct v1 as [q1 E1].
  exists (Qinv q1).
  destruct q1 as (((a, b), c), d).
  unfold Qinv, Qconj.
  rewrite E1.
  replace (1 / 1 ^ 2) with 1 by lra.
  rewrite scalar_q.
  repeat rewrite Rmult_1_l.
  rewrite <- E1.
  unfold Qnorm.
  replace ((- b)^2) with (b^2) by lra.
  replace ((- c)^2) with (c^2) by lra.
  replace ((- d)^2) with (d^2) by lra.
  reflexivity.
Defined. 

(* negation, used in the double covering proof *)

Definition Vopp (v: Versor) : Versor.
Proof.
  unfold Versor.
  destruct v as [(((x, y), z), w) norm].
  exists (-x, -y, -z, -w).
  unfold Qnorm in *.
  replace ((- x) ^ 2) with (x ^ 2) by lra.
  replace ((- y) ^ 2) with (y ^ 2) by lra.
  replace ((- z) ^ 2) with (z ^ 2) by lra.
  replace ((- w) ^ 2) with (w ^ 2) by lra.
  assumption.
Defined.

(* Q1 is the identity Versor *)

Definition V1: Versor.
Proof.
  unfold Versor.
  apply exist with Q1.
  unfold Q1. simpl.
  replace (_ + _) with 1 by lra.
  apply sqrt_1.
Defined.  

(* lift Qmul notation *)

Declare Scope V_scope.
Delimit Scope V_scope with V.
Open Scope V_scope.
Bind Scope V_scope with Versor.
Reserved Notation "x ** y" (at level 40, left associativity).
Infix "**" := Vmul: V_scope.

(* equivalence relation for the Versors sigma type *)

Definition versor_equiv (v1 v2 : Versor) : Prop := sigma_proj1_rel eq_equivalence v1 v2.
Reserved Notation "x $= y" (at level 70).
Infix "$=" := versor_equiv: V_scope.

(* proofs of the group properties *)

Lemma Versor_id_left: forall v : Versor, (V1 ** v) $= v.
Proof.
  intros.
  unfold versor_equiv, sigma_proj1_rel, proj1_sig.
  destruct v as [(((a, b), c), d) E].
  simpl.
  repeat f_equal; lra.
Qed.

Lemma Versor_id_right: forall v : Versor, (v ** V1) $= v.
Proof.
  intros.
  unfold versor_equiv, sigma_proj1_rel, proj1_sig.
  destruct v as [(((a, b), c), d) E].
  simpl.
  repeat f_equal; lra.
Qed.

Lemma Versor_assoc: forall v1 v2 v3, v1 ** v2 ** v3 $= v1 ** (v2 ** v3).
Proof.
  intros.
  destruct v1 as [(((a1, b1), c1), d1) E1].
  destruct v2 as [(((a2, b2), c2), d2) E2].
  destruct v3 as [(((a3, b3), c3), d3) E3].
  unfold versor_equiv, sigma_proj1_rel.
  simpl.
  f_equal.
  f_equal.
  f_equal.
  all: lra.
Qed.

Lemma Versor_right_inv: forall v, v ** (Vinv v) $= V1.
Proof.
  intros.
  destruct v as [(((a, b), c), d) E].
  unfold versor_equiv, sigma_proj1_rel.
  simpl.
  repeat rewrite Rmult_1_r.
  repeat rewrite Rmult_0_l.
  unfold Qnorm in E.
  replace (sqrt _) with 1.
  - replace (1 / (1 * 1)) with 1 by lra.
    repeat rewrite Rmult_1_l.
    repeat rewrite Rminus_0_r.
    repeat rewrite Rplus_0_r.
    unfold Q1.
    repeat f_equal.
    apply pow_eq with _ _ (2%nat) in E.
    rewrite pow1, pow2_sqrt in E.
    rewrite <- E. lra.
    repeat apply Rplus_le_le_0_compat.
    all: try lra.
    all: apply pow2_ge_0.
  - rewrite <- E. 
    simpl. 
    repeat rewrite Rmult_1_r.
    reflexivity.
Qed.

(* group instance *)

#[export] Instance Versor_is_Group : Group Versor Vmul versor_equiv := {
    id             := V1
  ; inverse        := Vinv
  ; rel_equiv      := sigma_proj1_rel_equivalence eq_equivalence
  ; id_left        := Versor_id_left
  ; id_right       := Versor_id_right
  ; assoc          := Versor_assoc
  ; right_inv      := Versor_right_inv
}.
