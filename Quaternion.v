Require Export Reals.
Require Import Psatz.
Require Import QubitIso.Group.

Definition Quaternion := (R * R * R * R)%type.

(* useful to have definitions for zero and the basis elements *)

Open Scope R_scope.

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

Definition Qmul (x y: Quaternion): Quaternion :=
  match x with
  | (a1, b1, c1, d1) => 
    match y with 
    | (a2, b2, c2, d2) => 
        (a1 * a2 - b1 * b2 - c1 * c2 - d1 * d2, 
         a1 * b2 + b1 * a2 + c1 * d2 - d1 * c2, 
         a1 * c2 - b1 * d2 + c1 * a2 + d1 * b2, 
         a1 * d2 + b1 * c2 - c1 * b2 + d1 * a2)
    end
  end.

Infix "**" := Qmul: Q_scope.

Definition Qnorm (x: Quaternion) : R := 
  match x with
  | (a, b, c, d) => sqrt( a^2 + b^2 + c^2 + d^2 )
  end.

Definition Qconj (x: Quaternion): Quaternion :=
  match x with
  | (a, b, c, d) => (a, -b, -c, -d)
  end.

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

(* Proofs in the Quaternions of group properties *)

Lemma Q_assoc: forall (x y z: Quaternion), (x ** y) ** z = x ** (y ** z).
Proof.
  intros.
  destruct x as (((a1, b1), c1), d1).
  destruct y as (((a2, b2), c2), d2).
  destruct z as (((a3, b3), c3), d3).
  simpl.
  f_equal.
  f_equal.
  f_equal.
  all: lra.
Qed.

Lemma Q_right_inv: forall x, (Qnorm x)^2 <> 0 -> x ** (Qinv x) = Q1.
Proof.
  unfold Q0, Q1, Qinv.
  intros.
  destruct x as (((a, b), c), d).
  rewrite norm_squared.
  unfold Qconj.
  rewrite scalar_q.
  remember (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2) as n2.
  simpl.
  repeat f_equal; try lra.
  replace (_ - _ - _ - _) with (a^2 / n2 + b^2 / n2 + c^2 / n2 + d^2 / n2).
  - repeat (rewrite <- Rdiv_plus_distr).
    subst.
    rewrite norm_squared in H.
    apply Rdiv_diag.
    assumption.
  - lra.
Qed.

Lemma Q_id_left: forall x, Q1 ** x = x.
Proof.
  intros.
  unfold Q1.
  destruct x as (((a, b), c), d).
  simpl.
  repeat f_equal; lra.
Qed.  
  
Lemma Q_id_right: forall x, x ** Q1 = x.
Proof.
  intros.
  unfold Q1.
  destruct x as (((a, b), c), d).
  simpl.
  repeat f_equal; lra.
Qed. 

(* type for unit Quaternion *)

Inductive Versor: Quaternion -> Prop := 
  | unit: forall x, Qnorm x = 1 -> Versor x.

(* extend the Quaternion group proofs to Versors, mostly trivial except for inverse *)

Lemma Versor_id_left: forall x : Quaternion, Versor x -> Q1 ** x = x.
Proof. intros. apply Q_id_left. Qed.  

Lemma Versor_id_right: forall x : Quaternion, Versor x -> x ** Q1 = x.
Proof. intros. apply Q_id_right. Qed.  

Lemma Versor_assoc: forall x y z, Versor x -> Versor y -> Versor z -> x ** y ** z = x ** (y ** z).
Proof. intros. apply Q_assoc. Qed.

Lemma Versor_right_inv: (forall x : Quaternion, Versor x -> x ** Qinv x = Q1).
Proof.
  intros.
  destruct H.
  apply Q_right_inv.
  unfold not. intros.
  apply pow_eq with _ _ (2%nat) in H.
  rewrite pow1 in H.
  rewrite H in H0.
  apply R1_neq_R0.
  assumption.
Qed.

Global Program Instance Versor_is_Group : PredicateGroup Quaternion Qmul Versor eq := {
    id        := Q1
  ; inverse   := Qinv
  ; id_left   := Versor_id_left
  ; id_right  := Versor_id_right
  ; assoc     := Versor_assoc
  ; right_inv := Versor_right_inv
}.
