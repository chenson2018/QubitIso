Require Import Relations.
Require Import Setoid.
Require Import Morphisms.

Section inverses.

Variables A B : Type.

Variable Arel: relation A.
Variable Brel: relation B.

Variable A_Eq: Equivalence Arel.
Variable B_Eq: Equivalence Brel.

Variable f   : A -> B.
Variable f_rw   : Proper (Arel ==> Brel) f.

#[local] Instance f_morphism: Proper (Arel ==> Brel) f.
Proof. apply f_rw. Qed.

#[local] Instance A_rw: Equivalence Arel.
Proof. apply A_Eq. Qed.

#[local] Instance B_rw: Equivalence Brel.
Proof. apply B_Eq. Qed.

Definition injection := forall a1 a2, Brel (f a1) (f a2) -> Arel a1 a2.
Definition left_inverse := exists finv: B -> A, Proper (Brel ==> Arel) finv /\ forall a: A, Arel (finv (f a)) a.

Definition surjection := forall b, exists a, Brel (f a) b.
Definition right_inverse := exists finv: B -> A, forall b: B, Brel (f (finv b)) b.

Lemma injection_left_inverse: left_inverse -> injection.
Proof.
  unfold left_inverse, injection.
  intros.
  destruct H as [finv [finv_rw l_inv]].
  assert (H: Arel (finv (f a1)) a1) by (apply l_inv).
  rewrite <- H.
  rewrite H0.
  rewrite l_inv.
  reflexivity.
Qed.

Lemma surjection_right_inverse: right_inverse -> surjection.
Proof.
  unfold right_inverse, surjection.
  intros.
  destruct H as [finv H'].
  exists (finv b).
  apply H'.
Qed.

Definition bijection := surjection /\ injection.

End inverses.
