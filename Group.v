Require Import Relations.
Require Import Setoid.
Require Import Morphisms.

Declare Scope group_scope.
Delimit Scope group_scope with G.
Open Scope group_scope.

(* equivalence relations *)

Lemma eq_equiv {X}: equiv X eq.
Proof.
  unfold equiv.
  unfold transitive, symmetric.
  repeat split.
  all: intros; subst; reflexivity.
Qed.    

Definition sigma_proj1_equiv 
  {X: Type} 
  {A: X -> Prop} 
  {rel: relation X}
  (e: equiv X rel)
  (s1 s2: sig A) 
  : Prop 
:= rel (proj1_sig s1) (proj1_sig s2).

Lemma sigma_proj1_equiv_equiv 
  {X: Type} 
  {A: X -> Prop} 
  {rel: relation X} 
  (e: equiv X rel)
  : equiv (sig A) (sigma_proj1_equiv e).
Proof.
  unfold equiv.
  destruct e as [R [T S]].
  unfold reflexive, transitive, symmetric, sigma_proj1_equiv in *.
  repeat split; intros.
  - apply R.
  - apply (T _ _ _ H H0).
  - apply S. assumption.
Qed.

(* these are to use with `Add Parametric` *)

Lemma sigma_proj1_refl
  {X: Type} 
  {A: X -> Prop} 
  {rel: relation X} 
  (e: equiv X rel)
  : reflexive (sig A) (sigma_proj1_equiv e).
Proof.
  assert (H: equiv (sig A) (sigma_proj1_equiv e)).
  { apply sigma_proj1_equiv_equiv. }
  destruct H as [r [t s]].
  assumption.
Qed.  

Lemma sigma_proj1_sym
  {X: Type} 
  {A: X -> Prop} 
  {rel: relation X} 
  (e: equiv X rel)
  : symmetric (sig A) (sigma_proj1_equiv e).
Proof.
  assert (H: equiv (sig A) (sigma_proj1_equiv e)).
  { apply sigma_proj1_equiv_equiv. }
  destruct H as [r [t s]].
  assumption.
Qed.  

Lemma sigma_proj1_trans
  {X: Type} 
  {A: X -> Prop} 
  {rel: relation X} 
  (e: equiv X rel)
  : transitive (sig A) (sigma_proj1_equiv e).
Proof.
  assert (H: equiv (sig A) (sigma_proj1_equiv e)).
  { apply sigma_proj1_equiv_equiv. }
  destruct H as [r [t s]].
  assumption.
Qed.

(* groups *)

Section groups.

Variables G: Type.
Variables Gop: G -> G -> G.
Variable Grel: relation G.

Infix "•=" := Grel (at level 70): group_scope.
Infix "•" := Gop (at level 40, left associativity): group_scope.

Infix "•=" := Grel (at level 70): group_scope.
Class Group := {
        id : G
      ; inverse: G -> G
      ; rel_equiv: equiv G Grel
      ; id_left: forall x: G, (id • x) •= x
      ; id_right: forall x: G, (x • id) •= x
      ; assoc: forall x y z: G, (x • y) • z •= x • (y • z)
      ; right_inv: forall x: G, x • (inverse x) •= id
}.

End groups.

Class GroupHomomorphism G H
  (Gop: G -> G -> G) 
  (Hop: H -> H -> H) 
  (Grel: relation G)
  (Hrel: relation H)
  (hom_f: G -> H)
: Type 
:= {
    hom_left_group: Group G Gop Grel
  ; hom_right_group: Group H Hop Hrel
  ; hom_mul {a1 a2}: Hrel
                      (hom_f (Gop a1 a2)) 
                      (Hop (hom_f a1) (hom_f a2))
}.

Class GroupIsomorphism G H
  (Gop: G -> G -> G) 
  (Hop: H -> H -> H) 
  (Grel: relation G)
  (Hrel: relation H)
  (hom_f: G -> H)
  (iso_f_inv: H -> G)
: Type 
:= {
    hom: GroupHomomorphism G H Gop Hop Grel Hrel hom_f
  ; iso_left_inv {g: G}: 
      Grel (iso_f_inv (hom_f g)) g
  ; iso_right_inv {h: H}: 
      Hrel (hom_f (iso_f_inv h)) h 
}.

Section morphism_properties.

Variables G H : Type.

Variable Grel: relation G.
Variable Hrel: relation H.

Variable G_Eq: Equivalence Grel.
Variable H_Eq: Equivalence Hrel.

Variable f: G -> H.
Variable finv: H -> G.

Variable f_rw   : Proper (Grel ==> Hrel) f.
Variable finv_rw: Proper (Hrel ==> Grel) finv.

Variables Gop: G -> G -> G.
Variables Hop: H -> H -> H.

Infix "=G" := Grel (at level 70): group_scope.
Infix "=H" := Hrel (at level 70): group_scope.
Infix "*G" := Gop (at level 40, left associativity): group_scope.
Infix "*H" := Hop (at level 40, left associativity): group_scope.

Variable Gop_compat: forall g1 g2 g1' g2': G, 
  g1 =G g1' ->
  g2 =G g2' ->
  g1 *G g2 =G g1' *G g2'.

Add Parametric Morphism: Gop
  with signature Grel ==> Grel ==> Grel as Gop_mor.
Proof. intros. apply Gop_compat; easy. Qed.

Variable Hop_compat: forall h1 h2 h1' h2': H, 
  h1 =H h1' ->
  h2 =H h2' ->
  h1 *H h2 =H h1' *H h2'.

Add Parametric Morphism: Hop
  with signature Hrel ==> Hrel ==> Hrel as Hop_mor.
Proof. intros. apply Hop_compat; easy. Qed.

Lemma Iso_to_Hom_inv:
  GroupIsomorphism  G H Gop Hop Grel Hrel f finv ->
  GroupHomomorphism H G Hop Gop Hrel Grel finv.
Proof.
  intros.
  destruct X.
  apply Build_GroupHomomorphism; destruct hom0.
  - assumption.
  - assumption.
  - intros.
    (* for my sanity *)
    rename a1 into h1.
    rename a2 into h2.
    assert (G1: exists g1, finv h1 =G g1).
    { exists (finv h1). reflexivity. }
    assert (G2: exists g2, finv h2 =G g2).
    { exists (finv h2). reflexivity. }
    destruct G1 as [g1 G1].
    destruct G2 as [g2 G2].
    assert (H1: f g1 =H h1).
    { rewrite <- G1. apply iso_right_inv0. }
    assert (H2: f g2 =H h2).
    { rewrite <- G2. apply iso_right_inv0. }
    assert (K: f (g1 *G g2) =H h1 *H h2).
    { rewrite hom_mul0, H1, H2. reflexivity. }
    rewrite <- K.
    rewrite iso_left_inv0, G1, G2. 
    reflexivity.
Qed.

End morphism_properties.

Section hom_trans.

Variables A B C : Type.

Variable Arel: relation A.
Variable Brel: relation B.
Variable Crel: relation C.

Variable A_Eq: Equivalence Arel.
Variable B_Eq: Equivalence Brel.
Variable C_Eq: Equivalence Crel.

Variable AtoB: A -> B.
Variable BtoC: B -> C.

Variables Aop: A -> A -> A.
Variables Bop: B -> B -> B.
Variables Cop: C -> C -> C.

Infix "=A" := Arel (at level 70): group_scope.
Infix "*A" := Aop (at level 40, left associativity): group_scope.
Infix "=B" := Brel (at level 70): group_scope.
Infix "*B" := Bop (at level 40, left associativity): group_scope.
Infix "=C" := Crel (at level 70): group_scope.
Infix "*C" := Cop (at level 40, left associativity): group_scope.

Variable BtoC_rw   : Proper (Brel ==> Crel) BtoC.

Lemma GroupHomomorphism_trans:
  GroupHomomorphism A B Aop Bop Arel Brel AtoB ->
  GroupHomomorphism B C Bop Cop Brel Crel BtoC ->
  GroupHomomorphism A C Aop Cop Arel Crel (fun a => BtoC (AtoB a)).
Proof.
  intros Hom_A_B Hom_B_C.
  destruct Hom_A_B.
  destruct Hom_B_C.
  apply Build_GroupHomomorphism.
  - assumption.
  - assumption.
  - intros.
    specialize hom_mul1 with (AtoB a1) (AtoB a2).
    rewrite <- hom_mul1.
    specialize hom_mul0 with a1 a2.
    rewrite <- hom_mul0.
    reflexivity.
Qed.

End hom_trans.
