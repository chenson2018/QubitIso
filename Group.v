Require Import Relations.

Declare Scope group_scope.
Delimit Scope group_scope with G.
Open Scope group_scope.

Reserved Notation "x • y" (at level 40, left associativity).
Class group_binop (G : Type) := group_op : G -> G -> G.
Infix "•" := group_op: group_scope.

Reserved Notation "x •= y" (at level 70).
Class group_eq_rel (G : Type) := group_eq : relation G.
Infix "•=" := group_eq: group_scope.

(* equivalence relations *)

(* TODO check if these are in the standard library *)

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

Class Group {G: Type}: Type := {
        id : G
      ; inverse: G -> G
      ; op: group_binop G
      ; rel: group_eq_rel G
      ; rel_equiv: equiv G rel
      ; id_left {x}: id • x •= x
      ; id_right {x}: x • id •= x
      ; assoc {x y z}: (x • y) • z •= x • (y • z)
      ; right_inv {x}: x • (inverse x) •= id
}.

(* TODO still having trouble inferring the operations *)

Class GroupHomomorphism
  {G H: Type} 
  {Gop: group_binop G}
  {Hop: group_binop H}
  {Grel: group_eq_rel G}
  {Hrel: group_eq_rel H}
: Type 
:= {
    hom_left_group: @Group G
  ; hom_right_group: @Group H
  ; hom_f: G -> H
  ; hom_mul {a b}: hom_f (a • b) •= hom_f a • hom_f b
}.

(* TODO reorganizing so that we don't have to access inside hom could make this more readable *)

Class GroupIsomorphism
  {G H: Type} 
  {Gop: group_binop G}
  {Hop: group_binop H}
  {Grel: group_eq_rel G}
  {Hrel: group_eq_rel H}
: Type 
:= {
    hom: @GroupHomomorphism G H _ _ _ _
  ; iso_f_inv: H -> G
  ; iso_left_inv {g: G}: 
      iso_f_inv (hom.(hom_f) g) •= g
  ; iso_right_inv {h: H}: 
      hom.(hom_f) (iso_f_inv h) •= h 
}.
