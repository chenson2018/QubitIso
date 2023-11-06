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

(* this has to be in the standard library somewhere, but I couldn't find it... *)
Lemma eq_equiv {X}: equiv X eq.
Proof.
  unfold equiv.
  unfold transitive, symmetric.
  repeat split.
  all: intros; subst; reflexivity.
Qed.    

Class PredicateGroup {G: Type}: Type := {
        id : G
      ; inverse: G -> G
      ; pred: G -> Prop
      ; op: group_binop G
      ; rel: group_eq_rel G
      ; rel_equiv: equiv G rel
      ; id_left {x}: pred x -> id • x •= x
      ; id_right {x}: pred x -> x • id •= x
      ; assoc {x y z}: pred x -> pred y -> pred z -> (x • y) • z •= x • (y • z)
      ; right_inv {x}: pred x -> x • (inverse x) •= id
      ; op_closed {x y}: pred x -> pred y -> pred (x • y)
      ; inverse_closed {x}: pred x -> pred (inverse x)
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
    hom_left_group: @PredicateGroup G
  ; hom_right_group: @PredicateGroup H
  ; hom_f: G -> H
  ; hom_mul {a b}:
      hom_left_group.(pred) a ->
      hom_left_group.(pred) b ->
      hom_f (a • b) •= hom_f a • hom_f b
  ; hom_f_closed {g}: 
      hom_left_group.(pred) g -> 
      hom_right_group.(pred) (hom_f g)
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
      hom.(hom_left_group).(pred) g ->
      iso_f_inv (hom.(hom_f) g) •= g
  ; iso_right_inv {h: H}: 
      hom.(hom_right_group).(pred) h ->
      hom.(hom_f) (iso_f_inv h)  •= h 
  ; iso_f_inv_closed {h: H}:
      hom.(hom_right_group).(pred) h ->
      hom.(hom_left_group).(pred) (iso_f_inv h)
}.
