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

(* TODO make isomorphism depend on homomorphism *)

Class GroupIsomorphism
  {G H: Type} 
  {Gop: group_binop G}
  {Hop: group_binop H}
  {Grel: group_eq_rel G}
  {Hrel: group_eq_rel H}
  {Heq: equiv H Hrel}
: Type 
:= {
    iso_left_group: @PredicateGroup G
  ; iso_right_group: @PredicateGroup H
  ; iso_f: G -> H
  ; iso_mul {a b}:
      iso_left_group.(pred) a ->
      iso_left_group.(pred) b ->
      iso_f (a • b) •= iso_f a • iso_f b
  ; iso_f_closed {g}: 
      iso_left_group.(pred) g -> 
      iso_right_group.(pred) (iso_f g)
  ; iso_bijection {x x'}: 
      iso_left_group.(pred) x  ->
      iso_left_group.(pred) x' ->
      iso_f x •= iso_f x' -> x •= x'
}.
