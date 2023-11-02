Declare Scope group_scope.
Delimit Scope group_scope with G.
Open Scope group_scope.

Reserved Notation "x * y" (at level 40, left associativity).
Class group_binop (G : Type) := group_op : G -> G -> G.
Infix "*" := group_op: group_scope.

(* TODO this needs to restrict to equivalence relations *)
Reserved Notation "x == y" (at level 70).
Class group_eq_rel (G : Type) := group_eq : G -> G -> Prop.
Infix "==" := group_eq: group_scope.

Class PredicateGroup (G: Type) (op: group_binop G) (pred: G -> Prop) (group_eq: group_eq_rel G): Type := {
        id : G
      ; inverse: G -> G
      ; id_left: forall x, pred x -> id * x == x
      ; id_right: forall x, pred x -> x * id == x
      ; assoc: forall x y z, pred x -> pred y -> pred z -> (x * y) * z == x * (y * z)
      ; right_inv: forall x, pred x -> x * (inverse x) == id
}.
