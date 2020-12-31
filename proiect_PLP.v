Inductive Var := m | n | i | j | x | y | a | b.
Scheme Equality for Var.

Require Export Coq.Strings.String.

Open Scope string_scope.

Inductive Value :=
| undef : Value
| nat_val : nat -> Value
| bool_val : bool -> Value
| string_val : string -> Value
| reference : nat -> Value.
Scheme Equality for Value.

Inductive Typ : Type := Bool | Nat | String.

Definition State := Var -> Value.
Definition sigma1 : State := fun x => undef.

Definition update (sigma : State)
           (x : Var) (v : nat) : State :=
  fun y =>
    if (Var_eq_dec y x)
    then nat_val(v)
    else (sigma y).

Definition is_declared (x : Var) (sigma : State) :=
  if (Value_beq (sigma x) undef)
  then false
  else true.

Definition object : Type := string -> option Value.
Definition heap : Type := nat -> option object.

Definition object_ok (o : object) (h : heap) : Prop :=
  forall (s : string) (ref : nat),
    o s = Some (reference ref) ->
    exists obj, h ref = Some obj.

Definition recursive (v : Typ) (s : string) (stmt : stmt) : Value :=
| (* if the stmt returns a value, return it *)
| (* else*)
| (* run the function with the new statement*)

Inductive Exp :=
| anum : nat -> Exp
| avar : Var -> Exp
| aplus : Exp -> Exp -> Exp
| aminus : Exp -> Exp -> Exp
| amul : Exp -> Exp -> Exp
| adiv : Exp -> Exp -> Exp
| btrue : Exp
| bfalse : Exp
| bless : Exp -> Exp -> Exp
| bgreat : Exp -> Exp -> Exp
| bleq : Exp -> Exp -> Exp
| bgeq : Exp -> Exp -> Exp
| bnot : Exp -> Exp
| band : Exp -> Exp -> Exp
| bor : Exp -> Exp -> Exp
| beq : Exp -> Exp -> Exp.

Coercion anum : nat >-> Exp.
Coercion avar : Var >-> Exp.

Notation "A +' B" := (aplus A B) (at level 50).
Notation "A -' B" := (aminus A B) (at level 50).
Notation "A *' B" := (amul A B) (at level 46).
Notation "A /' B" := (adiv A B) (at level 46).
Notation "A <' B" := (bless A B) (at level 53).
Notation "A >' B" := (bgreat A B) (at level 53).
Notation "A <=' B" := (bleq A B) (at level 53).
Notation "A >=' B" := (bgeq A B) (at level 53).