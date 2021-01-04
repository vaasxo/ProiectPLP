(* Variables and value types definition *)

Inductive Var := i | j | x | y | a | b.
Scheme Equality for Var.

Require Export Coq.Strings.String.

Require Import   Ascii.

Open Scope string_scope.

Inductive Value :=
| undef : Value
| nat_val : nat -> Value
| bool_val : bool -> Value
| string_val : string -> Value
| reference : nat -> Value.
Scheme Equality for Value.

Inductive Typ : Type := Bool | Int | String'.

(* Defining the environment *)

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

(* OOP stuff *)

(*Definition object : Type := string -> option Value.
Definition heap : Type := nat -> option object.

Definition object_ok (o : object) (h : heap) : Prop :=
  forall (s : string) (ref : nat),
    o s = Some (reference ref) ->
    exists obj, h ref = Some obj.*)

Record student : Set := 
createStudent 
{
  id_s    : nat;
  name_s  : string;
  grade : nat
}.

Record teacher : Set := 
createTeacher
{
  id_t    : nat;
  name_t  : string;
  course : string
}.

Inductive person : Set :=
| Student : student -> person
| Teacher : teacher -> person.

Coercion Student : student >-> person.
Coercion Teacher : teacher >-> person.

Definition get_age (p : person) : nat :=
match p with
| Student s => 20
| Teacher t => 38
end.

Definition get_grade (p : person) : option nat :=
match p with
| Student s => Some (grade s)
| _ => None
end.

Definition Radu := createStudent 1 "Radu" 8.
Definition Cristi := createStudent 2 "Cristi" 10.
Definition Andrei := createTeacher 1 "Andrei" "PLP".

Check get_grade Radu.

Compute get_grade Radu.

Check get_age Radu.

Compute get_age Radu.

Check get_age (Andrei).

Compute get_age (Andrei).

(*atoi*)

Definition num_of_ascii (c : ascii) : option nat :=
 match c with
| Ascii false false false false true true false false => Some 0
| Ascii true false false false true true false false => Some 1
| Ascii false true false false true true false false => Some 2
| Ascii true true false false true true false false => Some 3
| Ascii false false true false true true false false => Some 4
| Ascii true false true false true true false false => Some 5
| Ascii false true true false true true false false => Some 6
| Ascii true true true false true true false false => Some 7
| Ascii false false false true true true false false => Some 8
| Ascii true false false true true true false false => Some 9
| _ => None
end.

Definition ascii_of_num (n : nat) : option ascii :=
 match n with
| 0 => Some (Ascii false false false false true true false false)
| 1 => Some (Ascii true false false false true true false false)
| 2 => Some (Ascii false true false false true true false false)
| 3 => Some (Ascii true true false false true true false false)
| 4 => Some (Ascii false false true false true true false false)
| 5 => Some (Ascii true false true false true true false false)
| 6 => Some (Ascii false true true false true true false false)
| 7 => Some (Ascii true true true false true true false false)
| 8 => Some (Ascii false false false true true true false false)
| 9 => Some (Ascii true false false true true true false false)
| _ => None
end.

Fixpoint string_rev (s : string) : string :=
 match s with
 | EmptyString => EmptyString
 | String c rest => append (string_rev rest) (String c EmptyString)
end.

(*Fixpoint string_of_num_rec (n : nat) : option string :=
match n with
| 0 => Some "0"
| n => match (ascii_of_num (n%10)), (ascii_of_num (n/10)) with
          | Some n, Some m => Some (append (String n) (String m EmptyString))
          | _, _ => None
          end
end.*)

Fixpoint num_of_string_rec (s : string) : option nat :=
match s with
| EmptyString => Some 0
| String c rest => 
       match (num_of_ascii c), (num_of_string_rec rest) with
          | Some n, Some m => Some (n + 10 * m)
          | _ , _ => None
       end
end.

Definition string_to_nat (s : string) : nat := 
match num_of_string_rec (string_rev s) with
| Some n => n
| None => 0
end.

(*Definition nat_to_string (n : nat) : string :=
match string_of_num_rec n with
| Some s => s
| None => EmptyString
end.*)

Notation "atoi( X )" := (string_to_nat X) (at level 90).

Check atoi("123").

Compute atoi("123").


(* Expressions *)

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

Check 2 +' 2.
Check 2 +' btrue.
Check (band 2 2).

(* Statements *)

Inductive Stmt :=
| decl : Var -> Stmt 
| skip : Stmt
| assignment : Var -> Exp -> Stmt
| sequence : Stmt -> Stmt -> Stmt
| ifthenelse : Exp -> Stmt -> Stmt -> Stmt
| ifthen : Exp -> Stmt -> Stmt
| while : Exp -> Stmt -> Stmt
| recursive : Typ -> string -> Exp -> Stmt -> Stmt
| classStudent : Exp -> string -> Exp -> Stmt
| classTeacher : Exp -> string -> string -> Stmt. 

Notation "X =' A" := (assignment X A) (at level 50).
Notation "S1 ;; S2" := (sequence S1 S2) (at level 90).
Notation "if ( A ) B" := (ifthen A B) (at level 90).
Notation "if ( A ) B else C" := (ifthenelse A B C) (at level 90).

Check x =' 12 ;; y =' 13.
Check (recursive Bool "Function" x (x =' 12 ;; y =' 13)).
Check (classTeacher 3 "Andrei" "PLP").

(* Recursive functions - will (should) work after implementing semantics for stmt *)

(*Definition recursive (t : Typ) (s : string) (stmt : Stmt) : Value :=
match (eval_stmt stmt) with
| t x => x
| stmt' => (recursive v s stmt')
end.*)




