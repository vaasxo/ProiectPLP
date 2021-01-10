Require Export Coq.Strings.String.
From Coq Require Import Lists.List.
Require Import Ascii.
From Coq Require Import Strings.String.
Require Import Strings.String.
Open Scope string_scope.
Scheme Equality for string.

(*SYNTAX*)

(*Arithmetic expressions*)

Inductive Exp :=
| anum : nat -> Exp
| avar : string -> Exp
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
| beq : Exp -> Exp -> Exp
| bnot : Exp -> Exp
| band : Exp -> Exp -> Exp
| bor : Exp -> Exp -> Exp.

Coercion anum : nat >-> Exp.
Coercion avar : string >-> Exp.

Notation "A +' B" := (aplus A B) (at level 50).
Notation "A -' B" := (aminus A B) (at level 50).
Notation "A *' B" := (amul A B) (at level 46).
Notation "A /' B" := (adiv A B) (at level 46).
Notation "A <' B" := (bless A B) (at level 53).
Notation "A >' B" := (bgreat A B) (at level 53).
Notation "A <=' B" := (bleq A B) (at level 53).
Notation "A >=' B" := (bgeq A B) (at level 53).
Notation "A ==' B" := (beq A B) (at level 53, no associativity).
Notation "'~' A" := (bnot A) (at level 75, right associativity).
Infix "and'" := band (at level 60).
Infix "or'" := bor (at level 60).

Compute 1 +' 2.
Compute "x" +' "y".
Compute 5 -' 3.
Compute "a" -' 7.
Compute 10 *' 100.
Compute 23 *' "b".
Compute 80 /' 5.
Compute "x" /' "y".

Compute 5 <' 7.
Compute "x" >' 10.
Compute 8 <=' "i".
Compute "j" >=' 25.
Compute 6 ==' 6.
Compute "a" ==' "b".
Compute btrue ==' 2.

Compute ~btrue.
Compute ~(btrue) and' bfalse.
Compute 5 or' 0.
Compute ~(btrue or' 0) and' "x".  

(*functions*)

Inductive list_variable : Type :=
| null
| cons (s : string) (l : list_variable).

Notation "[]" := null (format "[]") : list_scope.
Notation "[ A ]" := (cons A null) : list_scope.
Notation "[ A , B , .. , C ]" := (cons A (cons B .. (cons C null) ..)) : list_scope.

Inductive Function :=
| function : string -> list_variable -> Function.

Notation "A 'takes' B" := (function A B) (at level 50).

Compute "cmmdc" takes ["x", "y"].

Compute "printWelcome" takes [].

Compute "add1toit" takes ["number"].

(*objects*)

Inductive Object :=
| object : string -> list_variable -> Function -> Object.

Notation "'class' A { B C }" := (object A B C) (at level 200). 

Compute object ("student") (["age","name","grade"]) ("getGrade" takes []).

Compute object ("car") (["make","model","color"]) ("setColor" takes ["color"]).

(*Compute class "car" { ["make", "model", "color"]  "setColor" takes ["color"]}.*)

(*Notation "A.B" := (objval A B)(at level 30).*)

(*Memory*)

Inductive Value :=
| undef : Value
| nat_val : nat -> Value
| bool_val : bool -> Value.

Scheme Equality for Value.

Definition Variabila := string -> nat.
Definition Adresa := nat -> Value.

Variable ValAdresa : nat.

Check(ValAdresa).

(*statements*)

Inductive Stmt :=
| var_declare : string -> Stmt 
| object_declare : string -> Object -> Stmt
| function_declare : Function -> Stmt -> Stmt
| assignment : string -> Exp -> Stmt 
| sequence : Stmt -> Stmt -> Stmt
| ifthenelse : Exp -> Stmt -> Stmt -> Stmt
| ifthen : Exp -> Stmt -> Stmt
| while : Exp -> Stmt -> Stmt.

Notation "'fie' A" := (var_declare A) (at level 90).
Notation "X ::= A" := (assignment X A) (at level 90).
Notation "S ;; S'" := (sequence S S') (at level 93, right associativity).
Notation "A <{ B }>" := (function_declare A B) (at level 90).
Notation "A 'is' B" := (object_declare A B) (at level 90).

Example ex1 :=
fie "c" ;;
"someFunction" takes [ "c" ] <{ "c" ::= 10 }>;;
fie "b" ;;
"c" ::= 10 ;;
"b" ::= "ana"
.
Compute ex1.

Example ex2 :=
fie "obiect" ;;
"obiect" is object ("student") (["age","name","grade"]) ("getGrade" takes []);;
ifthenelse ("a"=='"x") ("a"::=10) ("a"::=1);;
while ("a">='0) ("a"::="a"-'1);;
fie "b";;
ifthen (1) ("b"::=10+'5)
.
Compute ex2.

(*SEMANTICS*)

(*Memory*)

Definition nval (n : Value) : nat :=
match n with
| nat_val n => n
| _ => 0
end.

Definition bval (b : Value) : bool :=
match b with
| bool_val b => b
| _ => false
end.

Definition State : Variabila := fun n => 0.
Definition Values : Adresa := fun n => undef.

Definition updateState (state : Variabila) (s : string) (value : nat) : Variabila :=
  fun s' => 
    if (string_eq_dec s' s)
    then value
    else (state s').

Definition updateValues (values : Adresa) (n : nat) (value : Value) : Adresa :=
  fun n' => 
    if (Nat.eqb n' n)
    then value
    else (values n'). 

Definition is_declared (s : string) (state : Variabila) (values : Adresa) :=
  if (Value_beq (values (state s)) undef)
  then false
  else true.

Compute (updateState State "valAdresa" 0).

(*Exp*)

Fixpoint expEval (e : Exp) (s : Variabila) (v : Adresa) : nat :=
  match e with
  | avar var => nval(v(s var))
  | anum n' => n'
  | btrue => 1
  | bfalse => 0
  | aplus e1 e2 => (expEval e1 s v) + (expEval e2 s v)
  | aminus e1 e2 => (expEval e1 s v) - (expEval e2 s v)
  | amul e1 e2 => (expEval e1 s v) * (expEval e2 s v) 
  | adiv e1 e2 => Nat.div (expEval e1 s v) (expEval e2 s v)
  | bless b1 b2 => if (Nat.ltb (expEval b1 s v) (expEval b2 s v)) then 1 else 0
  | bgreat b1 b2=> if (Nat.ltb (expEval b2 s v) (expEval b1 s v)) then 1 else 0
  | bleq b1 b2=> if (Nat.leb (expEval b1 s v) (expEval b2 s v)) then 1 else 0
  | bgeq b1 b2=> if (Nat.leb (expEval b2 s v) (expEval b1 s v)) then 1 else 0
  | beq b1 b2=> if (Nat.eqb (expEval b1 s v) (expEval b1 s v)) then 1 else 0
  | bnot b' => match (expEval b' s v) with | 0 => 0 | _ => 1 end
  | band b1 b2 => 0
  | bor b1 b2=> if (Nat.eqb (expEval b1 s v) (expEval b2 s v)) then 1 else 0
  end.



