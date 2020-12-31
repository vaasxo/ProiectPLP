Inductive Var := m | n | i | j | x | y | a | b.
Scheme Equality for Var.

Require Export Coq.Strings.String.

Open Scope string_scope.

Inductive Expressin :=
| anum : nat -> Exp
| avar : Var -> Exp
| aplus : Exp -> Exp -> Exp
| amul : Exp -> Exp -> Exp
| btrue : Exp
| bfalse : Exp
| blessthan : Exp -> Exp -> Exp
| bnot : Exp -> Exp
| band : Exp -> Exp -> Exp.