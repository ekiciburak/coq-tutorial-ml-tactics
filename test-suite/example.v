Require Import Tutorial.Theory.

Require Import BinNums Coq.ZArith.ZArith.

Open Scope Z_scope.

Goal 15%Z = -15340000.
Proof. reflect_Z. simpl. Abort.

(* example 1 *)
Goal forall a b, a + b = 30.
Proof.  intros. reflect_Z. simpl. Abort.

(* example 2 *)
Goal forall a b c, a + b + 1 + c <= -15.
Proof.  intros. reflect_Z. simpl. Abort.

(* example 3 *)
Goal forall a b, a + b + 1 <= a.
Proof.  intros. reflect_Z. simpl. Abort.
