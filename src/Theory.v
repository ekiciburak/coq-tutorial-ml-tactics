
(** * Introduction

   The goal of this plugin is to reify concrete terms of type [nat]
   to a language of abstract terms of type [arith]. ([arith] is an
   inductive data-type that represents reified terms of type [nat].)
   This allows to use Barendredgt's so-called 2-level approach.  *)

Require Import Arith BinNums.

(** The abstract language of terms of type [nat] (restricted to [plus],
[O], [S] and variables) *)

(* This is not the most simple example of reification possible, since
we could work out an example without variables (with atoms, or holes,
that contains constants). However, using an environment allows one to
reify the identity of such atomic sub-terms. *)

Inductive parith :=
  | a_pvar: positive -> parith
  | a_pconst: positive -> parith
  | a_xI: parith -> parith
  | a_xO: parith -> parith
  | a_xH: parith.

Inductive zarith :=
  | a_zadd: zarith -> zarith -> zarith
  | a_zvar: Z -> zarith
  | a_zconst: Z -> zarith
  | a_ZNeg: parith -> zarith
  | a_ZPos: parith -> zarith
  | a_Z0: zarith.

(** [eval] maps reified terms of type [arith] to [nat] using an
environment to map syntactic variables to terms. *)

Section t.

(*
Locate "+".

Check Coq.ZArith.BinIntDef.Z.add.
*)

Require Import Coq.PArith.BinPos ZArith.

  Variable env : list Z.

  Fixpoint peval (t : parith) : positive :=
  match t with
    | a_pvar a => List.nth (Pos.to_nat a) (List.map Z.to_pos env) 1%positive
    | a_pconst a => a
    | a_xI a => xI (peval a)
    | a_xO a => xO (peval a)
    | a_xH => xH
  end.

  Fixpoint eval (t : zarith) : Z :=
  match t with
    | a_zadd a b => (eval a) + (eval  b)
    | a_zvar a => List.nth (Z.to_nat a) env 0%Z
    | a_zconst a => a
    | a_ZPos a => Zpos (peval a)
    | a_ZNeg a => Zneg (peval a)
    | a_Z0 => Z0
  end.

(* Locate "+". *)
End t.

(*
Check peval.
Check eval.
*)

(** * Some magic  
   
   We use the following vernacular command to make Coq load the plugin
   [plugin] when one load the Coq file [Theory]. In the plugin
   [plugin], we declare some new tactics that will be available in
   proof-mode.

   In the current trunk (07/05/2011 rev 14260), one has to declare all
   ML modules that need to be linked dynamically. *)
Declare ML Module "tpi".


