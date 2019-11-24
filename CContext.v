Require Import List.
Import ListNotations.
Require Import String.
Require Import Maps.

Definition stack (A: Type) := list A.

(* underlying C specification does not insist on an actual heap *)
Definition heap := list nat.

(* We want a way to look up values in the stack and heap.
   We'll have two symbol tables.  One to index into stack values,
and one to index into heap values
 **)

Definition sym_tbl := total_map nat.  (* make sure to initialize with error default value *) 

(* C programs will be manipulating stack, heap, and symbol table 
 
 Important: in prep for scoping, stack of sym_tbls
 *)

(* TODO - must fix **)
Inductive context :=
| space (s: stack nat) (st: sym_tbl) (h: heap) (ht: sym_tbl).

(* Some useful properties of our stack, heap, symbol table, and context **)

Definition push {A: Type} (x: A) (xl: stack A): stack A :=
  x::xl.

Definition pop {A: Type} (xl: stack A): option (A*stack A) :=
  match xl with
  | [] => None
  | h::t => Some (h,t)
  end.

Definition lookup_s (ctx: context) (var: string) :=
  let '(space s st _ _) := ctx in
  let result := st var in
  nth result s 0.

Definition lookup_h (ctx: context) (var: string) :=
  let '(space _ _ h ht) := ctx in
  let result := ht var in
  nth result h 0.

Definition lookup (ctx: context) (var: string) :=
  lookup_s ctx var \/ lookup_h ctx var.

