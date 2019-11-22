Require Import List.
Import ListNotations.
Require Import String.
Require Import Maps.

Definition generalized (A: Type) := list A.

Definition stack := generalized nat.

Definition push (x: nat) (xl: stack): stack :=
  x::xl.

Definition pop (xl: stack): option (nat*(stack)) :=
  match xl with
  | [] => None
  | h::t => Some (h,t)
  end.

Definition heap := generalized nat.

(* We want a way to look up values in the stack and heap *)
Definition symbol_table := total_map nat.  (* make sure to initialize with error default value *)

Definition context := (stack)*(heap)*(symbol_table).

Definition st := total_map nat.

Definition test A := list (nat * A).

Check (test nat).

Definition sample_context : context :=
  ([1], [1], t_empty 1).
