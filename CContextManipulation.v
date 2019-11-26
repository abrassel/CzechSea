Require Import CContext.
Require Import String.
Require Import Maps.

Definition struct_table := partial_map (partial_map nat).

(* TODO - must fix **)
Inductive context :=
| space (s: cstack) (st: stack sym_tbl) (h: cheap) (ht: sym_tbl)
        (H: valid_state s st) (s_tbl: struct_table).

Definition smart_lookup ctx var :=
  let '(space s st h ht _ _) := ctx in
  match lookup_s s st var with
  | Some val => Some val
  | None => match lookup_h h ht var with
            | Some val => Some val
            | None => None
            end
  end.

Definition decode_struct ctx s_name s_var :=
  let '(space _ _ _ _ _ s_tbl) := ctx in
  match s_tbl s_name with
  | Some s_map => match s_map s_var with
                  | Some offset => 

(* Internally translate each s_var to a pointer offset**)
Definition query_struct_space (ctx: context) (s_name s_var s_field: string) :=
  smart_lookup ctx (decode_struct ctx s_name s_var).

(* HOW DO I DEAL WITH TYPING DISTINCTIONS HERE? **)
                  
Hint Unfold query_struct_space.
