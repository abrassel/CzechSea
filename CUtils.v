Require Import PartialMaps.
Require Import String.

Definition sym_tbl := partial_map string nat.

(* Can imagine a heap as a single stack frame **)
Definition stack (A: Type) := list A.

Definition frame := stack nat.

Definition insert_var (f: frame)
           (ft: sym_tbl) (var: string) (val: nat)
  : (frame * sym_tbl).
Admitted.

Definition replace_addr (f: frame) (addr newval: nat)
  : frame.
Admitted.

Definition lookup_addr (f: frame) (addr: nat) : option nat.
Admitted.


Definition lookup_var (f: frame) (ft: sym_tbl) (var: string) : option nat :=
  match ft var with
  | None => None
  | Some addr => lookup_addr f addr
  end.


Definition valid_state_f (f: frame) (ht: sym_tbl): Prop :=
  True.

(* for a regular heap, use offset of 0.  used to create frames **)
Inductive frame_seq:
  frame -> sym_tbl -> frame -> sym_tbl ->
  Prop :=
| frame_refl: forall (f: frame) (ft: sym_tbl),
    valid_state_f f ft ->
    frame_seq f ft f ft
| frame_insert: forall f ft f' ft' var val,
    valid_state_f f ft ->
    ft var = None ->
    insert_var f ft var val = (f', ft')->
    frame_seq f ft f' ft'
| frame_update_addr: forall f ft f' addr newval,
    valid_state_f f ft ->
    0 <= addr < List.length f ->
    replace_addr f addr newval = f' ->
    frame_seq f ft f' ft
| frame_trans: forall f ft f' ft' f'' ft'',
    frame_seq f ft f' ft' ->
    frame_seq f' ft' f'' ft'' ->
    frame_seq f ft f'' ft''.

Inductive frame_seq_no_rewrite:
  frame -> sym_tbl -> frame -> sym_tbl -> nat -> Prop :=
| frame_norewrite_refl: forall (f: frame) (ft: sym_tbl) n,
    valid_state_f f ft ->
    frame_seq_no_rewrite f ft f ft n
| frame_norewrite_insert: forall f ft f' ft' var val n,
    valid_state_f f ft ->
    ft var = None ->
    insert_var f ft var val = (f', ft')->
    frame_seq_no_rewrite f ft f' ft' n
| frame_norewrite_update_addr: forall f ft f' addr newval n,
    valid_state_f f ft ->
    0 <= addr < List.length f ->
    addr <> n ->
    replace_addr f addr newval = f' ->
    frame_seq_no_rewrite f ft f' ft n
| frame_norewrite_trans: forall f ft f' ft' f'' ft'' n,
    frame_seq_no_rewrite f ft f' ft' n ->
    frame_seq_no_rewrite f' ft' f'' ft'' n ->
    frame_seq_no_rewrite f ft f'' ft'' n.

Inductive frame_seq_lift_insert_var:
  frame -> sym_tbl -> frame -> sym_tbl -> string -> Prop :=
| frame_exclude_var_refl: forall (f: frame) (ft: sym_tbl) targetvar,
    valid_state_f f ft ->
    frame_seq_lift_insert_var f ft f ft targetvar
| frame_live_insert_var_insert: forall f ft f' ft' val targetvar,
    valid_state_f f ft ->
    ft targetvar = None ->
    insert_var f ft targetvar val = (f', ft')->
    frame_seq_lift_insert_var f ft f' ft' targetvar
| frame_lift_insert_var_update_addr:
    forall f ft f' addr newval targetvar,
    valid_state_f f ft ->
    0 <= addr < List.length f ->
    replace_addr f addr newval = f' ->
    frame_seq_lift_insert_var f ft f' ft targetvar
| frame_lift_insert_trans: forall f ft f' ft' f'' ft'' targetvar,
    frame_seq_lift_insert_var f ft f' ft' targetvar ->
    frame_seq_lift_insert_var f' ft' f'' ft'' targetvar ->
    frame_seq_lift_insert_var f ft f'' ft'' targetvar.

Theorem lif_insert_imp_frame_seq: forall f ft f' ft' targetvar,
    frame_seq_no_rewrite f ft f' ft' targetvar ->
    frame_seq f ft f' ft'.
Proof.
Admitted.


Theorem no_rewrite_imp_frame_seq: forall f ft f' ft' n,
    frame_seq_no_rewrite f ft f' ft' n ->
    frame_seq f ft f' ft'.
Proof.
Admitted.

Theorem preservation_valid_state_f: forall
    f ft f' ft',
    frame_seq f ft f' ft' ->
    valid_state_f f' ft'.
Proof.
Admitted.

Theorem frame_seq_lookup_correct: forall
    f ft f' ft' var addr,
    ft var = addr ->
    frame_seq f ft f' ft' ->
    ft' var = addr.
Proof.
Admitted.


Theorem frame_seq_no_rewrite_correct: forall
    f ft f' ft' addr val,
    lookup_addr f addr = val ->
    frame_seq_no_rewrite f ft f' ft' addr ->
    lookup_addr f addr = val.
Proof.
Admitted.


