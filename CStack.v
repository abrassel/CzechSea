Require Import CUtils.
Require Import List.
Require Import String.
Require Import Arith.
Require Import PartialMaps.
Import ListNotations.

Definition cstack := list frame.

Definition insert_s (s: cstack) (st: stack sym_tbl)
           (var: string) (val: nat) :
  (cstack * stack sym_tbl) :=
  match s, st with
  | f::s', ft::st' =>
    let (f', ft') := (insert_var f ft var val) in
    (f'::s', ft'::st')
  | _, _ => (s, st)
  end.

Fixpoint replace_addr_s (s: cstack) (addr newval: nat):
  cstack :=
  match s with
  | [] => []
  | f::s' => if (addr <? List.length f) then
               (replace_addr f addr newval)::s'
             else
               f::(replace_addr_s s' (addr - List.length f) newval)
  end.

Definition lookup_addr_s (s: cstack) (addr: nat): option nat.
Admitted.

Definition get_addr_s (st: stack sym_tbl) (var: string): option nat.
Admitted.

Definition lookup_var_s (s: cstack) (st: stack sym_tbl) (var: string) : option nat.
Admitted.

Definition valid_state_s (s: cstack) (st: stack sym_tbl): Prop.
Admitted.

Definition push_frame_s (s: cstack) (st: stack sym_tbl):
  (cstack*stack sym_tbl).
Admitted.

Definition pop_frame_s (s: cstack) (st: stack sym_tbl):
  (cstack * stack sym_tbl).
Admitted.

Inductive cstack_frame_seq:
  cstack -> stack sym_tbl -> cstack -> stack sym_tbl -> Prop :=
| cstack_frame_refl: forall s st,
    valid_state_s s st ->
    cstack_frame_seq s st s st
| cstack_frame_newframe: forall s st,
    valid_state_s s st ->
    cstack_frame_seq s st ([]::s) (empty::st)
| cstack_frame_popframe: forall s st f ft,
    valid_state_s (f::s) (ft::st) ->
    cstack_frame_seq (f::s) (ft::st) s st
| cstack_frame_trans: forall s st s' st' s'' st'',
    cstack_frame_seq s st s' st' ->
    cstack_frame_seq s' st' s'' st'' ->
    cstack_frame_seq s st s'' st''.

Inductive cstack_seq:
  cstack -> stack sym_tbl -> cstack -> stack sym_tbl -> Prop :=
| cstack_refl: forall s st,
    cstack_seq s st s st
| cstack_var: forall f s ft st f' ft',
    valid_state_s (f::s) (ft::st) ->
    frame_seq f ft f' ft' ->
    cstack_seq (f::s) (ft::st) (f'::s) (ft'::st)
| cstack_frame: forall s st s' st',
    cstack_frame_seq s st s' st' ->
    cstack_seq s st s' st'
| cstack_trans: forall s st s' st' s'' st'',
    cstack_seq s st s' st' ->
    cstack_seq s' st' s'' st'' ->
    cstack_seq s st s'' st''.

Inductive cstack_no_rewrite:
  cstack -> stack sym_tbl -> cstack -> stack sym_tbl -> nat ->
  Prop :=
| cstack_no_rewrite_refl: forall s st n,
    cstack_no_rewrite s st s st n
| cstack_no_rewrite_addr: forall f s ft st f' ft' addr,
    valid_state_s s st ->
    frame_seq_no_rewrite f ft f' ft' addr ->
    cstack_no_rewrite (f::s) (ft::st) (f'::s) (ft'::st) addr
| cstack_no_rewrite_frame: forall s st s' st' n,
    cstack_frame_seq s st s' st' ->
    cstack_no_rewrite s st s' st' n
| cstack_no_rewrite_trans: forall s st s' st' s'' st'' n,
    cstack_no_rewrite s st s' st' n ->
    cstack_no_rewrite s' st' s'' st'' n->
    cstack_no_rewrite s st s'' st'' n.


Inductive cstack_no_shadowing:
  cstack -> stack sym_tbl -> cstack -> stack sym_tbl -> string ->
  Prop :=
| cstack_no_shadowing_refl: forall s st var,
    cstack_no_shadowing s st s st var
| cstack_no_shadowing_addr: forall f s ft st f' ft' var,
    valid_state_s (f::s) (ft::st) ->
    get_addr_s st var = None ->
    frame_seq_lift_insert_var f ft f' ft' var ->
    cstack_no_shadowing (f::s) (ft::st) (f'::s) (ft'::st) var
| cstack_no_shadowing_frame: forall s st s' st' var,
    cstack_frame_seq s st s' st' ->
    cstack_no_shadowing s st s' st' var
| cstack_no_shadowing_trans: forall s st s' st' s'' st'' var,
    cstack_no_shadowing s st s' st' var ->
    cstack_no_shadowing s' st' s'' st'' var->
    cstack_no_shadowing s st s'' st'' var.

(* Use this to prove that our set of operations are valid **)
Inductive cstack_seq_wrapper:
  cstack -> stack sym_tbl -> cstack -> stack sym_tbl -> Prop :=
| cstack_refl_wrapper: forall s st,
    valid_state_s s st ->
    cstack_seq_wrapper s st s st
| cstack_insert_wrapper: forall s st s' st' var val,
    valid_state_s s st ->
    insert_s s st var val= (s', st') ->
    cstack_seq_wrapper s st s' st'
| cstack_replace_wrapper: forall s s' st addr val,
    valid_state_s s st ->
    replace_addr_s s addr val = s' ->
    cstack_seq_wrapper s st s' st
| cstack_newframe_wrapper: forall s st s' st',
    valid_state_s s st ->
    push_frame_s s st = (s', st') ->
    cstack_seq_wrapper s st s' st'
| cstack_popframe_wrapper: forall s st s' st',
    valid_state_s s st ->
    pop_frame_s s st = (s', st') ->
    cstack_seq_wrapper s st s' st'
| cstack_trans_wrapper: forall s st s' st' s'' st'',
    cstack_seq_wrapper s st s' st' ->
    cstack_seq_wrapper s' st' s'' st'' ->
    cstack_seq_wrapper s st s'' st''.

Inductive cstack_seq_wrapper_no_shadowing:
  cstack -> stack sym_tbl -> cstack -> stack sym_tbl -> string -> Prop :=
| cstack_refl_wrapper_no_shadowing: forall s st var,
    valid_state_s s st ->
    cstack_seq_wrapper_no_shadowing s st s st var
| cstack_insert_wrapper_no_shadowing: forall s st s' st' var val oldvar,
    valid_state_s s st ->
    var <> oldvar -> 
    insert_s s st var val= (s', st') ->
    cstack_seq_wrapper_no_shadowing s st s' st' oldvar
| cstack_replace_wrapper_no_shadowing: forall s s' st addr val oldvar,
    valid_state_s s st ->
    replace_addr_s s addr val = s' ->
    cstack_seq_wrapper_no_shadowing s st s' st oldvar
| cstack_newframe_wrapper_no_shadowing: forall s st s' st' oldvar,
    valid_state_s s st ->
    push_frame_s s st = (s', st') ->
    cstack_seq_wrapper_no_shadowing s st s' st' oldvar
| cstack_popframe_wrapper_no_shadowing: forall s st s' st' oldvar,
    valid_state_s s st ->
    pop_frame_s s st = (s', st') ->
    cstack_seq_wrapper_no_shadowing s st s' st' oldvar
| cstack_trans_wrapper_no_shadowing: forall s st s' st' s'' st'' oldvar,
    cstack_seq_wrapper_no_shadowing s st s' st' oldvar ->
    cstack_seq_wrapper_no_shadowing s' st' s'' st'' oldvar ->
    cstack_seq_wrapper_no_shadowing s st s'' st'' oldvar.

Inductive cstack_seq_wrapper_no_rewrite:
  cstack -> stack sym_tbl -> cstack -> stack sym_tbl -> nat -> Prop :=
| cstack_refl_wrapper_no_rewrite: forall s st addr,
    valid_state_s s st ->
    cstack_seq_wrapper_no_rewrite s st s st addr
| cstack_insert_wrapper_no_rewrite: forall s st s' st' var val addr,
    valid_state_s s st ->
    insert_s s st var val= (s', st') ->
    cstack_seq_wrapper_no_rewrite s st s' st' addr
| cstack_replace_wrapper_no_rewrite: forall s s' st addr val oldaddr,
    valid_state_s s st ->
    addr <> oldaddr ->
    replace_addr_s s addr val = s' ->
    cstack_seq_wrapper_no_rewrite s st s' st oldaddr
| cstack_newframe_wrapper_no_rewrite: forall s st s' st' oldaddr,
    valid_state_s s st ->
    push_frame_s s st = (s', st') ->
    cstack_seq_wrapper_no_rewrite s st s' st' oldaddr
| cstack_popframe_wrapper_no_rewrite: forall s st s' st' oldaddr,
    valid_state_s s st ->
    pop_frame_s s st = (s', st') ->
    cstack_seq_wrapper_no_rewrite s st s' st' oldaddr
| cstack_trans_wrapper_no_rewrite: forall s st s' st' s'' st'' oldaddr,
    cstack_seq_wrapper_no_rewrite s st s' st' oldaddr ->
    cstack_seq_wrapper_no_rewrite s' st' s'' st'' oldaddr ->
    cstack_seq_wrapper_no_rewrite s st s'' st'' oldaddr.

Theorem cstack_wrapper_imp_cstack: forall s st s' st',
    cstack_seq_wrapper s st s' st' <->
    cstack_seq s st s' st'.
Proof.
Admitted.

Theorem cstack_no_rewrite_wrapper_imp_no_rewrite: forall s st s' st' addr,
    cstack_seq_wrapper_no_rewrite s st s' st' addr <->
    cstack_no_rewrite s st s' st' addr.
Proof.
Admitted.

Theorem cstack_no_shadowing_imp_no_shadowing: forall s st s' st' var,
    cstack_seq_wrapper_no_shadowing s st s' st' var <->
    cstack_no_shadowing s st s' st' var.
Proof.
Admitted.

Theorem cstack_no_rewrite_imp_cstack: forall s st s' st' addr,
    cstack_no_rewrite s st s' st' addr ->
    cstack_seq s st s' st'.
Proof.
Admitted.

Theorem cstack_no_shadowing_imp_cstack: forall s st s' st' var,
    cstack_no_shadowing s st s' st' var ->
    cstack_seq s st s' st'.
Proof.
Admitted.

Theorem preservation_valid_state_s: forall
    s st s' st',
    cstack_seq s st s' st' ->
    valid_state_s s' st'.
Proof.
Admitted.

Theorem cstack_seq_lookup_correct: forall
    s st s' st' var addr,
    get_addr_s st var = Some addr ->
    cstack_no_shadowing s st s' st' var ->
    get_addr_s st var = Some addr.
Proof.
Admitted.

Theorem cstack_seq_no_rewrite_correct: forall
    s st s' st' addr val,
    lookup_addr_s s addr = val ->
    cstack_no_rewrite s st s' st' addr ->
    lookup_addr_s s addr = val.
Proof.
Admitted.
