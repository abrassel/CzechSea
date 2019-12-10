Require Import CUtils.
Require Import CHeap.
Require Import CStack.

Definition ctx : Type := (cheap * sym_tbl *
                          cstack * stack sym_tbl).

Definition filter_h (c: ctx): cheap * sym_tbl.
Admitted.

Definition filter_s (c: ctx): cstack * stack sym_tbl.
Admitted.

Definition valid_state (c: ctx) :=
  let '(s, st) := filter_s c in
  let '(h, ht) := filter_h c in
  valid_state_h h ht /\
  valid_state_s s st.

Inductive ctx_seq: ctx -> ctx -> Prop :=
| ctx_refl: forall c,
    valid_state c ->
    ctx_seq c c
| ctx_heap: forall c c' h ht h' ht',
    filter_h c = (h, ht) ->
    filter_h c = (h', ht') ->
    cheap_seq h ht h' ht' ->
    ctx_seq c c'
| ctx_cstack: forall c c' s st s' st',
    filter_s c = (s, st) ->
    filter_s c' = (s', st') ->
    cstack_seq_wrapper s st s' st' ->
    ctx_seq c c'
| ctx_trans: forall c c' c'',
    ctx_seq c c' ->
    ctx_seq c' c'' ->
    ctx_seq c c''.

Theorem ctx_seq_valid_state_forwards: forall c c',
    ctx_seq c c' ->
    valid_state c'.
Proof.
Admitted.
    
