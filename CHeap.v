Require Import CUtils.
Require Import String. 

Definition cheap := frame.

Definition insert_h (h: cheap)
           (ht: sym_tbl) (var: string) (val: nat)
  : (cheap * sym_tbl) :=
  insert_var h ht var val.

Definition replace_addr_h (h: cheap) (addr newval: nat)
  : cheap :=
  replace_addr h addr newval.


Definition lookup_addr_h (h: cheap) (addr: nat) : option nat :=
  lookup_addr h addr.


Definition lookup_var_h (h: cheap) (ht: sym_tbl) (var: string) : option nat :=
  lookup_var h ht var. 


Definition valid_state_h (h: cheap) (ht: sym_tbl): Prop :=
  valid_state_f h ht.

(* for a regular heap, use offset of 0.  used to create frames **)
Definition cheap_seq := frame_seq.

Definition cheap_seq_no_rewrite := frame_seq_no_rewrite.


Theorem no_rewrite_imp_cheap_seq: forall h ht h' ht' n,
    cheap_seq_no_rewrite h ht h' ht' n ->
    cheap_seq h ht h' ht'.
Proof.
  intros.
  apply (no_rewrite_imp_frame_seq h ht h' ht' n H).
Qed.

Theorem preservation_valid_state_h: forall
    h ht h' ht',
    cheap_seq h ht h' ht' ->
    valid_state_h h' ht'.
Proof.
  intros.
  apply (preservation_valid_state_f h ht h' ht' H).
Qed.


Theorem cheap_seq_lookup_correct: forall
    h ht h' ht' var addr,
    ht var = addr ->
    frame_seq h ht h' ht' ->
    ht' var = addr.
Proof.
  intros.
  apply (frame_seq_lookup_correct h ht h' ht' var addr H H0).
Qed.


Theorem cheap_seq_no_rewrite_correct: forall
    h ht h' ht' addr val,
    lookup_addr h addr = val ->
    frame_seq_no_rewrite h ht h' ht' addr ->
    lookup_addr h addr = val.
Proof.
  intros.
  apply (frame_seq_no_rewrite_correct h ht h' ht' addr val H H0).
Qed.

