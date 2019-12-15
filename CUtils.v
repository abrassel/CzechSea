Require Import PartialMaps.
Require Import String.
Require Import List.
Require Import Omega.
Import ListNotations.

Definition sym_tbl := partial_map string nat.

Definition stack (A: Type) := list A.

Definition frame := stack nat.

(* Use this to create a new variable in a frame **)
Definition insert_var (f: frame)
           (ft: sym_tbl) (var: string) (val: nat)
  : (frame * sym_tbl) :=
  (val::f, (var |-> List.length f; ft)).

Fixpoint replace_addr (f: frame) (addr newval: nat)
  : frame :=
  match f with
  | [] => []
  | h::t => match addr with
            | 0 => newval::t
            | S n => h::(replace_addr t n newval)
            end
  end.

Definition lookup_addr (f: frame) (addr: nat) : option nat :=
  nth_error f addr.

Hint Unfold lookup_addr.

Definition lookup_var (f: frame) (ft: sym_tbl) (var: string) : option nat :=
  match ft var with
  | None => None
  | Some addr => lookup_addr f (List.length f - addr)
  end.


Definition valid_state_f (f: frame) (ht: sym_tbl): Prop :=
  forall var addr, ht var = Some addr -> addr < List.length f.

Hint Unfold valid_state_f.

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
| frame_lift_var_refl: forall (f: frame) (ft: sym_tbl) targetvar,
    valid_state_f f ft ->
    frame_seq_lift_insert_var f ft f ft targetvar
| frame_lift_insert_var: forall f ft f' ft' val targetvar,
    valid_state_f f ft ->
    ft targetvar = None ->
    insert_var f ft targetvar val = (f', ft')->
    frame_seq_lift_insert_var f ft f' ft' targetvar
| frame_lift_update_addr:
    forall f ft f' addr newval targetvar,
    valid_state_f f ft ->
    0 <= addr < List.length f ->
    replace_addr f addr newval = f' ->
    frame_seq_lift_insert_var f ft f' ft targetvar
| frame_lift_trans: forall f ft f' ft' f'' ft'' targetvar,
    frame_seq_lift_insert_var f ft f' ft' targetvar ->
    frame_seq_lift_insert_var f' ft' f'' ft'' targetvar ->
    frame_seq_lift_insert_var f ft f'' ft'' targetvar.

Lemma nth_error_nil: forall A addr,
    @nth_error A [] addr = None.
Proof.
  intros.
  destruct addr; reflexivity.
Qed.


(* Some lemmas about home cooked replacement **)
Lemma replace_addr_len: forall f addr newval,
    List.length f = List.length (replace_addr f addr newval).
Proof.
  induction f; intros.
  - reflexivity.
  - simpl.
    destruct addr.
    + reflexivity.
    + simpl. f_equal. apply IHf.
Qed.

Lemma replace_addr_lookup_eq: forall f addr newval,
    0 <= addr < List.length f ->
    lookup_addr (replace_addr f addr newval) addr = Some newval.
Proof.
  induction f; intros.
  - simpl in H. inversion H. inversion H1.
  - simpl in *.
    destruct addr.
    + reflexivity.
    + simpl.
      apply IHf.
      omega.
Qed.

Lemma replace_addr_lookup_neq: forall f addr oldaddr newval,
    addr <> oldaddr ->
    lookup_addr (replace_addr f addr newval) oldaddr = lookup_addr f oldaddr.
Proof.
  induction f; intros.
  - reflexivity.
  - simpl.
    destruct addr.
    + unfold lookup_addr.
      destruct oldaddr; try contradiction.
      reflexivity.
    + destruct oldaddr.
      * reflexivity.
      * simpl. apply IHf. omega.
Qed.  

Theorem lift_insert_imp_frame_seq: forall f ft f' ft' targetvar,
    frame_seq_lift_insert_var f ft f' ft' targetvar ->
    frame_seq f ft f' ft'.
Proof.
  intros. induction H; subst.
  - apply frame_refl. assumption.
  - apply frame_insert with (var:=targetvar) (val:=val); assumption.
  - apply frame_update_addr with (addr:=addr) (newval:=newval); try assumption; try reflexivity.
  - eapply frame_trans.
    apply IHframe_seq_lift_insert_var1.
    assumption.
Qed.

Theorem no_rewrite_imp_frame_seq: forall f ft f' ft' n,
    frame_seq_no_rewrite f ft f' ft' n ->
    frame_seq f ft f' ft'.
Proof.
  intros.
  induction H; subst.
  - apply frame_refl. assumption.
  - apply frame_insert with (var:=var) (val:=val); assumption.
  - apply frame_update_addr with (addr:=addr) (newval:=newval);
      try assumption; try reflexivity.
  - eapply frame_trans.
    apply IHframe_seq_no_rewrite1.
    assumption.
Qed.

Theorem valid_state_f_empty: valid_state_f [] ({}).
Proof.
  unfold valid_state_f.
  intros.
  inversion H.
Qed.

Theorem preservation_valid_state_f: forall
    f ft f' ft',
    frame_seq f ft f' ft' ->
    valid_state_f f' ft'.
Proof.
  intros. 
  induction H.
  - assumption.
  - inversion H1; subst; clear H1.
    unfold valid_state_f; intros.
    destruct (string_dec var var0).
    + rewrite e in H1. rewrite update_eq in H1.
      inversion H1; subst; clear H1.
      simpl. omega.
    + rewrite update_neq in H1. 2: auto.
      unfold valid_state_f in H.
      simpl.
      specialize H with (var:=var0) (addr:=addr).
      apply H in H1.
      omega.
  - inversion H1; subst; clear H2.
    unfold valid_state_f; intros.
    rewrite <- (replace_addr_len _ addr newval).
    unfold valid_state_f in H.
    apply (H var _ H1).
  - assumption.
Qed.  

Theorem frame_seq_lookup_correct: forall
    f ft f' ft' var addr,
    ft var = Some addr ->
    frame_seq f ft f' ft' ->
    ft' var = Some addr.
Proof.
  intros.
  induction H0; intros.
  - assumption.
  - inversion H2; subst; clear H2.
    destruct (string_dec var0 var).
    + congruence.
    + rewrite update_neq. 2: auto.
      assumption.
  - assumption.
  - auto.
Qed.

Theorem frame_seq_no_rewrite_correct: forall
    f ft f' ft' addr val,
    lookup_addr f addr = val ->
    frame_seq_no_rewrite f ft f' ft' addr ->
    lookup_addr f' (List.length f' - List.length f + addr) = val.
Proof.
  intros.
  induction H0; intros.
  - rewrite Nat.sub_diag.
    simpl. assumption.
  - inversion H2; subst; clear H2.
    unfold lookup_addr.

    assert (List.length (val0::f) - Datatypes.length f = 1). {
      simpl.
      destruct (List.length f); omega.
    }

    rewrite H. reflexivity.
  - rewrite <- H.
    rewrite <- H3.
    rewrite <- (replace_addr_len f addr newval).

    rewrite Nat.sub_diag. simpl.
    apply replace_addr_lookup_neq. assumption.
  - admit.
Admitted.
    
    
    
