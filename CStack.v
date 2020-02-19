Require Import CUtils.
Require Import List.
Require Import String.
Require Import Arith.
Require Import Omega.
Require Import PartialMaps.
Import ListNotations.

Definition cstack := list frame.

Definition insert_s (s: cstack) (st: stack sym_tbl)
           (var: string) (val: nat) :
  (cstack * stack sym_tbl) :=
  match s, st with
  | f::s', ft::st' =>
    match ft var with
    | None => 
      let (f', ft') := (insert_var f ft var val) in
      (f'::s', ft'::st')
    | Some _ => (s, st)
    end
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

Fixpoint lookup_addr_s (s: cstack) (addr: nat): option nat :=
  match s with
  | [] => None
  | f::s' => if (addr <? List.length f) then
               lookup_addr f addr
             else
               lookup_addr_s s' (addr - List.length f)
  end.

Fixpoint get_addr_s (st: stack sym_tbl) (var: string): option nat :=
  match st with
  | [] => None
  | ft::st' => match ft var with
               | None => get_addr_s st' var
               | Some val => Some val
               end
  end.

Definition lookup_var_s (s: cstack) (st: stack sym_tbl) (var: string) : option nat :=
  match get_addr_s st var with
  | None => None
  | Some addr => lookup_addr_s s addr
  end.

(* Important properties of validity for stacks:
   * The stack and stack symbol table are the same length.
   * each frame is valid 
**)
Fixpoint valid_state_s (s: cstack) (st: stack sym_tbl): Prop :=
  match s, st with
  | f::s', ft::st' => valid_state_f f ft /\ (valid_state_s s' st')
  | [], [] => True
  | _, _ => False
  end.

Definition push_frame_s (s: cstack) (st: stack sym_tbl):
  (cstack*stack sym_tbl) :=
  ([]::s, empty::st).  

Definition pop_frame_s (s: cstack) (st: stack sym_tbl):
  (cstack * stack sym_tbl) :=
  match s, st with
  | _::s', _::st' => (s', st')
  | _, _ => ([], [])
  end.

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

Inductive cstack_frame_seq_limit_pop:
  cstack -> stack sym_tbl -> cstack -> stack sym_tbl -> string -> Prop :=
| cstack_frame_limit_pop_refl: forall s st limited,
    valid_state_s s st ->
    cstack_frame_seq_limit_pop s st s st limited
| cstack_frame_limit_pop_newframe: forall s st limited,
    valid_state_s s st ->
    cstack_frame_seq_limit_pop s st ([]::s) (empty::st) limited
| cstack_frame_limit_pop_popframe: forall s st f ft limited,
    valid_state_s (f::s) (ft::st) ->
    ft limited = None ->
    cstack_frame_seq_limit_pop (f::s) (ft::st) s st limited
| cstack_frame_limit_pop_trans: forall s st s' st' s'' st'' limited,
    cstack_frame_seq_limit_pop s st s' st' limited ->
    cstack_frame_seq_limit_pop s' st' s'' st'' limited ->
    cstack_frame_seq_limit_pop s st s'' st'' limited.  
  

(* Essentially, there are two sets of each operation 
   provided. 

   There is a sequence definition which is written in terms of 
   the operations that a cstack has.

   The second sequence definition is reworded so that it it relies
   on the commutativity property of insertions / frame operations 
   to cluster by frame.  (These are wrapper)

   The reason why we do this is because the second version is much easier to prove with, but the first version is what we want to use.
 **)

Fixpoint stack_size (s: cstack): nat :=
  match s with
  | [] => 0
  | h::t => (List.length h) + (stack_size t)
  end.

Inductive cstack_seq:
  cstack -> stack sym_tbl -> cstack -> stack sym_tbl -> Prop :=
| cstack_refl: forall s st,
    valid_state_s s st ->
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
    valid_state_s s st ->
    cstack_no_rewrite s st s st n
| cstack_no_rewrite_addr: forall f s ft st f' ft' addr,
    valid_state_s (f::s) (ft::st) ->
    frame_seq_no_rewrite f ft f' ft' addr ->
    cstack_no_rewrite (f::s) (ft::st) (f'::s) (ft'::st) addr
| cstack_no_rewrite_frame: forall s st s' st' n,
    cstack_frame_seq s st s' st' ->
    cstack_no_rewrite s st s' st' n
| cstack_no_rewrite_trans: forall s st s' st' s'' st'' n,
    cstack_no_rewrite s st s' st' (n - (stack_size s' - (stack_size s))) ->
    cstack_no_rewrite s' st' s'' st'' (n - (stack_size s'' - (stack_size s)))->
    cstack_no_rewrite s st s'' st'' n.


Inductive cstack_no_shadowing:
  cstack -> stack sym_tbl -> cstack -> stack sym_tbl -> string ->
  Prop :=
| cstack_no_shadowing_refl: forall s st var,
    valid_state_s s st ->
    cstack_no_shadowing s st s st var
| cstack_no_shadowing_addr: forall f s ft st f' ft' var,
    valid_state_s (f::s) (ft::st) ->
    frame_seq_lift_insert_var f ft f' ft' var ->
    cstack_no_shadowing (f::s) (ft::st) (f'::s) (ft'::st) var
| cstack_no_shadowing_frame: forall s st s' st' var,
    cstack_frame_seq_limit_pop s st s' st' var ->
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
    cstack_seq_wrapper_no_rewrite s st s' st' (oldaddr - (stack_size s'' - (stack_size s))) ->
    cstack_seq_wrapper_no_rewrite s' st' s'' st''
                                  (oldaddr - (stack_size s'' - (stack_size s')))->
    cstack_seq_wrapper_no_rewrite s st s'' st'' oldaddr.

Lemma add_custom_stack_frame:
  forall s st f ft,
    valid_state_s s st ->
    valid_state_f f ft ->
    cstack_seq s st (f :: s) (ft :: st).
Proof.
  intros s st f. induction f; intros.
  - apply force_ft_empty in H0.
    rewrite H0.
    apply cstack_frame.
    apply cstack_frame_newframe.
    assumption.

  - admit. (* Use our hypothesis from before **)
Admitted.

Lemma no_rewrite_add_custom_stack_frame:
  forall s st f ft nat,
    valid_state_s s st ->
    valid_state_f f ft ->
    cstack_no_rewrite s st (f :: s) (ft :: st) nat.
Proof.
Admitted.    

Lemma valid_state_s_len: forall s st,
    valid_state_s s st ->
    List.length s = List.length st.
Proof.
  induction s; intros.
  - unfold valid_state_s in H.
    destruct st; [reflexivity | contradiction].
  - simpl in *.
    destruct st.
    + contradiction.
    + simpl. f_equal. apply IHs. destruct H as [_ H]. assumption.
Qed.

Theorem valid_state_replace: forall s st addr val,
    valid_state_s s st ->
    valid_state_s (replace_addr_s s addr val) st.
Proof.
  induction s; intros.
  - simpl. destruct st.
    apply I.
    inversion H.
  - destruct st. inversion H.
    destruct H.
    unfold replace_addr_s.
    destruct (addr <? List.length a) eqn:eq.
    + unfold valid_state_s; split.
      * eapply preservation_valid_state_f.
        eapply frame_update_addr.
        apply H.
        rewrite Nat.ltb_lt in eq. apply eq.
        reflexivity.
      * assumption.
    + fold replace_addr_s. split.
      assumption.
      apply IHs. assumption.
Qed.
  

Theorem cstack_seq_replace_addr_s: forall s st addr val,
    valid_state_s s st ->
    cstack_seq s st (replace_addr_s s addr val) st.
Proof.
  intros.
  generalize dependent st.
    generalize dependent addr.
    induction s; intros.
    + destruct st; try contradiction.
      simpl.
      constructor. reflexivity.
    + unfold valid_state_s in H.
      destruct st; try contradiction.
      destruct H as [frame H].
      fold valid_state_s in H.
      assert (valid_state_s s st). assumption.
      
      unfold replace_addr_s.
      destruct (addr <? List.length a) eqn:eq.
      * apply cstack_var.
        split; assumption.
        apply Nat.ltb_lt in eq.
        eapply frame_update_addr;
          try eassumption;
          try reflexivity.
      * fold replace_addr_s.
        eapply cstack_trans.
        apply cstack_frame.
        apply cstack_frame_popframe.
        split; assumption.

        eapply cstack_trans.
        apply IHs. assumption.

        apply add_custom_stack_frame.
        apply valid_state_replace. assumption. assumption.
Qed.

Theorem limit_pop_imp_frame_seq: forall s st s' st' limited,
    cstack_frame_seq_limit_pop s st s' st' limited ->
    cstack_frame_seq s st s' st'.
Proof.
  intros.
  induction H; intros.
  - apply cstack_frame_refl.
    assumption.
  - apply cstack_frame_newframe.
    assumption.
  - apply cstack_frame_popframe. assumption.
  - eapply cstack_frame_trans; eassumption.
Qed.

Theorem cstack_wrapper_imp_cstack: forall s st s' st',
    cstack_seq_wrapper s st s' st' <->
    cstack_seq s st s' st'.
Proof.
  intros.
  split; intros orig; induction orig; intros.
  - apply cstack_refl.
    assumption.
  - unfold insert_s in H0.
    unfold valid_state_s in H.
    destruct s; destruct st; try contradiction.
    + inversion H0; subst.
      constructor. reflexivity.
    + fold valid_state_s in H.
      destruct (s0 var) eqn:eq.
      * inversion H0; subst.
        apply cstack_refl.
        apply H.
      * inversion H0; subst.
        apply cstack_var.
        apply H.
        eapply frame_insert.
        {
          destruct H as [H _]. apply H.
        }
        apply eq.
        reflexivity.
  - rewrite <- H0. clear H0.
    apply cstack_seq_replace_addr_s.
    assumption.
  - inversion H0; subst.
    apply cstack_frame. apply cstack_frame_newframe.
    assumption.
  - unfold pop_frame_s in H0.
    destruct s; destruct st; try contradiction.
    inversion H0; subst. constructor. reflexivity.
    inversion H0; subst.
    apply cstack_frame. apply cstack_frame_popframe.
    assumption.
  - eapply cstack_trans; eassumption.



  - constructor. assumption.
  - induction H0.
    + constructor. assumption.
    + inversion H2; subst.
      eapply cstack_insert_wrapper.
      assumption.
      unfold insert_s.
      rewrite H1. simpl. reflexivity.
    + inversion H2; subst; clear H3.
      eapply cstack_replace_wrapper.
      assumption.
      simpl. apply Nat.ltb_lt in H1. rewrite H1.
      reflexivity.
    + eapply cstack_trans_wrapper.
      apply IHframe_seq1. assumption.
      apply IHframe_seq2.
      apply preservation_valid_state_f in H0_.
      destruct H as [_ H].
      split; assumption.
  - induction H; intros.
    + constructor. assumption.
    + apply cstack_newframe_wrapper.
      assumption. reflexivity.
    + apply cstack_popframe_wrapper.
      assumption. reflexivity.
    + eapply cstack_trans_wrapper; eassumption.
  - eapply cstack_trans_wrapper; eassumption.
Qed.
 
Theorem cstack_no_rewrite_wrapper_imp_no_rewrite: forall s st s' st' addr,
    cstack_seq_wrapper_no_rewrite s st s' st' addr <->
    cstack_no_rewrite s st s' st' addr.
Proof.
Admitted.

Theorem cstack_no_shadowing_imp_no_shadowing: forall s st s' st' var,
    cstack_seq_wrapper_no_shadowing s st s' st' var <->
    cstack_no_shadowing s st s' st' var.
Proof.
  intros. split; intros orig; induction orig; intros.
  - constructor; assumption.
  - unfold insert_s in H1. destruct s; destruct st; inversion H.
    inversion H1; subst.
    constructor; assumption.

    destruct (s0 var) eqn:eq.
    + inversion H1; subst. constructor; assumption.
    + inversion H1; subst.

      eapply cstack_no_shadowing_addr. assumption.
      eapply frame_lift_insert_var; try eassumption.
      reflexivity.
  - rewrite <- H0.
    unfold replace_addr_s.
    destruct s; destruct st; try contradiction.
    econstructor; reflexivity.
    fold replace_addr_s.
    destruct (addr <? List.length f) eqn:eq.
    + eapply cstack_no_shadowing_addr. assumption.
      eapply frame_lift_update_addr. destruct H; assumption.
      rewrite Nat.ltb_lt in eq. eassumption.
      reflexivity.
    + 

      
      
      
      
      
Theorem cstack_no_rewrite_imp_cstack: forall s st s' st' addr,
    cstack_no_rewrite s st s' st' addr ->
    cstack_seq s st s' st'.
Proof.
  intros.
  induction H; intros.
  - apply cstack_refl. assumption.
  - apply cstack_var.
    + assumption.
    + apply no_rewrite_imp_frame_seq with (n:=addr).
      assumption.
  - apply cstack_frame.
    assumption.
  - eapply cstack_trans.
    eassumption. assumption.
Qed.

Theorem cstack_no_shadowing_imp_cstack: forall s st s' st' var,
    cstack_no_shadowing s st s' st' var ->
    cstack_seq s st s' st'.
Proof.
  intros.
  induction H; intros.
  - apply cstack_refl. assumption.
  - apply cstack_var.
    assumption.
    apply lift_insert_imp_frame_seq with (targetvar:=var).
    assumption.
  - apply cstack_frame.
    apply limit_pop_imp_frame_seq with (limited:=var).
    assumption.
  - eapply cstack_trans.
    apply IHcstack_no_shadowing1.
    apply IHcstack_no_shadowing2.
Qed.

(* These are the theorems that provide information **)

Theorem preservation_cstack_frame_seq: forall
    s st s' st',
    cstack_frame_seq s st s' st' ->
    valid_state_s s' st'.
Proof.
  intros.
  induction H; intros.
  - assumption.
  - simpl. split. apply valid_state_f_empty.
    assumption.
  - inversion H. assumption.
  - assumption.
Qed.

Theorem cstack_frame_seq_lookup_correct: forall
    s st s' st' var addr,
    get_addr_s st var = Some addr ->
    cstack_frame_seq_limit_pop s st s' st' var ->
    get_addr_s st' var = Some addr.
Proof.
  intros.
  induction H0; intros.
  - assumption.
  - assumption.
  - simpl in H. rewrite H1 in H.
    assumption.
  - apply IHcstack_frame_seq_limit_pop2.
    apply IHcstack_frame_seq_limit_pop1.
    assumption.
Qed.

Theorem preservation_valid_state_s: forall
    s st s' st',
    cstack_seq s st s' st' ->
    valid_state_s s' st'.
Proof.
  intros.
  induction H; intros.
  - assumption.
  - inversion H.
    simpl. split.
    apply (preservation_valid_state_f f ft).
    assumption.
    assumption.
  - apply (preservation_cstack_frame_seq s st).
    assumption.
  - assumption.
Qed.  

Theorem cstack_seq_lookup_correct: forall
    s st s' st' var addr,
    get_addr_s st var = Some addr ->
    cstack_no_shadowing s st s' st' var ->
    get_addr_s st' var = Some addr.
Proof.
  intros.
  induction H0; intros.
  - assumption.
  - simpl in *.
    erewrite frame_seq_lookup_correct. reflexivity.

    destruct (ft var) eqn:eq.
    rewrite H in eq. apply eq.
    congruence.

    apply lift_insert_imp_frame_seq in H2.
    apply H2.
  - apply (cstack_frame_seq_lookup_correct s st s'); assumption.
  - apply IHcstack_no_shadowing2.
    apply IHcstack_no_shadowing1.
    assumption.
Qed.

Lemma append_frame_size: forall (s: cstack) (f f': frame),
    stack_size (f'::s) - stack_size(f::s) =
    List.length f' - List.length f.
Proof.
  intros. simpl. omega.
Qed.

Lemma append_frame_comp: forall (s: cstack) (f f': frame),
    stack_size (f'::s) >= stack_size (f::s) ->
    List.length f' >= List.length f.
Proof.
  intros.
  simpl in *. omega.
Qed.

Theorem cstack_seq_no_rewrite_correct: forall
    s st s' st' addr val,
    lookup_addr_s s addr = Some val ->
    cstack_no_rewrite s st s' st' addr ->
    stack_size s' >= stack_size s ->
    lookup_addr_s s' (stack_size s' - stack_size s + addr) = Some val.
Proof.
  intros.
  assert (valid_state_s s' st'). {
    apply preservation_valid_state_s with (s:=s) (st:=st).
    apply cstack_no_rewrite_imp_cstack with (addr:=addr).
    assumption.
  }
  induction H0; subst.
  - rewrite Nat.sub_diag. simpl. assumption.
  - rewrite append_frame_size.
    apply append_frame_comp in H1.
    simpl in *.

    destruct (addr <? Datatypes.length f) eqn:eq.

    rewrite Nat.ltb_lt in eq.
    apply (plus_lt_compat_l _ _ (Datatypes.length f' - Datatypes.length f)) in eq.
    assert (Datatypes.length f' - Datatypes.length f +
            Datatypes.length f = Datatypes.length f'). omega.
    rewrite H4 in eq. clear H4.
    rewrite <- Nat.ltb_lt in eq.
    rewrite eq.
    eapply frame_seq_no_rewrite_correct.
    destruct H2 as [fH sH].
    unfold valid_state_f in fH.
    assumption.
    apply H3.

    rewrite Nat.ltb_ge in eq.
    apply (plus_le_compat_l _ _ (Datatypes.length f' - Datatypes.length f)) in eq.
    assert (Datatypes.length f' - Datatypes.length f +
            Datatypes.length f = Datatypes.length f'). omega.
    rewrite H4 in eq.
    rewrite <- Nat.ltb_ge in eq.
    rewrite eq.

    assert (Datatypes.length f' - Datatypes.length f + addr -
                                                       Datatypes.length f' = addr - Datatypes.length f).
    omega.
    rewrite H5.
    assumption.
  - induction H0.
    + rewrite Nat.sub_diag. simpl. assumption.
    + simpl. rewrite Nat.sub_diag. simpl. rewrite Nat.sub_0_r. assumption.
    + simpl in *.
      assert (f = []). {
        apply length_zero_iff_nil.
        omega.
      }

      rewrite H3.
      simpl. rewrite Nat.sub_diag. simpl.
      rewrite H3 in H. simpl in H. rewrite Nat.sub_0_r in H. assumption.
    + admit.
  - admit.
Admitted.
    
