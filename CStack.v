Require Import List.
Import ListNotations.
Require Import String.
Require Import Omega.
Require Import PartialMaps.
Require Import FunctionalExtensionality.

Definition stack (A: Type) := list A.
Definition frame := stack nat.
Definition cstack := stack (frame).

(* We want a way to look up values in the stack and heap.
   We'll have two symbol tables.  One to index into stack values,
and one to index into heap values
 **)

Definition sym_tbl := partial_map string (nat*nat).
Definition addr_tags := partial_map nat nat.

(* Some useful properties of our stack, heap, symbol table, and context **)

Definition push {A: Type} (xl: stack A) (x: A): stack A :=
  x::xl.

Fixpoint push_n {A: Type} (xs: stack A) (v: A) (width: nat): stack A :=
  match width with
  | 0 => xs
  | S n' => push (push_n xs v n') v
  end.

Hint Unfold push_n.

Hint Unfold push.

Definition pop {A: Type} (xl: stack A): option (stack A) :=
  match xl with
  | [] => None
  | _::t => Some t
  end.

(*Use this to enter a new scope.  Don't forget that main has a scope **)
Definition push_new_frame (s: cstack) (st: stack sym_tbl) :=
  let s' := push s [] in
  let st' := push st (empty) in
  (s', st').

Hint Unfold push_new_frame.

Definition make_space_frame_s (stf: sym_tbl) (width: nat) :=
  map_pimap
    (fun _ ppair =>
       let '((addr, off)) := ppair in
       (addr + width, off)) stf.

Hint Unfold make_space_frame_s.

Definition make_space_s (st: stack sym_tbl) (width: nat)
  : stack sym_tbl :=
  map (fun stf =>
         make_space_frame_s stf width
      ) st.

Hint Unfold make_space_s.

(*Use this to create new variables on the stack *)
Definition push_var_s (s: cstack) (st: stack sym_tbl) (var: string) (width: nat) :=
  let st' := make_space_s st width in
  match s, st' with
  | sh::st, sth::stt =>
    let sh' := push_n sh 0 width in
    (sh'::st, (var |-> (0, width); sth)::stt)
  | _, _ => ([], [])
  end.

Hint Unfold push_var_s.

(*Use this to return from a scope **)
Definition pop_frame (s: cstack) (st: stack sym_tbl) :=
  match (pop s),(pop st) with
  | Some s', Some st' => (s', st')
  | _, _ => ([], [])
  end.

Hint Unfold pop_frame.

Fixpoint search_frame (st: stack sym_tbl) (var: string) :=
  match st with
  | [] => None
  | h::_ => h var
  end.

Hint Unfold search_frame.

Fixpoint search_sm (st: stack sym_tbl) (var: string) :=
  match st with
  | [] => None 
  | h::t => match h var with
            | None => search_sm t var
            | Some addrxwidth => Some addrxwidth
            end
  end.

Hint Unfold search_sm.

Fixpoint get_val_s (s: cstack) (offset: nat) :=
  match s with
  | [] => None (* Not going to happen **)
  | h::t => match nth_error h offset with
            | Some result => Some result
            | None =>
              get_val_s t (offset - List.length h)
            end
  end.

Hint Unfold get_val_s.

Fixpoint fetch_n (s: cstack) (cur_addr number: nat) :=
  match number with
  | S n' => match fetch_n s (S cur_addr) n' with
            | Some t =>
              match get_val_s s cur_addr with
              | Some h => Some (h::t)
              | None => None
              end
            | None => Some []
            end
  | 0 => Some []
  end.

Hint Unfold fetch_n.

Fixpoint lookup_s (s: cstack) (st: stack sym_tbl)
         (var: string) (width: nat): option (list nat) :=
  match search_sm st var with
  | None => None
  | Some (addr, width) => fetch_n s addr width
  end.

Hint Unfold lookup_s.

Fixpoint replace_vals {A} (l: list A) (vals: list A) :=
  match l, vals with
  | lh::lt, valsh::valst => valsh::(replace_vals lt valst)
  | _, _ => l
  end.
Hint Unfold replace_vals.

Fixpoint replace_vals_start {A} (ind: nat) (l: list A) (vals: list A) :=
  match ind, l with
  | 0, l => replace_vals l vals
  | S ind', h::t => h::(replace_vals_start ind' t vals)
  | _, [] => []
  end.

Hint Unfold replace_vals_start.

Fixpoint replace_s (l: cstack) offset vals :=
  match l with
  | [] => []
  | h::t => if (offset + List.length vals <=? List.length h) then
              (replace_vals_start offset h vals)::t
            else
              h::(replace_s t (offset - List.length h) vals)
  end.

Hint Unfold replace_s.

Definition update_var_s (s: cstack) (st: stack sym_tbl)
           (var: string) (val: list nat) :=
  match search_sm st var with
  | None => (s, st)
  | Some (addr,_) =>
    (replace_s s addr val, st)
  end.
       
Hint Unfold update_var_s.

Definition addr_s (st: stack sym_tbl) (var: string) :=
  search_sm st var.

Hint Unfold addr_s.

(* Definitions to talk about stacks **)

Inductive valid_state: nat -> cstack -> stack sym_tbl -> Prop :=
| valid_state_singleton: forall h1 h2 offset,
    (forall var addr width,
        h2 var = Some (addr, width) ->
        offset <= addr /\ width > 0 /\
        addr + width <= offset + List.length h1
    ) ->
    valid_state offset [h1] [h2]
| valid_state_cons: forall s st h1 h2 t1 t2 offset,
    s = h1::t1 -> st = h2::t2 ->
    (forall var addr width,
        (h2 var = Some (addr, width) ->
         offset <= addr /\ width > 0 /\
         addr + width <= offset + List.length h1)
    ) ->
    valid_state (offset + List.length h1) t1 t2 ->
    valid_state offset s st.

Inductive cstack_seq : cstack -> stack sym_tbl -> cstack -> stack sym_tbl -> Prop :=
| cstack_refl: forall s st,
    valid_state 0 s st ->
    cstack_seq s st s st
| cstack_decl_var: forall s st s' st' v width,
    valid_state 0 s st ->
    width > 0 -> 
    search_frame st v = None -> (* no duplicates in same scope **)
    push_var_s s st v width = (s', st') ->
    cstack_seq s st s' st'
| cstack_upd_var: forall s st s' st' var newvals addr width,
    valid_state 0 s st ->
    search_sm st var = Some (addr, width) ->
    List.length newvals = width ->
    update_var_s s st var newvals = (s', st') ->
    cstack_seq s st s' st'
| cstack_frame_empty:
    cstack_seq [] [] [[]] [empty]
| cstack_frame: forall s st s' st',
    valid_state 0 s st ->
    push_new_frame s st = (s', st') ->
    cstack_seq s st s' st'
| cstack_trans: forall s s' s'' st st' st'',
    valid_state 0 s st ->
    cstack_seq s st s' st' ->
    cstack_seq s' st' s'' st'' ->
    cstack_seq s st s'' st''.

Definition shadowed st st' v :=
  search_sm st v <> search_sm st' v.


(* Now let's do some correctness proofs **)
Lemma make_space_len: forall st width,
    List.length (make_space_s st width) = List.length st.
Proof.
  intros.
  unfold make_space_s.
  apply map_length.
Qed.

Lemma replace_vals_len: forall {A: Type} (h newvals: list A),
    List.length newvals<= List.length h ->
    List.length h = List.length (replace_vals h newvals).
Proof.
  induction h; intros.
  - reflexivity.
  - simpl in *.
    destruct newvals eqn:eq.
    + reflexivity.
    + simpl in *.
      apply le_S_n in H.
      f_equal.
      apply IHh. assumption.
Qed.
      
Lemma replace_vals_start_len: forall {A} (h newvals: list A) addr,
    addr + List.length newvals <= List.length h ->
    List.length (replace_vals_start addr h newvals) =
    List.length h.
Proof.
  intros A h newvals addr.
  generalize dependent A.
  induction addr; intros.
  - simpl in H.
    unfold replace_vals_start.
    symmetry. apply replace_vals_len.
    assumption.
  - simpl in *.
    destruct h; try reflexivity.
    simpl. f_equal.
    apply IHaddr.
    simpl in H. apply le_S_n in H. assumption.
Qed.

Lemma make_space_empty: forall st width,
    make_space_s st width = [] <-> st = [].
Proof.
  intros.
  assert (List.length st = List.length (make_space_s st width)).
  symmetry. apply make_space_len.

  split; intros;
  apply length_zero_iff_nil.
  rewrite H; apply length_zero_iff_nil; assumption.

  rewrite <- H. apply length_zero_iff_nil; assumption.
Qed.

Lemma rev_neq: forall {A} (l1 l2: list A),
    l1 <> l2 <-> l2 <> l1.
Proof.
  split; intros; auto.
Qed.

Lemma push_n_len: forall {A} (l1: list A) val n,
    List.length (push_n l1 val n) = List.length l1 + n.
Proof.
  intros. induction n.
  - auto.
  - simpl. omega.
Qed.

Lemma map_nil: forall {A B} (f: A -> B) l,
    map f [] = l -> l = [].
Proof.
  auto.
Qed.

Lemma option_inj: forall {A} (a b: A),
    Some a = Some b <-> a = b.
Proof.
  intros; split; intros.
  injection H; intros; assumption.
  rewrite H; reflexivity.
Qed.

Lemma make_space_frame_inverse_none: forall f offset var,
    make_space_frame_s f offset var = None ->
    f var = None.
Proof.
  intros.
  unfold make_space_frame_s in H.
  unfold map_pimap in H.
  destruct (f var). inversion H.
  reflexivity.
Qed.

Lemma make_space_frame_inverse: forall f offset var addr width,
    make_space_frame_s f offset var = Some (addr, width) ->
    f var = Some (addr - offset, width) /\ offset <= addr.
Proof.
  intros.
  unfold make_space_frame_s in H. unfold map_pimap in H.
  destruct (f var).
  injection H. destruct p; intros; simpl.
  injection H0; intros; subst.
  split.
  apply option_inj.
  assert (n = n + offset - offset). omega.
  rewrite <- H1. reflexivity.
  apply le_plus_r.
  split; inversion H.
Qed.  
  
Lemma make_space_inv: forall st st' width var addr width2,
    make_space_s st width = st' ->
    search_sm st var = Some (addr, width2) <->
    search_sm st' var = Some (addr + width, width2).
Proof.
  intros. generalize dependent st'.
  induction st; intros; split; intros.
  - unfold search_sm in H0.
    inversion H0.
  - unfold make_space_s in H.
    apply map_nil in H. rewrite H in H0.
    simpl in H0. inversion H0.               
  - unfold make_space_s in H.
    rewrite map_cons in H.
    rewrite <- H.
    unfold search_sm in H0.

    destruct (a var) eqn:eq.
    rewrite H0 in eq; clear H0.

    assert ((make_space_frame_s a width) var =
            Some (addr + width, width2)). {
      unfold make_space_frame_s.
      erewrite map_pimap_correct.
      2: apply eq.
      reflexivity.
    }

    unfold search_sm. rewrite H0.
    reflexivity.

    assert ((make_space_frame_s a width) var =
            None). {
      unfold make_space_frame_s.
      apply map_pimap_neq. assumption.
    }

    unfold search_sm. rewrite H1.
    fold search_sm.
    apply IHst.
    reflexivity.
    assumption.
  - unfold make_space_s in H.
    rewrite map_cons in H.
    unfold search_sm. unfold search_sm in H0.
    rewrite <- H in H0.

    destruct (a var) eqn:eq.

    assert (exists p', make_space_frame_s a width var = Some p'). {
      eapply ex_intro.
      unfold make_space_frame_s.
      erewrite map_pimap_correct.
      constructor.
      apply eq.
    }
    destruct H1 as [p' H1].
    rewrite H1 in H0.
    rewrite H0 in H1.
    unfold make_space_frame_s in H1.
    erewrite map_pimap_correct in H1. 2: apply eq.
    inversion H1; subst; clear H1.

    apply option_inj.   
    destruct p.
    inversion H3; subst.
    assert (n = addr). omega.
    auto.


    fold search_sm in *.

    assert (make_space_frame_s a width var = None). {
      unfold make_space_frame_s.
      erewrite map_pimap_neq.
      reflexivity. assumption.
    }

    rewrite H1 in H0; clear H1.
    eapply IHst.
    2: apply H0.
    reflexivity.
Qed.

Lemma ineq_lemma: forall a b x,
    x < 0 \/ b > a ->
    b <=? a = false.
Proof.
  intros.
  destruct H. inversion H.
  apply Nat.leb_gt.
  omega.
Qed.

Lemma valid_state_len: forall n s st,
    valid_state n s st ->
    List.length s = List.length st.
Proof.
  intros. induction H.
  - reflexivity.
  - inversion H; inversion H0; subst.
    simpl. f_equal. assumption.
Qed.

Lemma search_sm_inv: forall n s st h t v addr width,
    valid_state n s st ->
    search_sm st v = Some (addr, width) ->
    search_frame st v = None ->
    s = h::t ->
    n + List.length h < addr.
Proof.
  intros n s st. generalize dependent n. generalize dependent s.
  induction st; intros.
  - inversion H0.

  - rewrite H2 in H.

    simpl in *.
    rewrite H1 in H0.
    inversion H; subst.
    + inversion H0.
    + inversion H3; subst; clear H3.
      inversion H4; subst; clear H4.
      
      assert (t1 <> []). {
        assert (List.length t1 = List.length t2).
        simpl. eapply valid_state_len. apply H6.

        destruct t1.
        simpl in H2. symmetry in H2.
        apply length_zero_iff_nil in H2.
        rewrite H2 in H0. inversion H0.
        apply rev_neq. apply nil_cons.
      }

      destruct t1 eqn:eq; try contradiction.
      eapply IHst in H6.
Admitted.
      
      

  

Theorem valid_state_forwards: forall s st s' st',
    cstack_seq s st s' st' ->
    valid_state 0 s' st'.
Proof.
  intros s st s' st' cH.
  induction cH as
      [s st H |
       s st s' st' var width vH wH sfNone op |
       s st s' st' var newvals addr width vH sfH lnvH op |
       |
       s st s' st' vH op |
       s s' s'' st st' st'' vH cseq1 cseq2
      ]; intros.

  - (* refl case **)
    assumption.

  - (* make new var case **)
    unfold push_var_s in op.
    inversion vH; subst.
    + destruct (make_space_s [h2] width) eqn:eq.
      * rewrite make_space_empty in eq. inversion eq.

      * unfold make_space_s in eq. rewrite map_cons in eq.
        inversion eq; subst; clear eq.
        inversion op; clear op.
        constructor.
        intros.
        destruct (string_dec var0 var).
        rewrite e in H0. rewrite update_eq in H0. inversion H0; subst.
        rewrite push_n_len. omega.
        
        rewrite update_neq in H0. 2: auto.
      
        apply make_space_frame_inverse in H0. destruct H0.
        apply H in H0. rewrite push_n_len. omega. 
    + (* other possible validity state **)
      simpl in *.
      inversion op; subst; clear op.
      (* goal here is to strip off the first binding **)
      econstructor. constructor.
      constructor.
      intros.
      destruct (string_dec var0 var).
      rewrite e in H. rewrite update_eq in H. inversion H; subst.
      split.
      reflexivity. 
      rewrite push_n_len. omega.
      
      rewrite update_neq in H. 2: auto.
      
      apply make_space_frame_inverse in H. destruct H.
      apply H1 in H. rewrite push_n_len. omega. 

      (*induction **) admit.
      
  - (* update var case **)
    unfold update_var_s in op.
    rewrite sfH in op.
    inversion op; subst; clear op.

    inversion vH; subst.
    + (* case where we're a singleton **)
      simpl in *.
      destruct (h2 var) eqn:eq.
      * rewrite sfH in eq; clear sfH.
        apply H in eq. destruct eq as [_ [Hgt0 eq]].
        rewrite  <- Nat.leb_le in eq.
        rewrite eq. constructor.
        
        intros.
        rewrite replace_vals_start_len.
        eapply H. apply H0.
        rewrite Nat.leb_le in eq. apply eq.

      * inversion sfH.      
    + (* case where we are updating longer list **)
      simpl in *.
      (*
        Need the following fact:
        If h2 var = None but search_sm (h2::t2) var = Some (addr, width), then addr + len (newvals) > len(h1)
       **)
      admit.
      
  - (* empty case **)
    constructor.

    intros. inversion H.
  - (* new frame case **)
    inversion op; subst; clear op.
    unfold push.
    econstructor.
    constructor.
    constructor.
    
    intros. inversion H.
    assumption.
  - (* inductive case **)
    assumption.
    (*Qed. **)
Admitted.

Theorem lookup_works: forall (s s': cstack) (st st': stack sym_tbl) (v: string) (var width: nat),
    valid_state 0 s st ->
    search_sm st v = Some (var, width) ->
    cstack_seq s st s' st' ->
    search_sm st' v = Some (var, width) \/ shadowed st st' v.
Proof.
Admitted.

