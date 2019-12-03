Require Import List.
Import ListNotations.
Require Import String.
Require Import Maps.
Require Import Omega.

Definition MAX_HEAP_SIZE := 99.
Definition MIN_HEAP_SIZE := 50.

Definition stack (A: Type) := list A.
Definition frame := stack nat.
Definition cstack := stack (frame).

(* underlying C specification does not insist on an actual heap *)
Definition cheap := list nat.

(* We want a way to look up values in the stack and heap.
   We'll have two symbol tables.  One to index into stack values,
and one to index into heap values
 **)

Definition sym_tbl := partial_map nat.  (* make sure to initialize with error default value *) 

(* C programs will be manipulating stack, heap, and symbol table 
 
 Important: in prep for scoping, stack of sym_tbls
 *)

(* Some useful properties of our stack, heap, symbol table, and context **)

Definition push {A: Type} (xl: stack A) (x: A): stack A :=
  x::xl.

Hint Unfold push.

Definition pop {A: Type} (xl: stack A): option (stack A) :=
  match xl with
  | [] => None
  | _::t => Some t
  end.

Fixpoint get_pred (s: cstack) :=
  match s with
  | [] => MAX_HEAP_SIZE (* num allowed variables **)
  | h::t => (get_pred t) - (List.length h)
  end.

(*Use this to enter a new scope.  Don't forget that main has a scope **)
Definition push_new_frame (s: cstack) (st: stack sym_tbl) :=
  let s' := push s [] in
  let st' := push st (empty) in
  (s', st').

Hint Unfold push_new_frame.

(*Use this to create new variables on the stack *)
Definition push_var (s: cstack) (st: stack sym_tbl) (var: string) (v: nat) :=
  match s, st with
  | shead::stail, sthead::sttail =>
    let next_val := get_pred s in
    let s' := (push shead v)::stail in
    let st' := (var |-> next_val; sthead)::sttail in
    (s', st')
  | _, _ => ([], []) (* error case -> always have stack frames **)
  end.

Hint Unfold push_var.

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
            | Some n => Some n
            end
  end.

Hint Unfold search_sm.

Fixpoint frame_nth (s: cstack) (offset: nat) :=
  match s with
  | [] => None (* Not going to happen **)
  | h::t => (fix frame_aux l n :=
               match l, n with
               | h'::t', S n => frame_aux t' n
               | [], _ => frame_nth t n
               | h'::t', 0 => Some h'
               end
            ) h offset
  end.

Hint Unfold frame_nth.

Definition offset addr s := addr - get_pred s.

Hint Unfold offset.

Definition get_val_s (s: cstack) (addr: nat): option nat :=
  let off := offset addr s in
  let fix get_val_s_aux s t :=
      match s with
      | [] => None
      | h::t => match nth_error h off with
                | None => get_val_s_aux t (off - List.length h)
                | Some val => Some val
                end
      end
  in get_val_s_aux s off.

Hint Unfold get_val_s.

(*Use this to lookup a variable (scope shadowing applies **)
Fixpoint lookup_s (s: cstack) (st: stack sym_tbl) (var: string) :=
  match search_sm st var with
  | None => None
  | Some addr => 
    get_val_s s addr
  end.

Hint Unfold lookup_s.

Definition addr_s (st: stack sym_tbl) (var: string) :=
  search_sm st var.

Hint Unfold addr_s.

(* Now some useful lemmas **)

Definition valid_state (s: cstack) (st: stack sym_tbl) :=
  s <> [] /\ st <> [] /\
  forall var n, search_sm st var = Some n ->
                               n > get_pred s.

Hint Unfold valid_state.

Definition not_full (s: cstack) :=
  get_pred s > MIN_HEAP_SIZE.

Hint Unfold not_full.

Lemma S_n_sub_S_m: forall n m,
    n - m <> 0 ->
    S (n - S m) = n - m.
Proof.
  intros.
  omega.
Qed.

Lemma n_sub_s_m_gt: forall n m,
    n - m <> 0 ->
    n - m > n - S m.
Proof.
  intros.
  omega.
Qed.

Lemma min_heap_inv: forall a, a > MIN_HEAP_SIZE ->
                              a <> 0.
  unfold MIN_HEAP_SIZE. intros. omega.
Qed.

Lemma offset_stuff:
  forall n x f s,
    n > get_pred (f::s) ->
    not_full (f::s) ->
    (offset n ((x :: f) :: s)) =
    S (offset n (f::s)).
Proof.
  intros.

   assert (Hpred: (S (get_pred ((x::f)::s)) = get_pred (f::s))). {
      simpl.
      apply S_n_sub_S_m.
      unfold not_full in H0.      
      apply min_heap_inv. simpl in H0. assumption.
    }

    unfold offset. simpl in *.
    omega.
Qed.

Lemma lookup_stuff:
  forall x f s n,
    n > get_pred (f :: s) ->
    not_full (f::s) ->
    get_val_s ((x::f)::s) n =
    get_val_s (f::s) n.
Proof.
  intros.
  unfold get_val_s.
  
Admitted.  

Lemma search_sm_diff: forall f st var1 var2 val2,
    var1 <> var2 ->
    search_sm ((var2 |-> val2; f)::st) var1 =
    search_sm (f::st) var1.
Proof.
  intros.
  simpl.
  rewrite update_neq.
  reflexivity.
  auto.
Qed.

Lemma search_sm_same: forall f st var1 val1 ,
    search_sm ((var1 |-> val1; f)::st) var1 = Some val1.
Proof.
  intros.
  simpl.
  rewrite update_eq.
  reflexivity.
Qed.

Lemma add_stack_properly_pred: forall (s s': cstack) (st st': stack sym_tbl) (var: string) (val: nat),
    valid_state s st /\ not_full s ->
    search_frame st var = None ->
    push_var s st var val = (s', st') ->
    get_pred s' = pred (get_pred s).
Proof.
  destruct s; intros.
  inversion H; inversion H2; contradiction.

  inversion H0; subst.
  destruct st. destruct H as [[A1 [A2 A3]] A4].
  contradiction. clear H0.
                
  inversion H1; subst. clear H1.
  unfold push.
  
  unfold get_pred.
  simpl. omega.
Qed.

Lemma add_stack_properly_invariant: forall (s s': cstack) (st st': stack sym_tbl) (var: string) (val: nat),
    valid_state s st /\ not_full s ->
    search_frame st var = None ->
    push_var s st var val = (s', st') ->
    valid_state s' st'.
Proof.
  intros.
  destruct H as [[A1 [A2 A3]] A4].
  destruct s; destruct st; intros; try contradiction.

  inversion H1; subst; clear H1.
  unfold valid_state.
  split.
  intros contra; inversion contra.
  split. intros contra; inversion contra.
  intros var2.

  destruct (string_dec var var2).
  rewrite e.
  rewrite search_sm_same.
  intros.
  inversion H; subst.
  unfold push, offset.
  simpl. apply n_sub_s_m_gt.
  apply min_heap_inv.
  apply A4.

  intros.
  rewrite search_sm_diff in H.
  unfold offset.
  simpl.

  apply A3 in H. simpl in H.
  omega.
  auto.
Qed.

Fixpoint stack_size (s: cstack) :=
  match s with
  | [] => 0
  | h::t => (List.length h) + (stack_size t)
  end.

Hint Unfold stack_size.

(* Define a multi-step relationship **)
Inductive cstack_seq : cstack -> stack sym_tbl -> cstack -> stack sym_tbl -> Prop :=
| cstack_refl: forall s st,
    valid_state s st ->
    cstack_seq s st s st
| cstack_var: forall s st s' st' v val,
    valid_state s st ->
    search_frame st v = None ->
    not_full s ->
    push_var s st v val = (s', st') ->
    cstack_seq s st s' st'
| cstack_frame_empty:
    cstack_seq [] [] [[]] [empty]
| cstack_frame: forall s st s' st',
    valid_state s st ->
    push_new_frame s st = (s', st') ->
    cstack_seq s st s' st'
| cstack_trans: forall s s' s'' st st' st'',
    valid_state s st ->
    cstack_seq s st s' st' ->
    cstack_seq s' st' s'' st'' ->
    cstack_seq s st s'' st''.
                            
Theorem forwards_validity_s: forall s s' st st',
    cstack_seq s st s' st' ->
    valid_state s' st'.
Proof. 
  intros.
  induction H; intros.
  - assumption.
  - eapply add_stack_properly_invariant.
    split; [apply H | apply H1].
    apply H0.
    apply H2.
  - unfold valid_state.
    split. intros contra; inversion contra.
    split. intros contra; inversion contra.
    intros.
    inversion H.
  - inversion H0; subst.
    split. intros contra. inversion contra.
    split. intros contra. inversion contra.
    simpl. intros.
    destruct H as [V1 [V2 V3]].
    rewrite Nat.sub_0_r. apply V3 in H1. apply H1.
  - apply IHcstack_seq2.
Qed.

Lemma search_sm_early_stop:
  forall ft st v addr,
    ft v = Some addr ->
    search_sm (ft::st) v = Some addr.
Proof.
  intros.
  simpl. rewrite H.
  reflexivity.
Qed.

Lemma nth_cons: forall {A: Type} (la: list A) (a: A) (x: nat),
    nth_error (a::la) (S x) = nth_error la x.
Proof.
  intros.
  unfold nth_error.
  reflexivity.
Qed.

Lemma insert_non_shadowing:
  forall s st v1 addr1 f ft f' ft' v2 val2,
    valid_state (f::s) (ft::st) ->
    v2 <> v1 ->
    ft v1 = Some addr1 ->
    push_var (f::s) (ft::st) v2 val2 = (f'::s, ft'::st) ->
    search_frame (ft'::st) v1 = Some addr1.
Proof.
  intros.
  inversion H2; subst; clear H2.
  simpl.
  rewrite update_neq. apply H1. apply H0.
Qed.

Definition shadowed st st' v :=
  search_sm st v <> search_sm st' v. (*deref magic **)

(* Now, lemma showing that this works between frames **)
Theorem lookup_works: forall (s s': cstack) (st st': stack sym_tbl) (v: string) (val: nat),
    valid_state s st ->
    search_sm st v = Some val ->
    cstack_seq s st s' st' ->
    search_sm s' st' v = Some val \/ shadowed st st' v.
Proof.
  intros.
  destruct H as [SH [STH VarH]].
  induction H1.
  (* Refl -> we have it by assumption **)
  - left.
    assumption.

  - (*Var case.  We have 2 cases.
    Case 1: in the same stack frame.
    - Must not be equal so shadowing is impossible.
    Case 2: in different stack frames.
    - Can be equal, so shadowing is possible.
     **)

    destruct s as [| f s]; destruct st as [| ft st]; try contradiction.
    destruct (search_frame (ft :: st) v) eqn:eq.
    (* Case 1: we are in the same frame **)
    left.

    (* assert (stillValid: valid_state s' st'). {
      eapply add_stack_properly_invariant.
      split. apply H. apply H2.
      apply H1.
      apply H3.
    }
    destruct stillValid as [sv1 [sv2 sv3]]. **)

    (* Let's get some info about what s' and st' look like **)
    inversion H3; subst.

    unfold push.


    (* we know that v <> v0.  Let's show it **)
    destruct (string_dec v v0).
    rewrite e in eq. congruence.

    unfold lookup_s.
    rewrite search_sm_diff.
    unfold search_sm. simpl in eq. rewrite eq.
    rewrite lookup_stuff.
    unfold lookup_s in H0.
    rewrite search_sm_early_stop with (addr:=n) in H0.
    apply H0.
    apply eq.
    apply (VarH v).
    rewrite search_sm_early_stop with (addr:=n).
    reflexivity.
    assumption.
    assumption.
    assumption.
    (* DONE WITH SAME FRAME **)
    

    (* In this case we have that they are in different frames **)
    inversion H0.
    inversion eq.
    rewrite H6 in H5.
    destruct (search_sm st v) eqn:addr.
    2: inversion H5. (* we know that there is a valid lookup **)
    
    (* Moreover it's possible for them to be equal now **)
    destruct (string_dec v v0).
    (* shadowing case **)
    right.
    unfold shadowed.
    unfold search_sm.
    rewrite H6.
    fold search_sm.

    (*Problem here is that v has changed in st' **)

    inversion H3.
    rewrite addr.
    rewrite e.
    rewrite search_sm_same.

    injection; intros.

    simpl in VarH.
    specialize VarH with (var:=v) (n:=n).
    rewrite H6 in VarH.
    apply VarH in addr.
    omega.
    (*DONE WITH SHADOWING DIFFERENT STACK FRAME **)

    left.
    (* No shadowing here -> replacing something entirely different **)
    rewrite H6.
    rewrite H5.
    inversion H3; subst.
    unfold lookup_s.
    rewrite search_sm_diff.
    unfold search_sm.
    rewrite H6.
    fold search_sm.
    rewrite addr.
    unfold push.
    rewrite lookup_stuff.
    assumption.
    apply (VarH v n).
    unfold search_sm.
    rewrite H6.
    apply addr.
    assumption.
    assumption.

    (*DONE WITH NO SHADOWING DIFFERENT STACK FRAME **)

  - (*EMPTY -> FIRST STACK FRAME **)
    inversion H0.
  - (* PUSHING NEW FRAME 
       it's impossible to shadow since we aren't actually adding anything **)
    left.
    inversion H1.
    simpl.

    unfold lookup_s in H0.

    (* How do I deal with this fix? **)
    admit.
  - assert (valid_state s' st').
    apply forwards_validity_s with (s:=s) (st:=st).
    assumption.
    destruct H as [SV1 [SV2 SV3]].
    destruct H1 as [S'V1 [S'V2 S'V3]].

    assert (lookup_s s' st' v = Some val \/ shadowed st st' v).
    apply (IHcstack_seq1 SV1 SV2 SV3 H0).
    clear IHcstack_seq1.

    destruct H.
    (* Case 1 -> No shadowing so far **)
    assert (lookup_s s'' st'' v = Some val \/ shadowed st' st'' v).
    apply (IHcstack_seq2 S'V1 S'V2 S'V3 H).
    clear IHcstack_seq2.
    destruct H1.
    (* Case 1.1 -> No shadowing **)
    left. auto.

    (* Case 1.2 -> Shadowing at pt 2 **)
    right.
    intro contra.
    apply H1.
    unfold lookup_s in H.
    admit. (*Bug again **)

    (* Case 2.1 -> Shadowed from the beginning **)
    right.
    inversion H1_0; subst.
    apply H. (* refl case **)

    admit. (* just painstaking **)

    contradiction. (* empty case **)
    inversion H2; subst. (* new frame case **)
    unfold push. intro contra.
    simpl in *.
    apply H. assumption.

    (* trans case oh god **)
    admit.
Admitted.

    
 
  
  
    
    
  

