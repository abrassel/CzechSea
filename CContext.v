Require Import List.
Import ListNotations.
Require Import String.
Require Import Maps.
Require Import Omega.

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

(* TODO - must fix **)
Inductive context :=
| space (s: cstack) (st: stack sym_tbl) (h: cheap) (ht: sym_tbl).

(* Some useful properties of our stack, heap, symbol table, and context **)

(* Helpful to do global lookups across stacks **)
Definition flatten {A: Type} (l: list (list A)): list A :=
  fold_left (fun la la' => la ++ la') l [].


Definition push {A: Type} (xl: stack A) (x: A): stack A :=
  x::xl.

Definition pop {A: Type} (xl: stack A) (d: A):=
  match xl with
  | [] => (d, [])
  | h::t => (h,t)
  end.

Fixpoint get_pred (s: cstack) :=
  match s with
  | [] => 100 (* num allowed variables **)
  | h::t => (get_pred t) - (List.length h)
  end.

(*Use this to enter a new scope.  Don't forget that main has a scope **)
Definition push_new_frame (s: cstack) (st: stack sym_tbl) :=
  let s' := push s [] in
  let st' := push st (empty) in
  (s', st').

(*Use this to create new variables on the stack *)
Definition push_var (s: cstack) (st: stack sym_tbl) (var: string) (v: nat) :=
  match s, st with
  | shead::stail, sthead::sttail =>
    let next_val := get_pred s in
    let s' := (push shead v)::stail in
    let st' := (var !-> Some next_val; sthead)::sttail in
    (s', st')
  | _, _ => ([], []) (* error case -> always have stack frames **)
  end.          

(*Use this to return from a scope **)
Definition pop_frame (s: cstack) (st: stack sym_tbl) :=
  let '(f, s') := pop s [] in
  let '(ft, st') := pop st (empty) in
  (f, s', ft, st').

Fixpoint search_sm (st: stack sym_tbl) (var: string) :=
  match st with
  | [] => 0 (* guaranteed lookup success **)
  | h::t => match h var with
            | None => search_sm t var
            | Some n => n
            end
  end.

Fixpoint frame_nth (s: cstack) (offset: nat) :=
  match s with
  | [] => 0 (* Not going to happen **)
  | h::t => (fix frame_aux l n :=
               match l, n with
               | h'::t', S n => frame_aux t' n
               | [], _ => frame_nth t n
               | h'::t', 0 => h'
               end
            ) h offset
  end.

(*Use this to lookup a variable (scope shadowing applies **)
(*Not efficient.  but it does the job **)
Definition lookup_s (s: cstack) (st: stack sym_tbl) (var: string) :=
  let index := search_sm st var in
  let offset := index - S (get_pred s) in
  frame_nth s offset. (* guaranteed lookup success here too **)

Definition lookup_h (h: cheap) (ht: sym_tbl) (var: string) :=
  match ht var with
  | Some index => nth index h 0
  | None => 0 (* guaranteed lookup success **)
  end.

(* Now some useful lemmas **)
                                                            
(* Lemma saying that we add to stack properly -decrement by 1 eac time**)
Lemma add_stack_properly: forall (s s': cstack) (st st': stack sym_tbl) (var: string) (val: nat),
    s <> [] /\ st <> [] ->
    get_pred s <> 0 ->
    push_var s st var val = (s', st') ->
    get_pred s' = pred (get_pred s).
Proof.
  destruct s; intros.
  inversion H1; subst.
  destruct H. contradiction.

  inversion H1; subst.
  destruct st. destruct H; contradiction.

  inversion H3; subst. clear H3.
  unfold push.

  unfold get_pred.

  simpl.  omega.
Qed.

Fixpoint stack_size (s: cstack) :=
  match s with
  | [] => 0
  | h::t => (List.length h) + (stack_size t)
  end.

Lemma add_stack_invariant: forall (s: cstack),
    s <> [] ->
    List.length s <= 100 ->
    get_pred s = 100 - stack_size s.
Proof.
  induction s; intros.
  contradiction.

  destruct s.
  unfold get_pred.
  unfold stack_size.
  omega.

  unfold get_pred, stack_size.
  assert (get_pred (f :: s) = 100 - stack_size (f :: s)).
  apply IHs. intros contra. inversion contra.
  simpl. simpl in H0. omega.

  unfold get_pred, stack_size in H1. omega.
Qed.
  

(* Second, when you add a variable, you can get the variable **)
Lemma add_stack_vars: forall (s s': cstack) (st st': stack sym_tbl)
                                 (var: string) (val: nat),
    s <> [] /\ st <> [] ->
    get_pred s <> 0 ->
    push_var s st var val = (s', st') ->
    lookup_s s' st' var = val.
Proof.
  intros.
  assert (get_pred s' = pred (get_pred s)).
  apply (add_stack_properly _ _ _ _ _ _ H H0 H1).
  
  destruct H.

  (* we know that we cant have empty stack / table **)
  destruct s; destruct st; try contradiction.

  unfold push_var in H1. inversion H1; subst.

  unfold push. unfold lookup_s.
  unfold search_sm.

  assert ((var !-> Some (get_pred s - Datatypes.length f); s0) var = Some (get_pred s - Datatypes.length f)).
  apply update_eq.
  rewrite H4; clear H4; simpl.
  inversion H2; subst.

  assert (get_pred s - Datatypes.length f -
          S (get_pred s - S (Datatypes.length f)) = 0).
  omega.
  rewrite H4; clear.
  reflexivity.
Qed.

(* Define a multi-step relationship **)

Inductive cstack_seq : cstack -> stack sym_tbl -> cstack -> stack sym_tbl -> Prop :=
| cstack_refl: forall s st,
    cstack_seq s st s st
| cstack_var: forall s s' st st' v val,
    push_var s st v val = (s', st') ->
    cstack_seq s st s' st'
| cstack_frame: forall s s' st st',
    push_new_frame s st = (s', st') ->
    cstack_seq s st s' st'
| cstack_trans: forall s s' s'' st st' st'',
    cstack_seq s st s' st' ->
    cstack_seq s' st' s'' st'' ->
    cstack_seq s st s'' st''.

Theorem backwards_validity_s: forall s s' st st',
    s' <> [] /\ st' <> [] ->
    get_pred s' <> 0 ->
    cstack_seq s st s' st' ->
    s <> [] /\ st <> [] /\ get_pred s <> 0.
Proof.
Admitted.

Fixpoint shadowed (st: stack sym_tbl) (st': stack sym_tbl) v :=
  match st' with
  | [] => True (* Can't have new env bigger.  Impossible **)
  | h::t => st <> st' /\ match h v with
            | Some _ => True
            | _ => shadowed st t v
            end
  end.

(* Now, lemma showing that this works between frames **)
Theorem lookup_works: forall (s s': cstack) (st st': stack sym_tbl) (v: string) (val: nat),
    s' <> [] /\ st' <> [] ->
    get_pred s' <> 0 ->
    lookup_s s st v = val ->
    cstack_seq s st s' st' ->
    lookup_s s' st' v = val \/ shadowed st st' v. 
Proof.
Admitted.
  
  
(* Finally, need some way to guarantee that removing frames doesn't break anything **)
Theorem removal_works: forall (s s': cstack) (st st': stack sym_tbl) (v: string) (val: nat) f ft,
    s <> [] /\ st <> [] ->
    get_pred s <> 0 ->
    lookup_s s st v = val ->
    pop_frame s st = (f, s', ft, st') ->
    lookup_s s st v = val \/ lookup_s [f] [ft] v = val.
Proof.
Admitted.

(* No heap stuff yet **)

  
 
  
  
    
    
  

