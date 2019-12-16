Require Import CContext.
Require Import Types.
Require Import Expressions.


(** Inductive Type Definitions For Commands **)
Inductive CCommand : Type :=
| CCSkip : CCommand
| CCCreate: CType -> string -> CCommand
| CCAssign : string -> CExpression -> CCommand
| CCAssignN : CType->string->CExpression -> CCommand
| CCBreak: CCommand
| CCNext: CCommand -> CCommand -> CCommand
| CCIf: CExpression -> CCommand -> CCommand-> CCommand
| CCWhile: CExpression -> CCommand -> CCommand
(* Remove FOR  definition since it's syntatic sugar for while
| CCFor: CExpression-> CExpression->CCommand -> CCommand -> CCommand *)
(** Not Sure About This Section
|CCSwitch : CExpression-> CExpression -> CCommand -> CCommand

 **)

Bind Com_Scope with CCommand.                                                                

(** Added notations for commands **)                                      
Notation "'CONTINUE'" := CCSkip.
Notation "type X":= (CCCreate type X) (at level 60).
Notation "X '=' exp" := (CCAssign X exp) (at level 60).

Notation "X '+=' exp" := (CCAssign X (*X plus expression*)(at level 60).
Notation "X '-=' exp" := (CCAssign X (*X minus expression*)(at level 60).
Notation "X '*=' exp" := (CCAssign X (*X times expression*)(at level 60).

(* Remove the following since they are syntatic sugar 
Notation "X '++'" := (CCAssign X (*X plus 1 *)(at level 60).                                                    
Notation "X '--'" := (CCAssign X (*X minus 1*) (at level 60). *)                                                    

Notation "type X '=' exp" = (CCAssignN type X exp)(at level 60).
Notation "'BREAK'" := CCBreak.
Notation "com1 ; com2":= (CCNext com1 com2) (at level 80, right associativity).
Notation "'IF(' exp '){' c1 '}ELSE{' c2 '}'" := (CCIf exp c1 c2) (at level 80, right associativity).
Notation "'IF(' exp '){' c1 '}'" := (CCIf exp c1 CCSkip) (at level 80, right associativity).
Notation "'WHILE(' exp '){' c1 '}'" := (CCWhile exp c1) (at level 80, right associativity).
Notation ";" := CCSkip.
Notation "'FOR(' exp1 ';' exp2 ';' c1 '){' com '}'" := (CCFor exp1 exp2 c1 com) (at level 80, right associativity).


Open Scope Com_Scope.
(** Notation for command evaluation **)
Reserved Notation " com  '>>' ctx '>>>' ctx' " (at level 40)

(** Evaluation function for commands **)
Inductive  CC_Eval: CCommand-> context -> context->Prop:=
| CC_Eval_Create_S: forall str type s st s' st' h ht,
  lookup_s s st str = None ->
  (* Type mapping context change*)
  insert_s s st str (*Default val*) = (s', st') ->
  type str >> space s st h ht >>> space s' st' h ht

(* Keeping heap value creation outside for the time being
| CC_Eval_Create_H: forall str type s st h ht h' ht',
  lookup_h h ht str = None ->
  (*Type mapping context change*)
  insert_h h ht str (*Default val*) = (h', ht') ->
  type str >> space s st h ht >>> space s st h' ht' *)
  
| CC_Eval_Skip: forall ctx,
    CONTINUE >> ctx >>> ctx

| CC_Eval_next: forall c1 c2 ctx ctx' ctx''',
    c1 >> ctx >>> ctx'->
    c2 >> ctx' >>> ctx''->
    (c1 ; c2) >> ctx >>> ctx''   

| CC_Eval_If_T: forall ctx ctx' exp1 c1 c2,
    (*Exp evaluation to non zero*)->
    c1 >> ctx >>> ctx' ->
    (IF(exp1){ c1} ELSE{ c2}) >> ctx >>> ctx'

| CC_Eval_If_F:  forall ctx ctx' exp1 c1 c2,
    (*Exp evaluation to zero*)->
    c2 >> ctx >>> ctx'->
    (IF(exp1){ c1} ELSE{ c2}) >> ctx >>> ctx'

|CC_Eval_While_E: forall ctx exp1 c1,
    (*Exp evaluatio to zero*)->
    (WHILE(exp1){ c1}) >> ctx >>> ctx

|CC_Eval_While_L: forall ctx ctx' ctx'' exp1 c1,
    (*Exp evaluation to non zero*)->
    c1 >> ctx >>> ctx' ->
    (WHILE(exp1){ c1}) >> ctx' >>> ctx'' ->
    (WHILE(exp1){ c1}) >> ctx >>> ctx'' 

(* Remove FOR related stuff
|CC_Eval_For_E: forall ctx exp1 exp2 com c1,
    (*Exp evaluation to zero*) ->
    (FOR(exp1;exp2;com){ c1}) >> ctx >>> ctx

|CC_Eval_For_L: forall ctx ctx' ctx'' ctx''' exp1 exp2 com c1,
     (*Exp evaluation to non zero*) ->
     c1 >> ctx >>> ctx' ->                  
     (FOR(exp1;exp2;com){ c1}) >> ctx' >>> ctx'' ->
     com >> ctx'' >>> ctx'''
     (For(exp1;exp2;com){ c1}) >> ctx >>> ctx'''
*)

|CC_Eval_Assign_H_E: forall s st h ht h ht' str exp,
    lookup_h ht str = Some n->
    (*Check type matching*)
    replace_h h ht str (*Exp evaluation to val*) = (h', ht') ->
    (str = exp)>> space s st h ht >>> space s st h' ht'

|CC_Eval_Assign_S_E: forall s st h ht s' st' str exp,
    lookup_s st str = Some n->
    (*Check type matching *)
    replace_s s st str (*Exp evalution to val*) = (s', st') ->
    (str = exp) >> space s st h ht >>> space s' st' h ht

(* Keeping heap variable creation outside for the time being 
|CC_Eval_Assign_H_N: forall s st h ht h' ht' type str exp,
    CCreate
    insert_h h ht str (*Exp evaluation to val*) = (h', ht') ->
    (type str = exp) >> space s st h ht >>> space s st h' ht' *)

|CC_Eval_Assign_S_N: forall s st h ht s' st' type str exp,
    (CCreate type str) >> s st h ht >>> s' st' h ->
    (* Check type matching *)
    insert_s s' st' str (*Exp evaluation to val*) = (s'', st'') ->
    (type str = exp) >> space s st h ht >>> space s'' st'' h ht
                
where " com '>>' ctx '>>>'  ctx'" := (CC_Eval com ctx ctx').

Theorem com_ctx_seq: forall ctx ctx' com,
    valid_state ctx ->
    com >> ctx >>> ctx' ->
    ctx_seq ctx ctx'
Proof.
Admitted.

(*
Theorem com_type_preservation: forall str type ctx ctx' com,
        type_check str ctx = type ->
        com >> ctx >>> ctx' ->
        type_check str ctx' = type
*)
     
