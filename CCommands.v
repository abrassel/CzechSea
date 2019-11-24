Require Import CContext.
Require Import Types.
Require Import Expressions.


(** Inductive Type Definitions For Commands **)
Inductive CCommand : Type :=
| CCSkip : CCommand
| CCAssign : id -> CExpression -> CCommand
| CCBreak: CCommand
| CCNext: CCommand -> CCommand -> CCommand
| CCIf: CExpression -> CCommand -> CCommand-> CCommand
| CCWhile: CExpression -> CCommand -> CCommand
| CCFor: CExpression-> CExpression->CExpression -> CCommand -> CCommand
(** Not Sure About This Section
|CCSwitch : CExpression-> CExpression -> CCommand -> CCommand

 **)

Bind Com_Scope with CCommand.                                                                

(** Added notations for commands **)                                      
Notation "'CONTINUE'" := CCSkip.
Notation "X '=' exp" := (CCAssign X exp) (at level 60).
Notation "'BREAK'" := CCBreak.
Notation "com1 ; com2":= (CCNext com1 com2) (at level 80, right associativity).
Notation "'IF(' exp ')' c1 'ELSE' c2" := (CCIf exp c1 c2) (at level 80, right associativity).
Notation "'IF(' exp ')' c1" := (CCIf exp c1 CCSkip) (at level 80, right associativity).
Notation "'WHILE(' exp ')' c1" := (CCWhile exp c1) (at level 80, right associativity).
Notation ";" := CCSkip.
Notation "'FOR(' exp1 ';' exp2 ';' exp3 ')' com" := (CCFor exp1 exp2 exp3 com) (at level 80, right associativity).


Open Scope Com_Scope.
(** Notation for command evaluation **)
Reserved Notation " com  '>>' ctx '>>>' ctx' " (at level 40)

(** Evaluation function for commands **)
Inductive  CC_Eval: CCommand-> context -> context->Prop:=
| CC_Eval_Skip: forall ctx,
    CONTINUE >> ctx >>> ctx

| CC_Eval_next: forall c1 c2 ctx ctx' ctx''',
    c1 >> ctx >>> ctx'
    c2 >> ctx' >>> ctx''
    (c1 ; c2) >> ctx >>> ctx''   

| CC_Eval_If_T: forall ctx ctx' exp1 c1 c2,
    E_eval ctx exp1 = CVal n ->
    c1 >> ctx >>> ctx'
    (IF(exp1) c1 ELSE c2) >> ctx >>> ctx'

| CC_Eval_If_F:  forall ctx ctx' exp1 c1 c2,
    E_eval ctx exp1 = CVal 0 ->
    c2 >> ctx >>> ctx'
    (IF(exp1) c1 ELSE c2) >> ctx >>> ctx'

|CC_Eval_While_E: forall ctx exp1 c1,
    E_eval ctx exp1 = CVal 0 ->
    (WHILE(exp1) c1) >> ctx >>> ctx

|CC_Eval_While_L: forall ctx ctx' ctx'' exp1 c1,
    E_eval ctx exp1 = CVal 1 ->
    c1 >> ctx >>> ctx' ->
    (WHILE(exp1) c1) >> ctx' >>> ctx'' ->
    (WHILE(exp1) c1) >> ctx >>> ctx'' 

|CC_Eval_For_E: forall ctx exp1 exp2 exp3 c1,
    E_eval ctx exp2 = CVal 0 ->
    (FOR(exp1;exp2;exp3) c1) >> ctx >>> ctx

|CC_Eval_For_L: forall ctx ctx' ctx'' ctx''' exp1 exp2 exp3 c1,
     E_eval ctx exp1 = CVal n ->
     c1 >> ctx >>> ctx' ->                  
     (FOR(exp1;exp2;exp3) c1) >> ctx' >>> ctx'' ->
     (** Evaluation Line for expression? **) >> ctx'' >>> ctx'''
     (For(exp1;exp2;exp3) c1) >> ctx >>> ctx'''

where " com '>>' ctx '>>>'  ctx'" := (CC_Eval com ctx ctx').
     
