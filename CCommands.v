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

(** Added notations for commands **)                                      
Notation "'CONTINUE'" := CCSkip.
Notation "X '::=' exp" := (CCAssign X exp) (at level 60).
Notation "'BREAK'" := CCBreak.
Notation "com1 ; com2":= (CCNext com1 com2) (at level 80, right associativity).
Notation "'IF(' exp ')' c1 'ELSE' c2" := (CCIf exp c1 c2) (at level 80, right associativity).
Notation "'IF(' exp ')' c1" := (CCIf exp c1 CCSkip) (at level 80, right associativity).
Notation "'WHILE(' exp ')' c1" := (CCWhile exp c1) (at level 80, right associativity).
Notation ";" := CCSkip.
Notation "'FOR(' exp1 ';' exp2 ';' exp3 ')' com" := (CCFor exp1 exp2 exp3 com) (at level 80, right associativity).


(** Notation for context and commands **)

Reserved Notation 


Inductive  CC_Eval: CCommand-> context -> context:=
 | 



