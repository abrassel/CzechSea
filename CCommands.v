Require Import CContext
Require Import Types
Require Import Expressions


(** Inductive Type Definitions For Commands **)
Inductive CCommand : Type :=
| CCSkip : CCommand
| CCAssign : id -> CExpression -> CCommand
| CCBreak: CCommand
| CCNext: CCommand -> CCommand -> CCommand
| CIf: CExpression -> CCommand -> CCommand-> CCommand
| CWhile: CExpression -> CCommand -> CCommand
| CFor: CExpression -> CCommand -> CCommand
(** Not Sure About This Section
|CSwitch : CExpression-> CExpression -> CCommand -> CCommand




**)

                                     
