Require Import CContext.
Require Import Types.
Require Import String.
Require Import Maps.

(* at its core, everything in C can be modeled as a natural **)
Definition CCore_Value :=
  nat.

Inductive CCore_exp :=
| CVal: CCore_Value -> CCore_exp
| CAddr: string -> CCore_exp 
| CVar: string -> CCore_exp
| CPlus: CCore_exp -> CCore_exp -> CCore_exp
| CMinus: CCore_exp -> CCore_exp -> CCore_exp
| CMult: CCore_exp -> CCore_exp -> CCore_exp
(* | CDiv: CCore_exp -> CCore_exp -> CCore_exp **)
| CEq: CCore_exp -> CCore_exp -> CCore_exp
| CLt: CCore_exp -> CCore_exp -> CCore_exp
| CAnd: CCore_exp -> CCore_exp -> CCore_exp
| CPtr: CCore_Value -> CCore_exp
(* | CStruct: forall xl, struct xl -> string -> CCore_exp.
 how do I do this? **)
| CStruct: string -> string -> CCore_exp.

Inductive C_exp :=
| C_mod: C_exp -> C_exp -> C_exp (* a % b **)
| C_u_plus: C_exp -> C_exp (* +a **)
| C_u_min: C_exp -> C_exp (* -a **)
| C_neq: C_exp -> C_exp -> C_exp (* a != b **)
| C_gt: C_exp -> C_exp -> C_exp (* a > b **)
| C_ge: C_exp -> C_exp -> C_exp (* a >= b **)
| C_le: C_exp -> C_exp -> C_exp (*a <= b **)
| C_not: C_exp -> C_exp (* !a **)
| C_or: C_exp -> C_exp -> C_exp (* a || b **)
| C_deref: CCore_Value -> C_exp -> C_exp (* A[b] **)
| C_arrow: CCore_Value -> string -> C_exp
| C_tern: C_exp -> C_exp -> C_exp -> C_exp (* a ? b : c **).

Bind Scope Exp_scope with C_exp.
Bind Scope Exp_scope with CCore_exp.
Delimit Scope Exp_scope with Ccom.

Notation "a '_[_' b '_]'"
  := (C_mod a b) (at level 105, left associativity) : Exp_scope.

Notation "a '_._' b"
  := (CStruct a b) (at level 105, left associativity) : Exp_scope.

Notation "a '_->_' b"
  := (C_arrow a b) (at level 105, left associativity) : Exp_scope.

Notation "'+_' a"
  := (C_u_plus a) (at level 80) :  Exp_scope.

Notation "'-_' a"
  := (C_u_min a) (at level 80) : Exp_scope.

Notation "'!_' a"
  := (C_not a) (at level 80) : Exp_scope.

Notation "'*_' a"
  := (CPtr a) (at level 80) : Exp_scope.

Notation "'&_' a"
  := (CAddr a) (at level 80) : Exp_scope.

Notation "a '_*_' b"
  := (CMult a b) (at level 50, left associativity) : Exp_scope.

Notation "a '_%_' b"
  := (CMult a b) (at level 50, left associativity) : Exp_scope.

Notation "a '_+_' b"
  := (CPlus a b) (at level 50, left associativity) : Exp_scope.

Notation "a '_-_' b"
  := (CMinus a b) (at level 50, left associativity) : Exp_scope.

Notation "a '_==_' b"
  := (CEq a b) (at level 38, left associativity) : Exp_scope.

Notation "a '_!=_' b"
  := (C_neq a b) (at level 38, left associativity) : Exp_scope.

Notation "a '_<_' b"
  := (CLt a b) (at level 38, left associativity) : Exp_scope.

Notation "a '_<=_' b"
  := (C_le a b) (at level 38, left associativity) : Exp_scope.

Notation "a '_>_' b"
  := (C_gt a b) (at level 38, left associativity) : Exp_scope.

Notation "a '_>=_' b"
  := (C_ge a b) (at level 38, left associativity) : Exp_scope.

Notation "a _&&_ b"
  := (CAnd a b) (at level 25, left associativity) : Exp_scope.

Notation "a _||_ b"
  := (C_or a b) (at level 24, left associativity) : Exp_scope.

Notation "a _?_ b _:_ c"
  := (C_tern a b c) (at level 23, right associativity) : Exp_scope.

Open Scope Exp_scope.
Reserved Notation " ctx '>>' exp '>>>' exp'" (at level 40).
Inductive E_eval : context -> CCore_exp -> CCore_exp -> Prop :=
| E_Eval_Var_s: forall s st h ht ctx str n,
    space s st h ht = ctx ->
    lookup_s s st str = Some n ->
    ctx >> CVar str >>> CVal n
| E_Eval_Var_h: forall s st h ht ctx str n,
    space s st h ht = ctx ->
    lookup_h h ht str = Some n ->
    ctx >> CVar str >>> CVal n
| E_Eval_Addr_s: forall s st h ht ctx str addr,
    space s st h ht = ctx ->
    addr_s st str = Some addr ->
    ctx >> &_ str >>> CVal addr
| E_Eval_Addr_h: forall s st h ht ctx str addr,
    space s st h ht = ctx ->
    addr_h ht str = Some addr ->
    ctx >> &_ str >>> CVal addr
| E_Eval_Plus_l: forall ctx (expl expl' expr: CCore_exp),
    ctx >> expl >>> expl' ->
    ctx >> (expl _+_ expr) >>> (expl' _+_ expr)
| E_Eval_Plus_r: forall ctx expl expr expr',
    ctx >> expr >>> expr' ->
    ctx >> (expl _+_ expr) >>> (expl _+_ expr')
| E_Eval_Plus_c: forall ctx n1 n2,
    ctx >>  ((CVal n1) _+_ (CVal n2)) >>> CVal (n1 + n2)
| E_Eval_Min_l: forall ctx expl expl' expr,
    ctx >> expl >>> expl' ->
    ctx >> (expl _-_ expr) >>> (expl' _-_ expr)
| E_Eval_Min_r: forall ctx expl expr expr',
    ctx >> expr >>> expr' ->
    ctx >> (expl _-_ expr) >>> (expl _-_ expr')
| E_Eval_Min_c: forall ctx n1 n2,
    ctx >> ((CVal n1) _-_ (CVal n2)) >>> CVal (n1 - n2)
| E_Eval_Mult_l: forall ctx expl expl' expr,
    ctx >> expl >>> expl' ->
    ctx >> (expl _*_ expr) >>> (expl' _*_ expr)
| E_Eval_Mult_r: forall ctx expl expr expr',
    ctx >> expr >>> expr' ->
    ctx >> (expl _*_ expr) >>> (expl _*_ expr')
| E_Eval_Mult_c: forall ctx n1 n2,
    ctx >> ((CVal n1) _*_ (CVal n2)) >>> CVal (n1 * n2)
| E_Eval_Eq_l: forall ctx expl expl' expr,
    ctx >> expl >>> expl' ->
    ctx >> (expl _==_ expr) >>> (expl' _==_ expr)
| E_Eval_Eq_r: forall ctx expl expr expr',
    ctx >> expr >>> expr' ->
    ctx >> (expl _==_ expr) >>> (expl _==_ expr')
| E_Eval_Eq_c_tru: forall ctx n1 n2,
    n1 = n2 -> 
    ctx >> ((CVal n1) _==_ (CVal n2)) >>> CVal 0
| E_Eval_Eq_c_fls: forall ctx n1 n2,
    n1 <> n2 ->
    ctx >> ((CVal n1) _==_ (CVal n2)) >>> CVal 1
| E_Eval_Lt_l: forall ctx expl expl' expr,
    ctx >> expl >>> expl' ->
    ctx >> (expl _<_ expr) >>> (expl' _<_ expr)
| E_Eval_Lt_r: forall ctx expl expr expr',
    ctx >> expr >>> expr' ->
    ctx >> (expl _<_ expr) >>> (expl _<_ expr')
| E_Eval_Lt_c_tru: forall ctx n1 n2,
    n1 < n2 -> 
    ctx >> ((CVal n1) _<_ (CVal n2)) >>> CVal 0
| E_Eval_Lt_c_fls: forall ctx n1 n2,
    n1 >= n2 ->
    ctx >> ((CVal n1) _<_ (CVal n2)) >>> CVal 1
| E_Eval_And_l: forall ctx expl expl' expr,
    ctx >> expl >>> expl' ->
    ctx >> (expl _&&_ expr) >>> (expl' _&&_ expr)
| E_Eval_And_r: forall ctx expl expr expr',
    ctx >> expr >>> expr' ->
    ctx >> (expl _&&_ expr) >>> (expl _&&_ expr')
| E_Eval_And_c_tru: forall ctx n1 n2,
    n1 = 0 /\ n2 = 0 -> 
    ctx >> ((CVal n1) _&&_ (CVal n2)) >>> CVal 0
| E_Eval_And_c_fls: forall ctx n1 n2,
    n1 <> 0 \/ n2 <> 0 ->
    ctx >> ((CVal n1) _&&_ (CVal n2)) >>> CVal 1
| E_Eval_Ptr_s: forall s st h ht ctx ptr n,
    space s st h ht = ctx ->
    get_val_s s ptr = Some n ->
    ctx >> *_ ptr >>> CVal n
| E_Eval_Ptr_h: forall s st h ht ctx ptr n,
    space s st h ht = ctx ->
    get_val_h h ptr = Some n ->
    ctx >> *_ ptr >>> CVal n
| E_EVal_Struct_s: forall s st h ht ctx s_name s_var var val,
    query_struct_space ctx s_name s_var = Some var ->
    space s st h ht = ctx ->
    lookup_s s st var = Some val ->
    ctx >> (s_var _._ var) >>> CVal val

where " ctx '>>' exp '>>>' exp'" := (E_eval ctx exp exp').

    
    
  
