Require Import String.
Require Import Omega.

Class EqDec (A: Type) :=
  {
    dec: forall (x y: A), {x=y} + {x <> y}
  }.

Instance EqDecNat : EqDec nat :=
  {
    dec := Nat.eq_dec
  }.

Instance EqDecString : EqDec string :=
  {
    dec := string_dec
  }.

Definition partial_map A `{EqDec A} (B: Type) := 
  A -> option B.

Definition update {A} `{EqDec A} {B} (h: A) (v: B)  m :=
  fun (x: A) => if (dec x h) then Some v else m x.

Hint Unfold update.

Definition map_pimap {A} `{EqDec A} {B} (f: A -> B -> B) m :=
  fun (x: A) =>
    match m x with
    | None => None
    | Some v => Some (f x v)
    end.

Definition empty {A} `{EqDec A} {B} : partial_map A B :=
  fun _ => None.

Definition map_pmap {A} `{EqDec A} {B} (f: A -> B) m :=
  map_pimap (fun a _ => f a) m.

Notation "'{}'" := (empty)
                     (at level 100, right associativity).

Notation "x '|->' v ';' m" := (update x v m)
                              (at level 100, v at next level, right associativity).

Theorem update_eq: forall {A} `{EqDec A} {B} h v (m: A -> option B),
    (h |-> v; m) h = Some v.
Proof.
  intros. unfold update. destruct (dec h h).
  - reflexivity.
  - contradiction.
Qed.

Theorem update_neq: forall {A} `{EqDec A} {B} h1 h2 v2 (m: A -> option B),
    h1 <> h2 ->
    (h2 |-> v2; m) h1 = m h1.
Proof.
  intros.
  unfold update.
  destruct (dec h1 h2).
  - contradiction.
  - reflexivity.
Qed.

Theorem update_shadow: forall {A} `{EqDec A} {B} h1 h2 v2 (m: A -> option B),
    h1 = h2 ->
    (h2 |-> v2; m) h1 = Some v2.
Proof.
  intros. unfold update.
  destruct (dec h1 h2).
  - reflexivity.
  - contradiction.
Qed.

Theorem map_pimap_correct: forall {A} `{EqDec A} {B} h1 v1 f (m: A -> option B),
    m h1 = Some v1 ->
    (map_pimap f m) h1 = Some (f h1 v1).
Proof.
  intros.
  unfold map_pimap.
  rewrite H0. reflexivity.
Qed.

Theorem map_pimap_neq: forall {A} `{EqDec A} {B} h1 f (m: A -> option B),
    m h1 = None ->
    (map_pimap f m) h1 = None.
Proof.
  intros.
  unfold map_pimap.
  rewrite H0.
  reflexivity.
Qed.
