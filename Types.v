Require Import CContext.

(* We are going to take advantage of extensive syntactical sugaring in C to develop a set of core types which all other types can be derived from.

  Using this, we hope to significantly reduce the footprint of our proofs.  We define below a core set of types which all other types can be interpreted as syntactical sugar of.
 **)

(*
  Our principle goal with our typing system is to provide
  flexibility for future extensions.  

  Some notes: we define a pointer based on its underlying reference
  We define a struct based on the subfields it contains 
**)
Inductive CCore_Type :=
| void
| number (signed: bool).
(* | pointer (ref: CCore_Type). (* no support for arrays yet **) **)

Inductive CType :=
| unsigned_int
| int
| signed_char
| char
| short
| unsigned_short
| long_unsigned
| long_signed
| bool.
(* | array (len: nat) (ref: CType) Later **)


(* TODO: Add integer width **)
Fixpoint reduce_type_sugaring (t: CType): CCore_Type :=
  match t with
  | unsigned_int => number false
  | int => number true
  | signed_char => number true
  | char => number false
  | short => number true
  | unsigned_short => number false
  | long_unsigned => number false
  | long_signed => number true
  | bool => number false                  
(*  | array len ref => pointer len (reduce_type_sugaring ref) **)
  end.
  



