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
| number
| pointer_singleton (ref: CCore_Type)
| pointer_multi (len: nat) (ref: CCore_Type)
| struct (fields: list CCore_Type).

Inductive CType :=
| unsigned_int
| int
| signed_char
| char
| short
| unsigned_short
| long_min
| long_max
| array (len: nat) (ref: CType)
| bool.

(* TODO: Add integer width **)
Fixpoint reduce_type_sugaring (t: CType): CCore_Type :=
  match t with
  | unsigned_int => number
  | int => number
  | signed_char => number
  | char => number
  | short => number
  | unsigned_short => number
  | long_min => number
  | long_max => number
  | array len ref => pointer_multi len (reduce_type_sugaring ref)
  | bool => number
  end.

