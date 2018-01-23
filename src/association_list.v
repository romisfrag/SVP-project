Require Import Mmx.ast.
Require Import Mmx.binary.
Require Import List.
Import ListNotations.
Require Import Bool.
Require Import Nat Arith.

Definition tag_opcode_assoc :=
  list (tag * structure_op  * nat).

Definition M A := option A.

Definition ret {A} (a : A) : M A := Some a.

Definition bind {A B} (ma : M A)(k : A -> M B): M B :=
  match ma with
  | Some a => k a
  | None => None
  end.

Notation "'let!' x ':=' ma 'in' k" := (bind ma (fun x => k)) (at level 30).   


Fixpoint lookup (t : tag) (l : tag_opcode_assoc) : option nat :=
  match l with
    | [] => None
    | (t',s,n) :: tl => if tag_beq t t' 
                        then Some n
                        else lookup t tl
  end.
Fixpoint lookdown (n : nat) (l : tag_opcode_assoc) : option (tag * structure_op) :=
  match l with
    | [] => None
    | (t,s,n') :: tl => if  beq_nat n n'
                        then Some (t,s)
                        else lookdown n tl
  end.



Definition encdec : tag_opcode_assoc := 
  [
    (Arith ADD Signed, [Reg_s 8;Reg_s 8;Reg_s 8],10);
      (Arith SUB Signed, [Reg_s 8;Reg_s 8;Reg_s 8],11)
  ].    


Print reflect.
Lemma test_reflect : True -> reflect True true.
Proof.
  exact (ReflectT True).
Qed.


Definition tag_to_nat (t : tag) : option nat := lookup t encdec.

Definition nat_to_tag_struct (n : nat) : option (tag*structure_op) := lookdown n encdec.

Theorem lookdown_lookup : forall (n : nat) (s : structure_op) (t : tag),
    lookdown n encdec = Some (t,s) -> lookup t encdec = Some n.
Proof.
Admitted.

Theorem lookup_lookdown : forall (n : nat) (t : tag) (s : structure_op),
    lookup t encdec = Some n -> lookdown n encdec = Some (t,s).
  Admitted.



Lemma tag_to_nat_inv : forall (t : tag) (n : nat) (s : structure_op),
    tag_to_nat t = Some n -> nat_to_tag_struct n = Some (t,s).
Admitted.
Lemma nat_to_tag_inv : forall (t : tag) (n : nat) (s : structure_op),
    nat_to_tag_struct n = Some (t,s) -> tag_to_nat t = Some n.
Admitted.
  