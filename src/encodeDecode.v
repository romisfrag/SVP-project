Require Import Mmx.ast.
Require Import Mmx.binary.
Require Import Mmx.association_list.
Require Import List.
Import ListNotations.


(* ------------------------------- Encode --------------------------- *)

Fixpoint encode_operandes_rec (o : operands) (res : list bool) : option (list bool) :=
  match o with
  | [] => Some res
  | (op,size) :: next => let! op_n := (match op with
                                      | imm n => n_bit size n 
                                      | reg n => n_bit size n
                                      end) in
                          encode_operandes_rec next (res ++ op_n)
  end.
Definition encode_operandes (o : operands) : option (list bool) :=
  encode_operandes_rec o [].


Definition encode (i : instr) : option binary_instruction :=
  match i with
  | mk_instr t op => let! nat_tag := tag_to_nat t in
                     let! binary_tag := n_bit 8 nat_tag in 
                     let! binary_op := encode_operandes op in
                     Some (binary_tag ++ binary_op)
  end.





(* ----------------------------- Decode ------------------------- *)
Fixpoint get_first_n_bit  (bi : list bool) (size : nat) : (list bool*list bool) :=
  match size with
  | 0 => ([],bi)
  | S n => match bi with
           | h :: tl => match get_first_n_bit tl n with
                        | (l1,l2) => (h :: l1,l2)
                        end
           | [] => ([],[])
           end
  end.


Fixpoint decode_operandes (op_binary : list bool) (s : structure_op) : operands :=
  match s with
  | [] => []
  | elem_struct :: next => let res := match elem_struct with
                                              | Imm_s siz => let (a,b) := get_first_n_bit op_binary siz in
                                                             (a,siz,b,imm) 
                                              | Reg_s siz => let (a,b) := get_first_n_bit op_binary siz in
                                                             (a,siz,b,reg) 
                                      end in
                           match res with
                           | (l,siz,reste,construct) => let op := bit_n l in
                                                        (construct op, siz) :: decode_operandes reste next
                           end
  end.



