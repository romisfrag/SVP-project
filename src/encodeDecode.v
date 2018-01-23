Require Import Mmx.ast.
Require Import Mmx.binary.
Require Import Mmx.association_list.
Require Import List.
Import ListNotations.


(* ------------------------------- Encode --------------------------- *)

Fixpoint encode_operandes_rec (o : operands) (res : (list bool) * structure_op) : option ((list bool) * structure_op) :=
  match o with
  | [] => Some res
  | (op,size) :: next => let! result := (match op with
                                         | imm n => let! lol := n_bit size n in Some (lol,Imm_s size)
                                         | reg n => let! lol := n_bit size n in Some (lol, Reg_s size)
                                              end) in
                         let (op_n, cons) := result in
                         let (res_a,res_b) := res in
                         encode_operandes_rec next ((res_a ++ op_n),(res_b ++ [cons]))
  end.
Definition encode_operandes (o : operands) : option ((list bool) * structure_op) :=
  encode_operandes_rec o ([],[]).


Definition encode (i : instr) : option binary_instruction :=
  match i with
  | mk_instr t op => let! nat_tag := tag_to_nat t in
                     let! binary_tag := n_bit 8 nat_tag in 
                     let! binary_op_struc := encode_operandes op in
                     let (binary_op,struc) := binary_op_struc in
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


Definition decode (bi : binary_instruction) : option instr :=
  let (tag_binary,next) := get_first_n_bit bi 8 in
  let tag_nat := bit_n tag_binary in
  let! res := nat_to_tag_struct tag_nat in
  let (t,str) := res in 
  let ops := decode_operandes next str in
  Some (mk_instr t ops).
  




 