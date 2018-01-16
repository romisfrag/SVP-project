
(* Definition of arithmetiques operations *)
Inductive arith_mode :=
| Signed
| Unsigned
| Float.

Inductive arith_op :=
| ADD : arith_op
| SUB : arith_op.


(* Definition of logic bits  operations *)
Inductive logic_op :=
| OR : logic_op
| AND : logic_op.




(* general tag definition *)
Inductive tag :=
| Arith : arith_op -> arith_mode -> tag
| Logic : logic_op -> tag.



Scheme Equality for tag.


Lemma tag_beq_reflexivity : forall (t :tag), tag_beq t t = true.
Proof.
  destruct t.
  -destruct a; destruct a0; reflexivity.
  -destruct l; reflexivity.
Qed.

Lemma tag_beq_different : forall (t1 t2 : tag), tag_beq t1 t2 = true -> t1 = t2.
Proof.
Admitted.




(* operand definitions *)
Inductive operand :=
| imm : nat -> operand
| reg : nat -> operand.

Inductive operands :=
| unary : operand -> operands
| binary : operand -> operand -> operands
| ternary : operand -> operand -> operand -> operands.


Record instr := mk_instr { instr_opcode : tag;
                           instr_operand : operands }.


(* Binary instruction definitions *)

Definition binary_instruction := list bool.






