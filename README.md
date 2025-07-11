## Rocq Compiler
This P4C extension converts certain P4 programs to ROCQ code.

## Limitations
#### Imports
File imports are done statically `coqOutput << "From MyProject Require Import SmtExpr.\n";`
#### Headers
One header can be used and will be entitled `header_{name}` where name is the P4 name.
#### Actions
Unlimited actions may be added, but they are currently limited to constant assignment through addition to zero. They will be named `{name}_op` where name is the p4 name.
#### Tables
For all of the tables you will get the following:
```
(* Table: the_table_0 *)
Definition the_table_0_seq_rule : SeqRule := 
  SeqCtr [(header_H, repr 0%Z)] [MyAction1_op].

Definition the_table_0_rule : MatchActionRule := 
  Seq the_table_0_seq_rule.
```
- the_table_0: P4's name for your table
- header_H: the name of the program's header
- \[MyAction1_op\]: a list of actions to be applied to the table
#### State
Program state is statically generated:
```
(* THE SIMPLEST POSSIBLE ProgramState SmtArithExpr *)
(* We have been operating on stateless only so far so this is a dummy instance to satisfy the compiler.*)
Definition simplest_state : ProgramState SmtArithExpr := {|
ctrl_plane_map := fun _ => SmtConst (repr 0%Z);
header_map := fun _ => SmtConst (repr 0%Z);
state_var_map := fun _ => SmtConst (repr 0%Z)
|}.
```
#### Equivalence checker
The equivalence checker checks the first defined rule against itself.

## Usage (not accurate for first time)
cd build
cmake -DCMAKE_BUILD_TYPE=Debug ..
make -j8