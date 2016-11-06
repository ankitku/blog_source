---
title: Mechanizing the Metatheory of TAL-0 Language
author: Ankit
---

 Based on paper by Greg Morrisett , TAL-0 is the design of a RISC-style typed assembly language which focuses on control-flow safety. This post provides a mechanized metatheory, particularly a machine checked proof of soundness of the TAL-0 type system as proposed by the author in section 4.2.10 of the book Advanced Topics in Types and Programming Languages.

 The TAL-0 language runs on an abstract machine which is represented by 3 components :

1. A heap H which is a finite, partial map from labels to heap values

2. a register file R which is a total map from registers to values, and 

3. a current instruction sequence I.  

An example state of the abstact machine is shown below:
<img src="http://i288.photobucket.com/albums/ll170/_ankitku/TAL0/TAl_zpsq0tw1ps8.png" height: 70%;" />

We denote addresses of instructions stored in the heap as labels. Unlike a typical machine where labels are resolved to some machine address, which are integers, we maintain a distinction between labels and arbit integers, as this complies with our goal to state and prove the control-flow safety i.e. we can only branch to a valid label, and not to any arbit integer. This will ensure that the machine never gets stuck while trying to do some invalid operation.

```coq
Inductive aexp : Type :=
 | ANum : nat -> aexp
 | AReg : nat -> aexp
 | ALab : nat -> aexp.

Fixpoint aeval (a : aexp) (R : registers) : nat :=
  match a with
 | ANum n => n
 | AReg d => R (Id d)
 | ALab l => l
  end.
```
State of the machine is defined using the triple H, R and I:
```coq
Inductive st : Type :=
 | St : heaps -> registers -> instr -> st.
```

Instructions defined as follows :
```coq
Inductive instr : Type :=
 | IMov : forall d : nat,
    aexp -> instr
 | IAdd : forall d s : nat,
    instr
 | ISub : forall d v : nat,
    instr
 | IIf : forall d : nat,
    aexp -> instr
 | ISeq : instr -> instr -> instr
 | IJmp : aexp -> instr.
```

Evaluation of instructions is supposed to change the Machine State and
thus some of its components H, R or I. These changes are recorded as
relations between initial and final state of the machine.
```coq
Inductive ieval : st -> st -> Prop :=
 | R_IMov : forall H R I d a,
    ieval (St H R (R(d) := a ;; I)) (St H (t_update R (Id d) a) I)
 | R_IAdd : forall H R I d s,
     ieval (St H R (R(d) +:= R(s) ;; I)) (St H (t_update R (Id d) (aeval (AReg d) R + aeval (AReg s) R)) I)
 | R_ISub : forall H R I d v,
     ieval (St H R (R(d) -:= v ;; I)) (St H (t_update R (Id d) (aeval (AReg d) R - aeval (ANum v) R)) I)
 | R_IJmp_Succ : forall H R I' a l,
     l = (aeval a R) -> H (Id l) = Some I' -> ieval (St H R (JMP l)) (St H R I')
 | R_IJmpR_Succ : forall H R I' r,
     H (Id (R (Id r))) = Some I' -> ieval (St H R (JMP R(r))) (St H R I')
 | R_IJmp_Fail : forall H R I a,
     H (Id (aeval a R)) = None -> ieval (St H R I) (St H R I)
 | R_IIf_EQ : forall H R I I2 r v,
     aeval (AReg r) R = 0 -> (H (Id v)) = Some I2 -> ieval (St H R (JIF R(r) v ;; I)) (St H R I2)
 | R_IIf_NEQ : forall H R I r v,
     aeval (AReg r) R <> 0 -> ieval (St H R (JIF R(r) v ;; I)) (St H R I)   
 | R_ISeq : forall st st' st'',
     ieval st st' -> ieval st' st'' -> ieval st st''
 | R_IStuck : forall st, ieval st st.
```


##The Type System of TAL-0

The types consist of

1. int -> represents arbit integer stored in a register

2. reg -> a type constructor. Takes as input, the type of the register, to which this register is pointing.

3. code -> takes as input a typing context Gamma, and gives type (code Gamma) which is the type of an instruction sequence that expects type of the Register file to be Gamma before it begins execution 

4. arrow -> represents type of a single instruction (excluding JMP), which expects register file of type Gamma1 before execution, and changes it to Gamma2 after it has executed.

5. True (T in unicode) -> It is the super type. It is used to represent the type of a register in R, which contains the label of the instruction currently executing. Because in such a case, we have the equation : Gamma (r) = code Gamma, which in the absence of subtyping or polymorphic types can't be solved. Hence T is assigned the type for such a register as it subsumes all types including itself. When we jump through a register of type T, we forget the type assigned to it, and reassign T to it. Morrisett's paper uses the polymorphic type for due to some more benefits it affords. However we have used T type for its simplicity.

```coq
Inductive ty : Type :=
 | int : ty
 | reg : ty -> ty
 | code : partial_map ty -> ty
 | arrow : partial_map ty -> partial_map ty -> ty
 | True : ty.
```

Contexts are mappings between values and types. For values in Heaps,
their corresponding types are found in Psi, and for values in
Registers, their corresponding types are found in Gamma.
```coq
Definition context := partial_map ty.
```
#Typing Rules

Psi is a partial map containing types of instruction sequences. As all
instruction sequences end in a JMP statement, all valid values in Psi
are Some (code Gamma) where Gamma is the initial type state of
register expected by that instruction sequence. Now, typing rules may
require presence of either both Psi and Gamma, or only Psi or
neither. Hence, we introduce a combined context structure, that
handles all the 3 cases.

```coq
Inductive cmbnd_ctx :=
 | EmptyCtx : cmbnd_ctx
 | PsiCtx : context -> cmbnd_ctx
 | PsiGammaCtx : context -> context -> cmbnd_ctx.
```

<img
src="http://i288.photobucket.com/albums/ll170/_ankitku/TAL0/Screen%20Shot%202016-11-03%20at%2023.46.21_zpsi2vjatvk.png">

(the above image is taken from Morrisett's paper, defining the typing rules for TAL-0)

Typing rules for arithmetic expressions :
```coq
Inductive ahas_type : cmbnd_ctx -> aexp -> ty -> Prop :=
 | S_Int : forall Psi n,
     ahas_type (PsiCtx Psi) (ANum n) int
 | S_Lab : forall Psi Gamma l v R,
     Psi (Id l) = Some (code Gamma) -> l = aeval (ALab v) R -> ahas_type (PsiCtx Psi) (ALab v) (code Gamma)
 | S_Reg : forall Psi Gamma r,
     Gamma (Id r) = Some (reg int) -> ahas_type (PsiGammaCtx Psi Gamma) (AReg r) (reg int)
 | S_RegV : forall Psi Gamma r,
     ahas_type (PsiGammaCtx Psi Gamma) (AReg r) (reg (code Gamma))
 | S_RegT : forall Psi Gamma r,
     ahas_type (PsiGammaCtx Psi Gamma) (AReg r) True
 | S_Val : forall Psi Gamma a tau,
     ahas_type (PsiCtx Psi) a tau -> ahas_type (PsiGammaCtx Psi Gamma) a tau.
```

Typing rules for instructions :
```coq
Inductive ihas_type : cmbnd_ctx -> instr -> ty -> Prop :=
 | S_Jmp :  forall Psi Gamma v,
     ahas_type (PsiGammaCtx Psi Gamma) (ALab v) (code Gamma) -> ihas_type (PsiCtx Psi) (JMP v) (code Gamma)
 | S_JmpT :  forall Psi Gamma v,
     ahas_type (PsiGammaCtx Psi Gamma) (AReg v) True -> ihas_type (PsiCtx Psi) (JMP R(v)) (code Gamma)
 | S_Mov : forall Psi Gamma R d a tau,
    ahas_type (PsiGammaCtx Psi Gamma) a tau -> ahas_type (PsiGammaCtx Psi Gamma) (AReg d) (reg tau) -> (update Gamma (Id d) (reg tau)) = Gamma -> ihas_type (PsiCtx Psi) (R(d) := aeval a R) (arrow Gamma Gamma)
 | S_Add : forall Psi Gamma d s,
    ahas_type (PsiGammaCtx Psi Gamma) (AReg s) (reg int) -> ahas_type (PsiGammaCtx Psi Gamma) (AReg d) (reg int) -> update Gamma (Id d) (reg int) = Gamma -> ihas_type (PsiCtx Psi) (R(d) +:= R(s)) (arrow Gamma Gamma)
 | S_Sub : forall Psi Gamma s a v,
      ahas_type (PsiGammaCtx Psi Gamma) a int -> ahas_type (PsiGammaCtx Psi Gamma) (AReg s) (reg int) -> a = ANum v -> ihas_type (PsiCtx Psi) (R(s) -:= v) (arrow Gamma Gamma)
 | S_If :  forall Psi Gamma r v,
     ahas_type (PsiGammaCtx Psi Gamma) (AReg r) (reg int) -> ahas_type (PsiGammaCtx Psi Gamma) (ALab v) (code Gamma) -> ihas_type (PsiCtx Psi) (JIF R(r) v) (arrow Gamma Gamma)
 | S_Seq :  forall Psi i1 i2 Gamma Gamma2,
     ihas_type (PsiCtx Psi) i1 (arrow Gamma Gamma2) -> ihas_type (PsiCtx Psi) i2 (code Gamma2) -> ihas_type (PsiCtx Psi) (ISeq i1 i2) (code Gamma).
```

#Typing of Heaps, Registers and validity of machine
We say that machine is OK, i.e. in a valid state iff H has type Psi, R
has type Gamma and current instruction being executed has type "code Gamma".
```coq
Inductive Rhas_type : cmbnd_ctx -> registers -> context -> Prop :=
 | S_Regfile : forall Psi Gamma R r tau a, (Gamma (Id r)) = Some tau
 -> aeval a R = R (Id r) -> ahas_type (PsiGammaCtx Psi Gamma) a tau ->
 Rhas_type (PsiCtx Psi) R Gamma.

Inductive Hhas_type : cmbnd_ctx -> heaps -> context -> Prop :=
  | S_Heap : forall Psi H, (forall l tau, exists i, Psi (Id l) = Some
  tau /\ H (Id l) = Some i /\ ihas_type (PsiCtx Psi) i tau) ->
  Hhas_type EmptyCtx H Psi.

Inductive M_ok : cmbnd_ctx -> heaps -> registers -> instr -> Prop :=
 | S_Mach : forall H R I Psi Gamma, Hhas_type EmptyCtx H Psi -> Rhas_type (PsiCtx Psi) R Gamma -> ihas_type (PsiCtx Psi) I (code Gamma) -> M_ok EmptyCtx H R I.
```

Some canonical values lemmas we will need in proving Soundness of the
type system.
```coq
Lemma Canonical_Values_Int : forall H Psi Gamma v tau, Hhas_type EmptyCtx H Psi -> ahas_type (PsiGammaCtx Psi Gamma) v tau -> tau = int -> exists n, v = ANum n.

Lemma Canonical_Values_Reg :forall H Psi Gamma r R, Hhas_type EmptyCtx
H Psi -> Rhas_type (PsiCtx Psi) R Gamma -> ahas_type (PsiGammaCtx Psi
Gamma) (AReg r) (reg int) -> exists (n : nat), R (Id r) = n.

Lemma Canonical_Values_label1 : forall H Psi Gamma v, Hhas_type
EmptyCtx H Psi -> ahas_type (PsiGammaCtx Psi Gamma) (ALab v) (code
Gamma) ->  Psi (Id v) = Some (code Gamma) -> exists i, H (Id v) = Some
i /\ ihas_type (PsiCtx Psi) i (code Gamma).

Lemma Canonical_Values_label2 : forall H Psi Gamma R r, Hhas_type EmptyCtx H Psi -> ahas_type (PsiGammaCtx Psi Gamma) (AReg r) True -> exists i, H (Id (R (Id r))) = Some i /\ ihas_type (PsiCtx Psi) i (code Gamma).
```

Proving safety of the type system requires proving

1. Progress : A well typed machine state (M_ok M(H,R,I)) doesn't get
stuck. eg. It will never try to jump to an arbit integer, which we
wanted as part of control flow safety.
2. Preservation : After each transition to a new machine state
M'(H',R',I'), the new state is also well typed.

Hence the soundness theorem is stated as follows :
```coq
Theorem Soundness : forall H R I, M_ok EmptyCtx H R I -> exists H' R'
I', ieval (St H R I) (St H' R' I') /\ M_ok EmptyCtx H' R' I'.
```

Complete proofs can be found [here][src].


[src]:https://github.com/ankitku/awotap/blob/master/TAL.v





-
