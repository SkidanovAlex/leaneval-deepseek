import Mathlib
import Submission.HvdH.Interfaces

/-!
# Flat StackLang code, and the TM2 machine that executes it

This file defines the compilation of `HvdH.Cmd` (StackLang) into a flat instruction list, and the
`Turing.TM2` machine that runs such a list.  All the *proofs* of the simulation live in
`Submission/Work/Compiler/Sim.lean`; here we only set up the objects and the "one step of the
machine" computation lemmas.
-/

set_option autoImplicit false

namespace Work.Compiler

open HvdH

/-! ## 1. Flat code -/

/-- Flat instructions.  `test r c l` is "if `reg r = c` fall through, else `goto l`". -/
inductive Instr where
  | skip : Instr
  | pop (k : Stk) (r : Reg) : Instr
  | peek (k : Stk) (r : Reg) : Instr
  | push (k : Stk) (r : Reg) : Instr
  | set (r : Reg) (c : Glyph) : Instr
  | mov (dst src : Reg) : Instr
  | test (r : Reg) (c : Glyph) (l : ℕ) : Instr
  | jmp (l : ℕ) : Instr
  | call : Instr
  | ret : Instr
  deriving DecidableEq, Inhabited

/-- Number of instructions that `compile c pc` has (independent of `pc`). -/
def clen : Cmd → ℕ
  | .skip => 1
  | .pop _ _ => 1
  | .peek _ _ => 1
  | .push _ _ => 1
  | .set _ _ => 1
  | .mov _ _ => 1
  | .seq a b => clen a + clen b
  | .ite _ _ p q => clen p + 1 + clen q + 1
  | .loop _ _ b => clen b + 1 + 1
  | .self => 1

/-- Compile a command to a block of flat code assumed to start at index `pc`. -/
def compile : Cmd → ℕ → List Instr
  | .skip, _ => [.skip]
  | .pop k r, _ => [.pop k r]
  | .peek k r, _ => [.peek k r]
  | .push k r, _ => [.push k r]
  | .set r c, _ => [.set r c]
  | .mov d t, _ => [.mov d t]
  | .seq a b, pc => compile a pc ++ compile b (pc + clen a)
  | .ite r c p q, pc =>
      .test r c (pc + clen p + 2) ::
        (compile p (pc + 1) ++ .jmp (pc + clen p + 2 + clen q) :: compile q (pc + clen p + 2))
  | .loop r c b, pc =>
      .test r c (pc + clen b + 2) :: (compile b (pc + 1) ++ [.jmp pc])
  | .self, _ => [.call]

/-- The whole program of `main`: its compiled block followed by the final `ret`. -/
def progCode (main : Cmd) : List Instr := compile main 0 ++ [Instr.ret]

theorem compile_length : ∀ (c : Cmd) (pc : ℕ), (compile c pc).length = clen c
  | .skip, _ => rfl
  | .pop _ _, _ => rfl
  | .peek _ _, _ => rfl
  | .push _ _, _ => rfl
  | .set _ _, _ => rfl
  | .mov _ _, _ => rfl
  | .seq a b, pc => by
      simp only [compile, List.length_append, clen]
      rw [compile_length a pc, compile_length b (pc + clen a)]
  | .ite r c p q, pc => by
      simp only [compile, List.length_cons, List.length_append, clen]
      rw [compile_length p (pc + 1), compile_length q (pc + clen p + 2)]
      ring
  | .loop r c b, pc => by
      simp only [compile, List.length_cons, List.length_append, List.length_nil, clen]
      rw [compile_length b (pc + 1)]
  | .self, _ => rfl

/-! ## 2. The machine: stacks, labels, states -/

/-- Stack indices of the TM2 machine: `inl k` for the 16 StackLang stacks, `inr 0` the input,
`inr 1` the output, `inr 2` the return-address stack. -/
abbrev KK : Type := Fin 16 ⊕ Fin 3

/-- Labels: `i < code.length` runs instruction `i`; the last four indices are the prologue,
its second phase, the epilogue and the halting label. -/
abbrev Λ (code : List Instr) : Type := Fin (code.length + 5)

/-- The label at (or nearest below) index `l`. -/
def lab (code : List Instr) (l : ℕ) : Λ code :=
  ⟨min l (code.length + 4), Nat.lt_succ_of_le (Nat.min_le_right l (code.length + 4))⟩

/-- Alphabets: the 16 language stacks carry `Glyph`, the input `InSym`, the output `Bool`, and the
return stack carries labels. -/
@[reducible] def Γ (code : List Instr) : KK → Type
  | .inl _ => Glyph
  | .inr ⟨0, _⟩ => InSym
  | .inr ⟨1, _⟩ => Bool
  | .inr _ => Λ code

instance instFintypeGamma0 (code : List Instr) : Fintype (Γ code (Sum.inr 0)) :=
  (inferInstance : Fintype InSym)
instance instInhabitedGamma0 (code : List Instr) : Inhabited (Γ code (Sum.inr 0)) :=
  (inferInstance : Inhabited InSym)

/-- Machine state: the 16 registers, plus three scratch slots. -/
structure MS (code : List Instr) where
  reg : Reg → Glyph
  dat : Option Glyph
  sym : Option InSym
  ret : Option (Λ code)
  deriving Inhabited, Fintype

/-- The initial machine state. -/
def initMS (code : List Instr) : MS code :=
  ⟨fun _ => Glyph.eos, none, none, none⟩

/-- Interpretation of `Bool` from the output stack glyph. -/
def glyphToBool : Glyph → Bool
  | .bit b => b
  | _ => false

/-- The stack vector of the machine, given the StackLang state, the contents of the input stack,
the output stack and the return stack. -/
def toStk (code : List Instr) (s : State) (L0 : List InSym) (L1 : List Bool)
    (rs : List (Λ code)) : ∀ k : KK, List (Γ code k)
  | Sum.inl k => s.stk k
  | Sum.inr ⟨0, _⟩ => L0
  | Sum.inr ⟨1, _⟩ => L1
  | Sum.inr ⟨2, _⟩ => rs

/-! ## 3. The program -/

/-- The label of the prologue's first phase. -/
def labA (code : List Instr) : Λ code := ⟨code.length, by omega⟩
/-- The label of the prologue's second phase. -/
def labB (code : List Instr) : Λ code := ⟨code.length + 1, by omega⟩
/-- The label of the first epilogue phase. -/
def labE1 (code : List Instr) : Λ code := ⟨code.length + 2, by omega⟩
/-- The label of the second epilogue phase. -/
def labE2 (code : List Instr) : Λ code := ⟨code.length + 3, by omega⟩
/-- The label of the halting statement. -/
def labH (code : List Instr) : Λ code := ⟨code.length + 4, by omega⟩

open Turing in
/-- Statement of the prologue, phase A: move the input word from `inr 0` to language stack 1. -/
def prologA (code : List Instr) : TM2.Stmt (Γ code) (Λ code) (MS code) :=
  .pop (Sum.inr 0) (fun σ a => {σ with sym := a})
    (.branch (fun σ => σ.sym.isSome)
      (.push (Sum.inl 1) (fun σ => inpGlyph (σ.sym.getD default))
        (.goto fun _ => ⟨code.length, by omega⟩))
      (.goto fun _ => ⟨code.length + 1, by omega⟩))

open Turing in
/-- Statement of the prologue, phase B: move language stack 1 to language stack 0. -/
def prologB (code : List Instr) : TM2.Stmt (Γ code) (Λ code) (MS code) :=
  .pop (Sum.inl 1) (fun σ a => {σ with dat := a})
    (.branch (fun σ => σ.dat.isSome)
      (.push (Sum.inl 0) (fun σ => σ.dat.getD Glyph.eos)
        (.goto fun _ => ⟨code.length + 1, by omega⟩))
      (.goto fun _ => lab code 0))

open Turing in
/-- Statement of the first epilogue phase: move language stack 1 to language stack 2 (reversing). -/
def epilogA (code : List Instr) : TM2.Stmt (Γ code) (Λ code) (MS code) :=
  .pop (Sum.inl 1) (fun σ a => {σ with dat := a})
    (.branch (fun σ => σ.dat.isSome)
      (.push (Sum.inl 2) (fun σ => σ.dat.getD Glyph.eos)
        (.goto fun _ => ⟨code.length + 2, by omega⟩))
      (.goto fun _ => ⟨code.length + 3, by omega⟩))

open Turing in
/-- Statement of the second epilogue phase: move language stack 2 to the output stack `inr 1`
(reversing back, so the order is preserved). -/
def epilogB (code : List Instr) : TM2.Stmt (Γ code) (Λ code) (MS code) :=
  .pop (Sum.inl 2) (fun σ a => {σ with dat := a})
    (.branch (fun σ => σ.dat.isSome)
      (.push (Sum.inr 1) (fun σ => glyphToBool (σ.dat.getD Glyph.eos))
        (.goto fun _ => ⟨code.length + 3, by omega⟩))
      (.load (fun _ => initMS code) (.goto fun _ => ⟨code.length + 4, by omega⟩)))

open Turing in
/-- Statement of the instruction at index `i`. -/
def stmtOf (code : List Instr) (i : ℕ) : Instr → TM2.Stmt (Γ code) (Λ code) (MS code)
  | .skip => .goto fun _ => lab code (i + 1)
  | .pop k r =>
      .pop (Sum.inl k) (fun σ a => {σ with reg := Function.update σ.reg r (a.getD Glyph.eos)})
        (.goto fun _ => lab code (i + 1))
  | .peek k r =>
      .peek (Sum.inl k) (fun σ a => {σ with reg := Function.update σ.reg r (a.getD Glyph.eos)})
        (.goto fun _ => lab code (i + 1))
  | .push k r => .push (Sum.inl k) (fun σ => σ.reg r) (.goto fun _ => lab code (i + 1))
  | .set r c => .load (fun σ => {σ with reg := Function.update σ.reg r c})
      (.goto fun _ => lab code (i + 1))
  | .mov d t => .load (fun σ => {σ with reg := Function.update σ.reg d (σ.reg t)})
      (.goto fun _ => lab code (i + 1))
  | .test r c l => .branch (fun σ => decide (σ.reg r = c)) (.goto fun _ => lab code (i + 1))
      (.goto fun _ => lab code l)
  | .jmp l => .goto fun _ => lab code l
  | .call => .push (Sum.inr 2) (fun _ => lab code (i + 1)) (.goto fun _ => lab code 0)
  | .ret =>
      .peek (Sum.inr 2) (fun σ o => {σ with ret := o})
        (.branch (fun σ => σ.ret.isSome)
          (.pop (Sum.inr 2) (fun σ o => {σ with ret := o})
            (.goto fun σ => σ.ret.getD (lab code 0)))
          (.goto fun _ => ⟨code.length + 2, by omega⟩))

open Turing in
/-- The machine.  Label `i` runs instruction `i` of `code` if there is one, and otherwise the
prologue phase A (`i = code.length`), phase B, the epilogue, or the halting statement. -/
def mach (code : List Instr) (i : Λ code) : TM2.Stmt (Γ code) (Λ code) (MS code) :=
  match code[(i : ℕ)]? with
  | some ins => stmtOf code (i : ℕ) ins
  | none =>
    if (i : ℕ) = code.length then prologA code
    else if (i : ℕ) = code.length + 1 then prologB code
    else if (i : ℕ) = code.length + 2 then epilogA code
    else if (i : ℕ) = code.length + 3 then epilogB code
    else .halt

open Turing in
/-- The bundled `FinTM2` machine running `code`, with input alphabet `InSym` on `Sum.inr 0` and
output alphabet `Bool` on `Sum.inr 1`. -/
def toTM2 (code : List Instr) : FinTM2 where
  K := KK
  kDecidableEq := inferInstance
  kFin := inferInstance
  k₀ := Sum.inr 0
  k₁ := Sum.inr 1
  Γ := Γ code
  Λ := Λ code
  main := labA code
  ΛFin := inferInstance
  σ := MS code
  initialState := initMS code
  σFin := inferInstance
  Γk₀Fin := inferInstance
  m := mach code

end Work.Compiler
