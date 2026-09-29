import Mathlib
import Submission.Work.Compiler.Defs

/-!
# One-step computation lemmas for the compiled TM2 machine

For each instruction of the flat code, the result of a single `Turing.TM2.step` of the machine
`mach code` reading that instruction at label `i`.
-/

set_option autoImplicit false

namespace Work.Compiler

open HvdH Turing

abbrev Cfg (code : List Instr) := TM2.Cfg (Γ code) (Λ code) (MS code)

/-! ## `Option.isSome` reductions -/

@[simp] theorem isSome_none' {α : Type*} : (none : Option α).isSome = false := rfl
@[simp] theorem isSome_some' {α : Type*} (a : α) : (some a).isSome = true := rfl

/-- `cond` applied to an `isSome` test of an empty option. -/
@[simp] theorem cond_isSome_none {α β : Type*} (a b : β) :
    cond ((none : Option α).isSome) a b = b := rfl
/-- `cond` applied to an `isSome` test of a nonempty option. -/
@[simp] theorem cond_isSome_some {α β : Type*} (x : α) (a b : β) :
    cond ((some x : Option α).isSome) a b = a := rfl

/-! ## EvalsToInTime helpers -/

def evalsToInTime_one {σ : Type*} {f : σ → Option σ} {a b : σ} (h : f a = some b) :
    StateTransition.EvalsToInTime f a (some b) 1 :=
  ⟨⟨1, by rw [Function.iterate_one]; exact h⟩, le_refl 1⟩

def EvalsToInTime.mono' {σ : Type*} {f : σ → Option σ} {a : σ} {b : Option σ} {m m' : ℕ}
    (h : StateTransition.EvalsToInTime f a b m) (hmm : m ≤ m') :
    StateTransition.EvalsToInTime f a b m' :=
  ⟨h.toEvalsTo, le_trans h.steps_le_m hmm⟩

/-! ## Instruction steps -/

theorem step_skip (code : List Instr) (i : Λ code)
    (hk : code[(i : ℕ)]? = some Instr.skip) (v : MS code) (S : ∀ j, List (Γ code j)) :
    TM2.step (mach code) ⟨some i, v, S⟩ = some ⟨some (lab code ((i : ℕ) + 1)), v, S⟩ := by
  simp [mach, hk, TM2.step, TM2.stepAux, stmtOf]

theorem step_pop (code : List Instr) (i : Λ code) (k : Stk) (r : Reg)
    (hk : code[(i : ℕ)]? = some (Instr.pop k r)) (v : MS code) (S : ∀ j, List (Γ code j)) :
    TM2.step (mach code) ⟨some i, v, S⟩ = some ⟨some (lab code ((i : ℕ) + 1)),
      {v with reg := Function.update v.reg r ((S (Sum.inl k)).head?.getD Glyph.eos)},
      Function.update S (Sum.inl k) ((S (Sum.inl k)).tail)⟩ := by
  simp [mach, hk, TM2.step, TM2.stepAux, stmtOf]

theorem step_peek (code : List Instr) (i : Λ code) (k : Stk) (r : Reg)
    (hk : code[(i : ℕ)]? = some (Instr.peek k r)) (v : MS code) (S : ∀ j, List (Γ code j)) :
    TM2.step (mach code) ⟨some i, v, S⟩ = some ⟨some (lab code ((i : ℕ) + 1)),
      {v with reg := Function.update v.reg r ((S (Sum.inl k)).head?.getD Glyph.eos)}, S⟩ := by
  simp [mach, hk, TM2.step, TM2.stepAux, stmtOf]

theorem step_push (code : List Instr) (i : Λ code) (k : Stk) (r : Reg)
    (hk : code[(i : ℕ)]? = some (Instr.push k r)) (v : MS code) (S : ∀ j, List (Γ code j)) :
    TM2.step (mach code) ⟨some i, v, S⟩ = some ⟨some (lab code ((i : ℕ) + 1)), v,
      Function.update S (Sum.inl k) (v.reg r :: S (Sum.inl k))⟩ := by
  simp [mach, hk, TM2.step, TM2.stepAux, stmtOf]

theorem step_set (code : List Instr) (i : Λ code) (r : Reg) (c : Glyph)
    (hk : code[(i : ℕ)]? = some (Instr.set r c)) (v : MS code) (S : ∀ j, List (Γ code j)) :
    TM2.step (mach code) ⟨some i, v, S⟩ = some ⟨some (lab code ((i : ℕ) + 1)),
      {v with reg := Function.update v.reg r c}, S⟩ := by
  simp [mach, hk, TM2.step, TM2.stepAux, stmtOf]

theorem step_mov (code : List Instr) (i : Λ code) (d t : Reg)
    (hk : code[(i : ℕ)]? = some (Instr.mov d t)) (v : MS code) (S : ∀ j, List (Γ code j)) :
    TM2.step (mach code) ⟨some i, v, S⟩ = some ⟨some (lab code ((i : ℕ) + 1)),
      {v with reg := Function.update v.reg d (v.reg t)}, S⟩ := by
  simp [mach, hk, TM2.step, TM2.stepAux, stmtOf]

theorem step_test_true (code : List Instr) (i : Λ code) (r : Reg) (c : Glyph) (l : ℕ)
    (hk : code[(i : ℕ)]? = some (Instr.test r c l)) (v : MS code) (S : ∀ j, List (Γ code j))
    (hv : v.reg r = c) :
    TM2.step (mach code) ⟨some i, v, S⟩ = some ⟨some (lab code ((i : ℕ) + 1)), v, S⟩ := by
  simp [mach, hk, TM2.step, TM2.stepAux, stmtOf, hv]

theorem step_test_false (code : List Instr) (i : Λ code) (r : Reg) (c : Glyph) (l : ℕ)
    (hk : code[(i : ℕ)]? = some (Instr.test r c l)) (v : MS code) (S : ∀ j, List (Γ code j))
    (hv : v.reg r ≠ c) :
    TM2.step (mach code) ⟨some i, v, S⟩ = some ⟨some (lab code l), v, S⟩ := by
  simp [mach, hk, TM2.step, TM2.stepAux, stmtOf, hv]

theorem step_jmp (code : List Instr) (i : Λ code) (l : ℕ)
    (hk : code[(i : ℕ)]? = some (Instr.jmp l)) (v : MS code) (S : ∀ j, List (Γ code j)) :
    TM2.step (mach code) ⟨some i, v, S⟩ = some ⟨some (lab code l), v, S⟩ := by
  simp [mach, hk, TM2.step, TM2.stepAux, stmtOf]

theorem step_call (code : List Instr) (i : Λ code)
    (hk : code[(i : ℕ)]? = some Instr.call) (v : MS code) (S : ∀ j, List (Γ code j)) :
    TM2.step (mach code) ⟨some i, v, S⟩ =
      some ⟨some (lab code 0), v,
        Function.update S (Sum.inr 2) (lab code ((i : ℕ) + 1) :: S (Sum.inr 2))⟩ := by
  simp [mach, hk, TM2.step, TM2.stepAux, stmtOf]

theorem step_ret_some (code : List Instr) (i : Λ code) (l : Λ code)
    (hk : code[(i : ℕ)]? = some Instr.ret) (v : MS code) (S : ∀ j, List (Γ code j))
    (hl : (S (Sum.inr 2)).head? = some l) :
    TM2.step (mach code) ⟨some i, v, S⟩ = some ⟨some l, {v with ret := some l},
      Function.update S (Sum.inr 2) (S (Sum.inr 2)).tail⟩ := by
  simp [mach, hk, TM2.step, TM2.stepAux, stmtOf, hl]

theorem step_ret_none (code : List Instr) (i : Λ code)
    (hk : code[(i : ℕ)]? = some Instr.ret) (v : MS code) (S : ∀ j, List (Γ code j))
    (hl : (S (Sum.inr 2)).head? = none) :
    TM2.step (mach code) ⟨some i, v, S⟩ = some ⟨some (labE1 code), {v with ret := none}, S⟩ := by
  simp [mach, hk, TM2.step, TM2.stepAux, stmtOf, hl, labE1, cond_isSome_none]

/-! ## Prologue, epilogue, halt -/

theorem step_prologA_some (code : List Instr) (i : Λ code) (x : InSym)
    (hn : code[(i : ℕ)]? = none) (hi : (i : ℕ) = code.length)
    (v : MS code) (S : ∀ j, List (Γ code j)) (hx : (S (Sum.inr 0)).head? = some x) :
    TM2.step (mach code) ⟨some i, v, S⟩ = some ⟨some (labA code), {v with sym := some x},
      Function.update (Function.update S (Sum.inr 0) (S (Sum.inr 0)).tail) (Sum.inl 1)
        (inpGlyph x :: S (Sum.inl 1))⟩ := by
  simp [mach, hn, hi, labA, prologA, TM2.step, TM2.stepAux, hx]

theorem step_prologA_none (code : List Instr) (i : Λ code)
    (hn : code[(i : ℕ)]? = none) (hi : (i : ℕ) = code.length)
    (v : MS code) (S : ∀ j, List (Γ code j)) (hx : (S (Sum.inr 0)).head? = none) :
    TM2.step (mach code) ⟨some i, v, S⟩ = some ⟨some (labB code), {v with sym := none},
      Function.update S (Sum.inr 0) (S (Sum.inr 0)).tail⟩ := by
  simp [mach, hn, hi, labB, prologA, TM2.step, TM2.stepAux, hx, cond_isSome_none]

theorem step_prologB_some (code : List Instr) (i : Λ code) (g : Glyph)
    (hn : code[(i : ℕ)]? = none) (hi : (i : ℕ) = code.length + 1)
    (v : MS code) (S : ∀ j, List (Γ code j)) (hx : (S (Sum.inl 1)).head? = some g) :
    TM2.step (mach code) ⟨some i, v, S⟩ = some ⟨some (labB code), {v with dat := some g},
      Function.update (Function.update S (Sum.inl 1) (S (Sum.inl 1)).tail) (Sum.inl 0)
        (g :: S (Sum.inl 0))⟩ := by
  simp [mach, hn, hi, labB, prologB, TM2.step, TM2.stepAux, hx]

theorem step_prologB_none (code : List Instr) (i : Λ code)
    (hn : code[(i : ℕ)]? = none) (hi : (i : ℕ) = code.length + 1)
    (v : MS code) (S : ∀ j, List (Γ code j)) (hx : (S (Sum.inl 1)).head? = none) :
    TM2.step (mach code) ⟨some i, v, S⟩ = some ⟨some (lab code 0), {v with dat := none},
      Function.update S (Sum.inl 1) (S (Sum.inl 1)).tail⟩ := by
  simp [mach, hn, hi, prologB, TM2.step, TM2.stepAux, hx, lab, cond_isSome_none]

theorem step_epilogA_some (code : List Instr) (i : Λ code) (g : Glyph)
    (hn : code[(i : ℕ)]? = none) (hi : (i : ℕ) = code.length + 2)
    (v : MS code) (S : ∀ j, List (Γ code j)) (hx : (S (Sum.inl 1)).head? = some g) :
    TM2.step (mach code) ⟨some i, v, S⟩ = some ⟨some (labE1 code), {v with dat := some g},
      Function.update (Function.update S (Sum.inl 1) (S (Sum.inl 1)).tail) (Sum.inl 2)
        (g :: S (Sum.inl 2))⟩ := by
  simp [mach, hn, hi, labE1, epilogA, TM2.step, TM2.stepAux, hx]

theorem step_epilogA_none (code : List Instr) (i : Λ code)
    (hn : code[(i : ℕ)]? = none) (hi : (i : ℕ) = code.length + 2)
    (v : MS code) (S : ∀ j, List (Γ code j)) (hx : (S (Sum.inl 1)).head? = none) :
    TM2.step (mach code) ⟨some i, v, S⟩ = some ⟨some (labE2 code), {v with dat := none},
      Function.update S (Sum.inl 1) (S (Sum.inl 1)).tail⟩ := by
  simp [mach, hn, hi, labE2, epilogA, TM2.step, TM2.stepAux, hx, cond_isSome_none]

theorem step_epilogB_some (code : List Instr) (i : Λ code) (g : Glyph)
    (hn : code[(i : ℕ)]? = none) (hi : (i : ℕ) = code.length + 3)
    (v : MS code) (S : ∀ j, List (Γ code j)) (hx : (S (Sum.inl 2)).head? = some g) :
    TM2.step (mach code) ⟨some i, v, S⟩ = some ⟨some (labE2 code), {v with dat := some g},
      Function.update (Function.update S (Sum.inl 2) (S (Sum.inl 2)).tail) (Sum.inr 1)
        (glyphToBool g :: S (Sum.inr 1))⟩ := by
  simp [mach, hn, hi, labE2, epilogB, TM2.step, TM2.stepAux, hx]

theorem step_epilogB_none (code : List Instr) (i : Λ code)
    (hn : code[(i : ℕ)]? = none) (hi : (i : ℕ) = code.length + 3)
    (v : MS code) (S : ∀ j, List (Γ code j)) (hx : (S (Sum.inl 2)).head? = none) :
    TM2.step (mach code) ⟨some i, v, S⟩ = some ⟨some (labH code), initMS code,
      Function.update S (Sum.inl 2) (S (Sum.inl 2)).tail⟩ := by
  simp [mach, hn, hi, labH, epilogB, TM2.step, TM2.stepAux, hx, initMS, cond_isSome_none]

theorem step_halt (code : List Instr) (i : Λ code)
    (hn : code[(i : ℕ)]? = none) (h0 : (i : ℕ) ≠ code.length)
    (h1 : (i : ℕ) ≠ code.length + 1) (h2 : (i : ℕ) ≠ code.length + 2)
    (h3 : (i : ℕ) ≠ code.length + 3)
    (v : MS code) (S : ∀ j, List (Γ code j)) :
    TM2.step (mach code) ⟨some i, v, S⟩ = some ⟨none, v, S⟩ := by
  simp [mach, hn, h0, h1, h2, h3, TM2.step, TM2.stepAux, epilogA, epilogB]

end Work.Compiler
