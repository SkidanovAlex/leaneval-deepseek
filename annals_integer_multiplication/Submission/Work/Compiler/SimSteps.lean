import Submission.Work.Compiler.Sim

/-!
# One-instruction simulations, in `EIT` form

Each instruction of the flat code, applied at a position `pc` with the machine configuration written
in terms of `toStk`, reaches the next configuration in exactly one machine step.  These are the
building blocks of the main simulation theorem (`simulate`).
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Work.Compiler

open HvdH Turing StateTransition

/-- `toStk` does not depend on the registers. -/
theorem toStk_reg (code : List Instr) (rg : Reg → Glyph) (s : State) (L0 : List InSym)
    (L1 : List Bool) (rs : List (Λ code)) :
    toStk code ⟨rg, s.stk⟩ L0 L1 rs = toStk code s L0 L1 rs := rfl

/-- Updating the language stack `k` and the registers of `s`. -/
theorem toStk_pop (code : List Instr) (s : State) (k : Stk) (r : Reg) (y : Glyph)
    (L0 : List InSym) (L1 : List Bool) (rs : List (Λ code)) :
    toStk code ⟨Function.update s.reg r y, Function.update s.stk k (s.stk k).tail⟩ L0 L1 rs
      = Function.update (toStk code s L0 L1 rs) (Sum.inl k) (s.stk k).tail := by
  funext j
  cases j with
  | inl j =>
      show Function.update s.stk k (s.stk k).tail j
        = Function.update (toStk code s L0 L1 rs) (Sum.inl k) (s.stk k).tail (Sum.inl j)
      by_cases h : j = k
      · subst h; rw [Function.update_self, Function.update_self]
      · rw [Function.update_of_ne h, Function.update_of_ne (by simpa using h)]
        rfl
  | inr j => fin_cases j <;> simp [toStk, Function.update]

def eit_skip (code : List Instr) (pc : ℕ) (hpc : pc ≤ code.length) (hpc1 : pc + 1 ≤ code.length)
    (hk : code[pc]? = some Instr.skip) (σ : MS code) (s : State)
    (L0 : List InSym) (L1 : List Bool) (rs : List (Λ code)) :
    EIT code ⟨some (labOf code pc hpc), σ, toStk code s L0 L1 rs⟩
      ⟨some (labOf code (pc + 1) hpc1), σ, toStk code s L0 L1 rs⟩ 1 := by
  have hk' : code[((labOf code pc hpc : Λ code) : ℕ)]? = some Instr.skip := hk
  refine eit_one ?_
  rw [step_skip code (labOf code pc hpc) hk' σ (toStk code s L0 L1 rs)]
  rw [show ((labOf code pc hpc : Λ code) : ℕ) + 1 = pc + 1 from rfl, lab_mk code hpc1]

def eit_pop (code : List Instr) (pc : ℕ) (hpc : pc ≤ code.length) (hpc1 : pc + 1 ≤ code.length)
    (k : Stk) (r : Reg) (hk : code[pc]? = some (Instr.pop k r))
    (σ : MS code) (s : State) (L0 : List InSym) (L1 : List Bool) (rs : List (Λ code)) :
    EIT code ⟨some (labOf code pc hpc), σ, toStk code s L0 L1 rs⟩
      ⟨some (labOf code (pc + 1) hpc1),
        {σ with reg := Function.update σ.reg r ((s.stk k).head?.getD Glyph.eos)},
        toStk code ⟨Function.update s.reg r ((s.stk k).head?.getD Glyph.eos),
          Function.update s.stk k (s.stk k).tail⟩ L0 L1 rs⟩ 1 := by
  have hk' : code[((labOf code pc hpc : Λ code) : ℕ)]? = some (Instr.pop k r) := hk
  refine eit_one ?_
  rw [step_pop code (labOf code pc hpc) k r hk' σ (toStk code s L0 L1 rs)]
  rw [show ((labOf code pc hpc : Λ code) : ℕ) + 1 = pc + 1 from rfl, lab_mk code hpc1, toStk_pop]
  try rfl

def eit_peek (code : List Instr) (pc : ℕ) (hpc : pc ≤ code.length) (hpc1 : pc + 1 ≤ code.length)
    (k : Stk) (r : Reg) (hk : code[pc]? = some (Instr.peek k r))
    (σ : MS code) (s : State) (L0 : List InSym) (L1 : List Bool) (rs : List (Λ code)) :
    EIT code ⟨some (labOf code pc hpc), σ, toStk code s L0 L1 rs⟩
      ⟨some (labOf code (pc + 1) hpc1),
        {σ with reg := Function.update σ.reg r ((s.stk k).head?.getD Glyph.eos)},
        toStk code ⟨Function.update s.reg r ((s.stk k).head?.getD Glyph.eos), s.stk⟩ L0 L1 rs⟩ 1 := by
  have hk' : code[((labOf code pc hpc : Λ code) : ℕ)]? = some (Instr.peek k r) := hk
  refine eit_one ?_
  rw [step_peek code (labOf code pc hpc) k r hk' σ (toStk code s L0 L1 rs)]
  rw [show ((labOf code pc hpc : Λ code) : ℕ) + 1 = pc + 1 from rfl, lab_mk code hpc1, toStk_reg]
  try rfl

def eit_push (code : List Instr) (pc : ℕ) (hpc : pc ≤ code.length) (hpc1 : pc + 1 ≤ code.length)
    (k : Stk) (r : Reg) (hk : code[pc]? = some (Instr.push k r))
    (σ : MS code) (s : State) (L0 : List InSym) (L1 : List Bool) (rs : List (Λ code))
    (hr : σ.reg r = s.reg r) :
    EIT code ⟨some (labOf code pc hpc), σ, toStk code s L0 L1 rs⟩
      ⟨some (labOf code (pc + 1) hpc1), σ,
        toStk code ⟨s.reg, Function.update s.stk k (s.reg r :: s.stk k)⟩ L0 L1 rs⟩ 1 := by
  have hk' : code[((labOf code pc hpc : Λ code) : ℕ)]? = some (Instr.push k r) := hk
  refine eit_one ?_
  rw [step_push code (labOf code pc hpc) k r hk' σ (toStk code s L0 L1 rs)]
  rw [show ((labOf code pc hpc : Λ code) : ℕ) + 1 = pc + 1 from rfl, lab_mk code hpc1, hr,
    toStk_update_inl]
  try rfl

def eit_set (code : List Instr) (pc : ℕ) (hpc : pc ≤ code.length) (hpc1 : pc + 1 ≤ code.length)
    (r : Reg) (g : Glyph) (hk : code[pc]? = some (Instr.set r g))
    (σ : MS code) (s : State) (L0 : List InSym) (L1 : List Bool) (rs : List (Λ code)) :
    EIT code ⟨some (labOf code pc hpc), σ, toStk code s L0 L1 rs⟩
      ⟨some (labOf code (pc + 1) hpc1),
        {σ with reg := Function.update σ.reg r g},
        toStk code ⟨Function.update s.reg r g, s.stk⟩ L0 L1 rs⟩ 1 := by
  have hk' : code[((labOf code pc hpc : Λ code) : ℕ)]? = some (Instr.set r g) := hk
  refine eit_one ?_
  rw [step_set code (labOf code pc hpc) r g hk' σ (toStk code s L0 L1 rs)]
  rw [show ((labOf code pc hpc : Λ code) : ℕ) + 1 = pc + 1 from rfl, lab_mk code hpc1, toStk_reg]
  try rfl

def eit_mov (code : List Instr) (pc : ℕ) (hpc : pc ≤ code.length) (hpc1 : pc + 1 ≤ code.length)
    (d t : Reg) (hk : code[pc]? = some (Instr.mov d t))
    (σ : MS code) (s : State) (L0 : List InSym) (L1 : List Bool) (rs : List (Λ code))
    (hrt : σ.reg t = s.reg t) :
    EIT code ⟨some (labOf code pc hpc), σ, toStk code s L0 L1 rs⟩
      ⟨some (labOf code (pc + 1) hpc1),
        {σ with reg := Function.update σ.reg d (s.reg t)},
        toStk code ⟨Function.update s.reg d (s.reg t), s.stk⟩ L0 L1 rs⟩ 1 := by
  have hk' : code[((labOf code pc hpc : Λ code) : ℕ)]? = some (Instr.mov d t) := hk
  refine eit_one ?_
  rw [step_mov code (labOf code pc hpc) d t hk' σ (toStk code s L0 L1 rs)]
  rw [show ((labOf code pc hpc : Λ code) : ℕ) + 1 = pc + 1 from rfl, lab_mk code hpc1, hrt,
    toStk_reg]
  try rfl

def eit_test_true (code : List Instr) (pc : ℕ) (hpc : pc ≤ code.length) (hpc1 : pc + 1 ≤ code.length)
    (r : Reg) (g : Glyph) (l : ℕ) (hk : code[pc]? = some (Instr.test r g l))
    (σ : MS code) (s : State) (L0 : List InSym) (L1 : List Bool) (rs : List (Λ code))
    (hv : σ.reg r = g) :
    EIT code ⟨some (labOf code pc hpc), σ, toStk code s L0 L1 rs⟩
      ⟨some (labOf code (pc + 1) hpc1), σ, toStk code s L0 L1 rs⟩ 1 := by
  have hk' : code[((labOf code pc hpc : Λ code) : ℕ)]? = some (Instr.test r g l) := hk
  refine eit_one ?_
  rw [step_test_true code (labOf code pc hpc) r g l hk' σ (toStk code s L0 L1 rs) hv]
  rw [show ((labOf code pc hpc : Λ code) : ℕ) + 1 = pc + 1 from rfl, lab_mk code hpc1]

def eit_test_false (code : List Instr) (pc : ℕ) (hpc : pc ≤ code.length)
    (r : Reg) (g : Glyph) (l : ℕ) (hl : l ≤ code.length)
    (hk : code[pc]? = some (Instr.test r g l))
    (σ : MS code) (s : State) (L0 : List InSym) (L1 : List Bool) (rs : List (Λ code))
    (hv : σ.reg r ≠ g) :
    EIT code ⟨some (labOf code pc hpc), σ, toStk code s L0 L1 rs⟩
      ⟨some (labOf code l hl), σ, toStk code s L0 L1 rs⟩ 1 := by
  have hk' : code[((labOf code pc hpc : Λ code) : ℕ)]? = some (Instr.test r g l) := hk
  refine eit_one ?_
  rw [step_test_false code (labOf code pc hpc) r g l hk' σ (toStk code s L0 L1 rs) hv,
    lab_mk code hl]

def eit_jmp (code : List Instr) (pc : ℕ) (hpc : pc ≤ code.length)
    (l : ℕ) (hl : l ≤ code.length) (hk : code[pc]? = some (Instr.jmp l))
    (σ : MS code) (s : State) (L0 : List InSym) (L1 : List Bool) (rs : List (Λ code)) :
    EIT code ⟨some (labOf code pc hpc), σ, toStk code s L0 L1 rs⟩
      ⟨some (labOf code l hl), σ, toStk code s L0 L1 rs⟩ 1 := by
  have hk' : code[((labOf code pc hpc : Λ code) : ℕ)]? = some (Instr.jmp l) := hk
  refine eit_one ?_
  rw [step_jmp code (labOf code pc hpc) l hk' σ (toStk code s L0 L1 rs), lab_mk code hl]

def eit_call (code : List Instr) (pc : ℕ) (hpc : pc ≤ code.length)
    (hk : code[pc]? = some Instr.call)
    (σ : MS code) (s : State) (L0 : List InSym) (L1 : List Bool) (rs : List (Λ code)) :
    EIT code ⟨some (labOf code pc hpc), σ, toStk code s L0 L1 rs⟩
      ⟨some (labOf code 0 (Nat.zero_le _)), σ,
        toStk code s L0 L1 (lab code (pc + 1) :: rs)⟩ 1 := by
  have hk' : code[((labOf code pc hpc : Λ code) : ℕ)]? = some Instr.call := hk
  refine eit_one ?_
  rw [step_call code (labOf code pc hpc) hk' σ (toStk code s L0 L1 rs)]
  rw [show ((labOf code pc hpc : Λ code) : ℕ) + 1 = pc + 1 from rfl, lab_mk code (Nat.zero_le _),
    ← toStk_inr2]
  try rfl

def eit_ret (code : List Instr) (p : ℕ) (hp : p ≤ code.length) (l : Λ code)
    (hk : code[p]? = some Instr.ret)
    (σ : MS code) (s : State) (L0 : List InSym) (L1 : List Bool) (rs : List (Λ code)) :
    EIT code ⟨some (labOf code p hp), σ, toStk code s L0 L1 (l :: rs)⟩
      ⟨some l, {σ with ret := some l}, toStk code s L0 L1 rs⟩ 1 := by
  have hk' : code[((labOf code p hp : Λ code) : ℕ)]? = some Instr.ret := hk
  have hl : ((toStk code s L0 L1 (l :: rs)) (Sum.inr 2)).head? = some l := rfl
  refine eit_one ?_
  rw [step_ret_some code (labOf code p hp) l hk' σ (toStk code s L0 L1 (l :: rs)) hl,
    toStk_inr2 code s L0 L1 (l :: rs) rs]
  try rfl

end Work.Compiler
