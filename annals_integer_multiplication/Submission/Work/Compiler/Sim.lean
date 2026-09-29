import Mathlib
import Submission.Work.Compiler.Defs
import Submission.Work.Compiler.Steps
import Submission.Work.Compiler.CodeAt

/-!
# Simulation: the compiled machine soundly executes StackLang

The main theorem `simulate` is proved by induction on the derivation `Eval main c s s' n`: the
compiled block of `c` sits at position `pc` (`CodeAt`), and the machine, started at the label of
position `pc` with the language stacks equal to those of `s` and the return stack equal to `rs`,
reaches the label of position `pc + clen c` with the language stacks of `s'` and the same return
stack, in at most `10 * n` steps.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Work.Compiler

open HvdH Turing StateTransition

/-- Machine reachability in at most `m` steps (a `Type`, to be composed with `EIT.trans`). -/
abbrev EIT (code : List Instr) (a b : Cfg code) (m : ℕ) : Type :=
  EvalsToInTime (TM2.step (mach code)) a (some b) m

/-- A single machine step. -/
def eit_one {code : List Instr} {a b : Cfg code} (h : TM2.step (mach code) a = some b) :
    EIT code a b 1 :=
  ⟨⟨1, by rw [Function.iterate_one]; exact h⟩, le_refl 1⟩

/-- Weaken the bound. -/
def eit_mono {code : List Instr} {a b : Cfg code} {m m' : ℕ} (h : EIT code a b m)
    (hmm : m ≤ m') : EIT code a b m' :=
  EvalsToInTime.mono' h hmm

/-- Concatenate two runs. -/
def eit_trans {code : List Instr} {a b d : Cfg code} {m₁ m₂ : ℕ} (h₁ : EIT code a b m₁)
    (h₂ : EIT code b d m₂) : EIT code a d (m₂ + m₁) :=
  EvalsToInTime.trans (TM2.step (mach code)) m₁ m₂ a b (some d) h₁ h₂

/-- The label of position `l`, when `l` is known to be in range. -/
def labOf (code : List Instr) (l : ℕ) (h : l ≤ code.length) : Λ code := ⟨l, by omega⟩

theorem lab_mk (code : List Instr) {l : ℕ} (h : l ≤ code.length) :
    lab code l = labOf code l h := Fin.ext (Nat.min_eq_left (by omega))

theorem labOf_congr (code : List Instr) {l₁ l₂ : ℕ} (h₁ : l₁ ≤ code.length)
    (h₂ : l₂ ≤ code.length) (h : l₁ = l₂) : labOf code l₁ h₁ = labOf code l₂ h₂ := by
  subst h; rfl

/-! ## Stack-vector manipulations -/

theorem toStk_update_inl (code : List Instr) (s : State) (k : Stk) (v : List Glyph)
    (L0 : List InSym) (L1 : List Bool) (rs : List (Λ code)) :
    toStk code ⟨s.reg, Function.update s.stk k v⟩ L0 L1 rs
      = Function.update (toStk code s L0 L1 rs) (Sum.inl k) v := by
  funext j
  cases j with
  | inl j =>
      by_cases h : j = k
      · subst h; simp only [toStk, Function.update_self]
      · simp [toStk, Function.update, h]
  | inr j => fin_cases j <;> simp [toStk, Function.update]

theorem toStk_inr2 (code : List Instr) (s : State) (L0 : List InSym) (L1 : List Bool)
    (rs v : List (Λ code)) :
    toStk code s L0 L1 v = Function.update (toStk code s L0 L1 rs) (Sum.inr 2) v := by
  funext j
  cases j with
  | inl k => simp [toStk, Function.update]
  | inr j => fin_cases j <;> simp [toStk, Function.update]

/-! ## Bounds on positions -/

/-- `CodeAt` puts `pc + clen c` inside `code`. -/
theorem codeAt_le (code : List Instr) : ∀ (c : Cmd) (pc : ℕ),
    CodeAt code pc c → pc + clen c ≤ code.length
  | .skip, pc, h => by
      simp only [CodeAt, clen] at h ⊢
      exact Nat.succ_le_of_lt (List.getElem?_eq_some_iff.mp h).choose
  | .pop k r, pc, h => by
      simp only [CodeAt, clen] at h ⊢
      exact Nat.succ_le_of_lt (List.getElem?_eq_some_iff.mp h).choose
  | .peek k r, pc, h => by
      simp only [CodeAt, clen] at h ⊢
      exact Nat.succ_le_of_lt (List.getElem?_eq_some_iff.mp h).choose
  | .push k r, pc, h => by
      simp only [CodeAt, clen] at h ⊢
      exact Nat.succ_le_of_lt (List.getElem?_eq_some_iff.mp h).choose
  | .set r c, pc, h => by
      simp only [CodeAt, clen] at h ⊢
      exact Nat.succ_le_of_lt (List.getElem?_eq_some_iff.mp h).choose
  | .mov d t, pc, h => by
      simp only [CodeAt, clen] at h ⊢
      exact Nat.succ_le_of_lt (List.getElem?_eq_some_iff.mp h).choose
  | .seq a b, pc, h => by
      simp only [CodeAt] at h
      obtain ⟨h1, h2⟩ := h
      have i1 := codeAt_le code a pc h1
      have i2 := codeAt_le code b (pc + clen a) h2
      simp only [clen]
      omega
  | .ite r g p q, pc, h => by
      simp only [CodeAt] at h
      obtain ⟨-, -, -, hq⟩ := h
      have iq := codeAt_le code q (pc + clen p + 2) hq
      simp only [clen]
      omega
  | .loop r g b, pc, h => by
      simp only [CodeAt] at h
      obtain ⟨-, -, hj⟩ := h
      have hj' : pc + clen b + 1 < code.length := (List.getElem?_eq_some_iff.mp hj).choose
      simp only [clen]
      omega
  | .self, pc, h => by
      simp only [CodeAt, clen] at h ⊢
      exact Nat.succ_le_of_lt (List.getElem?_eq_some_iff.mp h).choose

/-- `pc` itself is in range. -/
theorem codeAt_le_start {code : List Instr} {pc : ℕ} {c : Cmd} (hc : CodeAt code pc c) :
    pc ≤ code.length :=
  le_trans (Nat.le_add_right pc (clen c)) (codeAt_le code c pc hc)

end Work.Compiler
