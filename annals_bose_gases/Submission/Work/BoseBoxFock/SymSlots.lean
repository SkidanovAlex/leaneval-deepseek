import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Normed.Lp.lpSpace
import Submission.Work.BoseBoxFock.SymScalar
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.SymSlots` — the `symR` slots in block form

`symR r = Σ_{i<25} r^{p_i+q_i} • KvecF i`.  After unfolding `KvecF` the slots are the
words `Bkin`, `Bgap`, `BNH`, the five scalar slots `3–7`, `BW`, `Bbog1/2`, the eight
`χ̂`/`χ̂²`-linear slots `Bc8 … Ba9'` and the two cubic slots `BQ3a/b`.  This file
rewrites each of those words into the monomial *blocks* of `SymBlocks.lean` with a
`k`-independent scalar coefficient, which is the form the assembly of `symDiscrep`
consumes.
-/

noncomputable section

open scoped BigOperators

namespace Work.BoseBoxFock

open Work.BoseB4

set_option autoImplicit false
set_option linter.unusedVariables false

variable {m : ℕ} [NeZero m]

/-- Slot 12 (`Bc8`). -/
theorem Bc8_blocks {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
    (f : Mode → Fin m → ℝ) (E : Work.BoseB7.Q3Env Mode) :
    Bc8 f E = (((i3F E * E.W1 0 : ℝ)) : ℂ) • BχC f E := by
  rw [Bc8, BchiC_const, ← BχC]

/-- Slot 13 (`−Bc8'`). -/
theorem Bc8'_blocks {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
    (f : Mode → Fin m → ℝ) (E : Work.BoseB7.Q3Env Mode) :
    Bc8' f E
      = (((2 * (i3F E * E.W1 0) + E.mu * E.W1 0 : ℝ)) : ℂ) • BχC f E := by
  rw [Bc8', BchiC_const, ← BχC]

/-- Slot 14 (`Ba8`). -/
theorem Ba8_blocks {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
    (f : Mode → Fin m → ℝ) (E : Work.BoseB7.Q3Env Mode) :
    Ba8 f E = (((i3F E * E.W1 0 : ℝ)) : ℂ) • BχA f E := by
  rw [Ba8, BchiA_const, ← BχA]

/-- Slot 15 (`−Ba8'`). -/
theorem Ba8'_blocks {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
    (f : Mode → Fin m → ℝ) (E : Work.BoseB7.Q3Env Mode) :
    Ba8' f E
      = (((2 * (i3F E * E.W1 0) + E.mu * E.W1 0 : ℝ)) : ℂ) • BχA f E := by
  rw [Ba8', BchiA_const, ← BχA]

/-- Slot 16 (`Bc9`). -/
theorem Bc9_blocks {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
    (g : Mode → Fin m → ℝ) (E : Work.BoseB7.Q3Env Mode) :
    Bc9 g E = (((i3F E * E.W1omega0 : ℝ)) : ℂ) • BchiSqC g E := by
  rw [Bc9, BchiC_const, ← BchiSqC]

/-- Slot 17 (`−Bc9'`). -/
theorem Bc9'_blocks {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
    (g : Mode → Fin m → ℝ) (E : Work.BoseB7.Q3Env Mode) :
    Bc9' g E
      = (((2 * (i3F E * E.W1omega0) + 0 : ℝ)) : ℂ) • BchiSqC g E := by
  rw [Bc9', BchiC_const, ← BchiSqC]

/-- Slot 18 (`Ba9`). -/
theorem Ba9_blocks {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
    (g : Mode → Fin m → ℝ) (E : Work.BoseB7.Q3Env Mode) :
    Ba9 g E = (((i3F E * E.W1omega0 : ℝ)) : ℂ) • BchiSqA g E := by
  rw [Ba9, BchiA_const, ← BchiSqA]

/-- Slot 19 (`−Ba9'`). -/
theorem Ba9'_blocks {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
    (g : Mode → Fin m → ℝ) (E : Work.BoseB7.Q3Env Mode) :
    Ba9' g E
      = (((2 * (i3F E * E.W1omega0) + 0 : ℝ)) : ℂ) • BchiSqA g E := by
  rw [Ba9', BchiA_const, ← BchiSqA]

/-- Slot 23 (`BQ3a` with γ = ℓ⁻³ f_L Ŵ₁). -/
theorem BQ3a_blocks {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
    (f g : Mode → Fin m → ℝ) (PHs : Finset Mode) (E : Work.BoseB7.Q3Env Mode) :
    BQ3a (Work.BoseB7.excited Mode) PHs (fun s k => i3F E * (E.fL s * E.W1 k)) g f
      = ((i3F E : ℝ) : ℂ) • BQa f g PHs E := by
  rw [BQ3a_const, ← BQa]

/-- Slot 24 (`BQ3b` with γ = ℓ⁻³ f_L Ŵ₁). -/
theorem BQ3b_blocks {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
    (f g : Mode → Fin m → ℝ) (PHs : Finset Mode) (E : Work.BoseB7.Q3Env Mode) :
    BQ3b (Work.BoseB7.excited Mode) PHs (fun s k => i3F E * (E.fL s * E.W1 k)) g f
      = ((i3F E : ℝ) : ℂ) • BQb f g PHs E := by
  rw [BQ3b_const, ← BQb]

/-! ## Repointing the environment does not change the blocks -/

theorem Bkin_KzEnvAt {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
    (f : Mode → Fin m → ℝ) (E : Work.BoseB7.Q3Env Mode) (ρ : ℝ) :
    Bkin f (Work.BoseFixR.KzEnvAt E ρ) = Bkin f E := rfl

theorem BNW_KzEnvAt {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
    (f : Mode → Fin m → ℝ) (E : Work.BoseB7.Q3Env Mode) (ρ : ℝ) :
    BNW f (Work.BoseFixR.KzEnvAt E ρ) = BNW f E := rfl

theorem BNω_KzEnvAt {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
    (f : Mode → Fin m → ℝ) (E : Work.BoseB7.Q3Env Mode) (ρ : ℝ) :
    BNω f (Work.BoseFixR.KzEnvAt E ρ) = BNω f E := rfl

theorem BPa_KzEnvAt {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
    (f : Mode → Fin m → ℝ) (E : Work.BoseB7.Q3Env Mode) (ρ : ℝ) :
    BPa f (Work.BoseFixR.KzEnvAt E ρ) = BPa f E := rfl

theorem BPc_KzEnvAt {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
    (f : Mode → Fin m → ℝ) (E : Work.BoseB7.Q3Env Mode) (ρ : ℝ) :
    BPc f (Work.BoseFixR.KzEnvAt E ρ) = BPc f E := rfl

theorem BχC_KzEnvAt {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
    (f : Mode → Fin m → ℝ) (E : Work.BoseB7.Q3Env Mode) (ρ : ℝ) :
    BχC f (Work.BoseFixR.KzEnvAt E ρ) = BχC f E := rfl

theorem BχA_KzEnvAt {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
    (f : Mode → Fin m → ℝ) (E : Work.BoseB7.Q3Env Mode) (ρ : ℝ) :
    BχA f (Work.BoseFixR.KzEnvAt E ρ) = BχA f E := rfl

theorem BchiSqC_KzEnvAt {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
    (g : Mode → Fin m → ℝ) (E : Work.BoseB7.Q3Env Mode) (ρ : ℝ) :
    BchiSqC g (Work.BoseFixR.KzEnvAt E ρ) = BchiSqC g E := rfl

theorem BchiSqA_KzEnvAt {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
    (g : Mode → Fin m → ℝ) (E : Work.BoseB7.Q3Env Mode) (ρ : ℝ) :
    BchiSqA g (Work.BoseFixR.KzEnvAt E ρ) = BchiSqA g E := rfl

theorem BQa_KzEnvAt {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
    (f g : Mode → Fin m → ℝ) (PHs : Finset Mode) (E : Work.BoseB7.Q3Env Mode) (ρ : ℝ) :
    BQa f g PHs (Work.BoseFixR.KzEnvAt E ρ) = BQa f g PHs E := rfl

theorem BQb_KzEnvAt {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
    (f g : Mode → Fin m → ℝ) (PHs : Finset Mode) (E : Work.BoseB7.Q3Env Mode) (ρ : ℝ) :
    BQb f g PHs (Work.BoseFixR.KzEnvAt E ρ) = BQb f g PHs E := rfl

end Work.BoseBoxFock
