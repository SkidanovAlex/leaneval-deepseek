import Mathlib

/-!
# Shared definitions for the strip section (`strip_section_strict`)

The complexified almost Mathieu section equation
`u x = z - 2λ cos(2π(x-α)) - 1/u (x-α)`
is solved by a fixed-point iteration in the strip `{|Im x| < σ}`.  This file fixes the
vocabulary used by `strip_section_strict` and by the lemmas proved for it.
-/

noncomputable section

namespace Work.TMComp.MAnalytic

/-- The inhomogeneity `x ↦ z - 2λ cos(2π(x-α))` of the section equation. -/
def stripA (α lam : ℝ) (z : ℂ) : ℂ → ℂ :=
  fun x => z - 2 * lam * Complex.cos (2 * Real.pi * (x - α))

/-- One step of the fixed point iteration: `f ↦ (x ↦ A x - 1/f (x-α))`. -/
def stripStep (A : ℂ → ℂ) (α : ℝ) : (ℂ → ℂ) → (ℂ → ℂ) :=
  fun f x => A x - (f (x - α))⁻¹

/-- The `n`-th iterate of `stripStep A α` applied to `A`. -/
def stripIter (A : ℂ → ℂ) (α : ℝ) (n : ℕ) : ℂ → ℂ :=
  (stripStep A α)^[n] A

/-- The horizontal strip `{|Im x| < σ}`. -/
def stripDom (σ : ℝ) : Set ℂ :=
  {x : ℂ | |x.im| < σ}

@[simp] theorem stripIter_zero (A : ℂ → ℂ) (α : ℝ) : stripIter A α 0 = A := rfl

theorem stripIter_succ (A : ℂ → ℂ) (α : ℝ) (n : ℕ) :
    stripIter A α (n + 1) = stripStep A α (stripIter A α n) :=
  Function.iterate_succ_apply' _ _ _

@[simp] theorem stripStep_apply (A : ℂ → ℂ) (α : ℝ) (f : ℂ → ℂ) (x : ℂ) :
    stripStep A α f x = A x - (f (x - α))⁻¹ := rfl

end Work.TMComp.MAnalytic
