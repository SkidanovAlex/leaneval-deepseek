/-
# Definitions for the `strip_decay_of_line_decay` engine

The target lemma `Work.CKFinal.strip_decay_of_line_decay` reduces a holomorphic function on `ℍ`
satisfying `(T-I)²f = 0` and a growth bound to an explicit exponential decay on the strip.  The
proof goes through the `q`-expansion of the two `1`-periodic functions

  `shiftB f τ = f (τ+1) - f τ`,   `shiftA f τ = f τ - τ (shiftB f τ)`.

This file collects the definitions shared by that proof and by the lemmas delegated for it.
-/
import Mathlib
import Submission.Work.Kernels.PhiAnnihilation
import Submission.Work.Kernels.ModerateGrowth

noncomputable section

open UpperHalfPlane

namespace Work.CKFinal

/-- The extension of a function on `ℍ` to all of `ℂ`, set to `0` below the real axis.  For a
`1`-periodic `g` this extension is again `1`-periodic, which is what makes the `q`-expansion of
`g` well behaved. -/
noncomputable def pext (g : ℍ → ℂ) : ℂ → ℂ :=
  fun z => if h : 0 < z.im then g ⟨z, h⟩ else 0

/-- The `q`-expansion of a `1`-periodic holomorphic function on `ℍ`:  a function of
`q = e^{2πiτ}` (with the singularity at `q = 0` filled in by the limiting value). -/
noncomputable def qExp (g : ℍ → ℂ) : ℂ → ℂ :=
  Function.Periodic.cuspFunction 1 (pext g)

/-- `shiftB f τ = f (τ + 1) - f τ`. -/
noncomputable def shiftB (f : ℍ → ℂ) : ℍ → ℂ := fun τ => f ((1 : ℝ) +ᵥ τ) - f τ

/-- `shiftA f τ = f τ - τ (f (τ + 1) - f τ)`. -/
noncomputable def shiftA (f : ℍ → ℂ) : ℍ → ℂ := fun τ => f τ - (τ : ℂ) * shiftB f τ

end Work.CKFinal
