/-
# The aggregate depends on the phases only through their fractional parts

`cubeCorr`/`aggr` (in `blindConvertK_front`) use the phases `β u v` only through the factor
`e(2πi·(β u v)·x)` with `x ∈ ℤ`.  Since `e(2πi·n·x) = 1` for `n ∈ ℤ`, replacing `β` by its
fractional part leaves the aggregate *exactly* unchanged.  This is what lets the assembly of
`blindConvertK` assume `0 ≤ β < 1` (see `NOTES_blindConvertK_SESSION.md` §7).
-/

import Mathlib
import Submission.Work.Peluse.Ulower.StepLe.blindConvertK_front

set_option autoImplicit false
open scoped BigOperators

namespace Work.Peluse.Ulower.StepLe

noncomputable section

/-- The exponential of an integer multiple of `2πi x` is one. -/
lemma exp_int_mul_eq_one (n x : ℤ) :
    Complex.exp (2 * Real.pi * Complex.I * (n : ℂ) * (x : ℂ)) = 1 := by
  have h1 : 2 * Real.pi * Complex.I * (n : ℂ) * (x : ℂ)
      = ((n * x : ℤ) : ℂ) * (2 * Real.pi * Complex.I) := by
    push_cast; ring
  rw [h1, Complex.exp_int_mul, Complex.exp_two_pi_mul_I]
  simp

/-- The summands of the aggregate are unchanged when the phase is replaced by its fractional part. -/
lemma cubeCorr_frac {σ B : ℕ} (F : ℤ → ℂ)
    (β : (Fin σ → ℤ) → (Fin σ → ℤ) → ℝ) (u v : Fin σ → ℤ) :
    cubeCorr σ B F (fun u v => β u v - (⌊β u v⌋ : ℝ)) u v = cubeCorr σ B F β u v := by
  have hphase : ∀ x : ℤ,
      Complex.exp (2 * Real.pi * Complex.I * ((β u v - (⌊β u v⌋ : ℝ) : ℝ) : ℂ) * (x : ℂ))
        = Complex.exp (2 * Real.pi * Complex.I * ((β u v : ℝ) : ℂ) * (x : ℂ)) := by
    intro x
    have hdec : 2 * Real.pi * Complex.I * ((β u v - (⌊β u v⌋ : ℝ) : ℝ) : ℂ) * (x : ℂ)
        = 2 * Real.pi * Complex.I * ((β u v : ℝ) : ℂ) * (x : ℂ)
          + 2 * Real.pi * Complex.I * (-(⌊β u v⌋ : ℂ)) * (x : ℂ) := by
      push_cast; ring
    rw [hdec, Complex.exp_add]
    have hzero : Complex.exp (2 * Real.pi * Complex.I * (-(⌊β u v⌋ : ℂ)) * (x : ℂ)) = 1 := by
      have := exp_int_mul_eq_one (-⌊β u v⌋) x
      simpa using this
    rw [hzero, mul_one]
  simp only [cubeCorr]
  simp only [hphase]

end

end Work.Peluse.Ulower.StepLe
