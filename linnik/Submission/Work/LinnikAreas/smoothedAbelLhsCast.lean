import Mathlib
import Submission.Work.LinnikAreas.RatioDefs

namespace Work.LinnikAreas

open Complex
open scoped BigOperators

/-- `Ssm` is defined in real form (`lamR χ n = (lam χ n).re`); for a character with real `λ`
(the hypothesis `hχre`) it coincides with the complex sum `Σ_n λ(n) n^{-β} (1 - n/x)`. -/
theorem smoothedAbelLhsCast {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχre : ∀ n : ℕ, (Work.LinnikAreas.lam χ n).im = 0) (β : ℝ) {x : ℕ} (hx : 1 ≤ x) :
    (Work.LinnikAreas.Ssm χ β (x:ℝ) : ℂ)
      = ∑ n ∈ Finset.Icc 1 x, Work.LinnikAreas.lam χ n *
          ((n:ℂ) ^ (-(β:ℂ)) * (1 - (n:ℂ) / (x:ℂ))) := by
  have _hx := hx
  rw [Ssm_apply, Nat.floor_natCast, Complex.ofReal_sum]
  apply Finset.sum_congr rfl
  intro n _
  -- `λ(n)` is the cast of its real part `lamR χ n`, by the realness hypothesis.
  have hlam : ((lamR χ n : ℝ) : ℂ) = lam χ n := by
    unfold lamR
    rw [Complex.ext_iff]
    refine ⟨by simp, ?_⟩
    simpa [lam] using (hχre n).symm
  -- Push the real-to-complex cast through the product and the `rpow`.
  rw [Complex.ofReal_mul, Complex.ofReal_mul, Complex.ofReal_sub, Complex.ofReal_one,
    Complex.ofReal_div, Complex.ofReal_natCast, Complex.ofReal_natCast]
  rw [hlam]
  rw [Complex.ofReal_cpow (Nat.cast_nonneg n)]
  push_cast
  ring

end Work.LinnikAreas
