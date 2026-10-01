import Mathlib
import Submission.Work.ZeroFreeTables.testFn71_defs

namespace Work.ZeroFreeTables

/-- HB Lemma 7.1: the value of the closed form `tf71cf` at the point
`u/ζ` (`ζ = λ tan θ`), where the answer collapses (via `cos 2θ = 2cos²θ − 1`
and `sin²θ + cos²θ = 1`) to an elementary expression in `u`. -/
theorem tf71cf_eq_D (θ lam u : ℝ) (hθ0 : 0 < θ) (hθ1 : θ < Real.pi / 2) (hlam : 0 < lam) :
    Work.ZeroFreeTables.tf71cf θ lam (u / Work.ZeroFreeTables.tf71ζ θ lam)
      = (lam * (1 + Real.tan θ ^ 2) / (Real.sin θ * Real.cos θ)) *
        ((θ - u / 2 - Real.sin θ * Real.cos θ) * Real.cos u
          + Real.cos θ ^ 2 * (2 * θ - u) + (Real.cos θ ^ 2 + 1 / 2) * Real.sin u
          - 2 * Real.sin θ * Real.cos θ) := by
  rw [tf71cf, tf71ζ, tf71γ, tf71ζ]
  have htan : Real.tan θ ≠ 0 := ne_of_gt (tf71_tan_pos hθ0 hθ1)
  have hK : lam * Real.tan θ ≠ 0 := mul_ne_zero (ne_of_gt hlam) htan
  rw [mul_div_cancel₀ u hK, Real.tan_eq_sin_div_cos θ]
  simp only [Real.sin_sub, Real.sin_two_mul, Real.cos_two_mul]
  have hs : Real.sin θ ≠ 0 := tf71_sinθ_ne hθ0 hθ1
  have hc : Real.cos θ ≠ 0 :=
    ne_of_gt (Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hθ1⟩)
  have hs2 : Real.sin (2 * θ) ≠ 0 := tf71_sin2θ_ne hθ0 hθ1
  have hsc : Real.sin θ * Real.cos θ ≠ 0 := mul_ne_zero hs hc
  field_simp
  ring_nf
  linear_combination ((2 * θ - u) * Real.cos u) * Real.sin_sq_add_cos_sq θ

end Work.ZeroFreeTables
