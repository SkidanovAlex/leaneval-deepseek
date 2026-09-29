import Mathlib
import Submission.Work.Holonomy3.defs

/-!
# `PullbackMero` is invariant under scaling the power series by `q⁻¹`

If the germ `z ↦ Σₙ aₙ φ(z)ⁿ` is meromorphic on the unit disc with denominator `P` (`P(0) ≠ 0`)
and holomorphic numerator `N`, then so is the germ of the scalar multiple `q⁻¹ • f`, with the same
denominator `P` and numerator `q⁻¹ • N`.
-/

namespace Work.Holonomy3

theorem scale_pullbackMero (q : ℕ) (hq : 0 < q) (f : PowerSeries ℚ) (φ : ℂ → ℂ) (h : Submission.CDTPlan.PullbackMero f φ) : Submission.CDTPlan.PullbackMero ((q : ℚ)⁻¹ • f) φ := by
  obtain ⟨P, N, hP, hN, hsum⟩ := h
  refine ⟨P, fun z => (((q : ℚ)⁻¹ : ℚ) : ℂ) * N z, hP, hN.const_mul _, ?_⟩
  filter_upwards [hsum] with z hz
  have h2 : HasSum (fun n => ((((q : ℚ)⁻¹ : ℚ) : ℂ)) *
      (((PowerSeries.coeff n f : ℚ) : ℂ) * φ z ^ n))
      ((((q : ℚ)⁻¹ : ℚ) : ℂ) * (N z / P.eval z)) := hz.mul_left _
  have hfun : (fun n => ((PowerSeries.coeff n ((q : ℚ)⁻¹ • f) : ℚ) : ℂ) * φ z ^ n)
      = (fun n => ((((q : ℚ)⁻¹ : ℚ) : ℂ)) *
          (((PowerSeries.coeff n f : ℚ) : ℂ) * φ z ^ n)) := by
    funext n
    rw [PowerSeries.coeff_smul, smul_eq_mul]
    push_cast
    ring
  rw [hfun]
  have hdiv : (((q : ℚ)⁻¹ : ℚ) : ℂ) * N z / P.eval z
      = (((q : ℚ)⁻¹ : ℚ) : ℂ) * (N z / P.eval z) := by ring
  rw [hdiv]
  exact h2

end Work.Holonomy3
