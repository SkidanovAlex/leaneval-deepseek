import Mathlib
import Submission.Work.ZeroFreeTables.HB88TentDefs

namespace Work.ZeroFreeTables

theorem TentLaplace (X σ : ℝ) (hX : 0 < X) :
    (∫ t in (0:ℝ)..X, Real.exp (σ * t) * Work.ZeroFreeTables.tent X t)
      = Work.ZeroFreeTables.tentFm σ X := by
  have hX0 : 0 ≤ X := le_of_lt hX
  -- On `[0,X]` the tent equals `X - t`.
  have hcongr : (∫ t in (0:ℝ)..X, Real.exp (σ * t) * tent X t)
      = ∫ t in (0:ℝ)..X, Real.exp (σ * t) * (X - t) := by
    apply intervalIntegral.integral_congr
    intro t ht
    rw [Set.uIcc_of_le hX0] at ht
    have hle : 0 ≤ X - t := by linarith [ht.2]
    simp only [tent]
    rw [max_eq_left hle]
  rw [hcongr]
  rcases eq_or_ne σ 0 with hσ | hσ
  · -- `σ = 0`: elementary integral.
    subst hσ
    have h1 : (∫ t in (0:ℝ)..X, Real.exp (0 * t) * (X - t))
        = ∫ t in (0:ℝ)..X, (X - t) := by
      apply intervalIntegral.integral_congr
      intro t ht
      simp
    rw [h1]
    have hsub : (∫ t in (0:ℝ)..X, (X - t))
        = (∫ t in (0:ℝ)..X, (fun _ : ℝ => X) t) - ∫ t in (0:ℝ)..X, t :=
      intervalIntegral.integral_sub (continuous_const.intervalIntegrable _ _)
        (continuous_id.intervalIntegrable _ _)
    rw [hsub, intervalIntegral.integral_const, integral_id]
    simp [tentFm]
    ring
  · -- `σ ≠ 0`: primitive `s ↦ e^{σ s} ((X - s)/σ + 1/σ²)`.
    have hderiv : ∀ t ∈ Set.uIcc (0:ℝ) X,
        HasDerivAt (fun s : ℝ => Real.exp (σ * s) * ((X - s) / σ + 1 / σ ^ 2))
          (Real.exp (σ * t) * (X - t)) t := by
      intro t _
      have hlin : HasDerivAt (fun s : ℝ => σ * s) σ t :=
        ((hasDerivAt_id t).const_mul σ).congr_deriv (mul_one σ)
      have hexp : HasDerivAt (fun s : ℝ => Real.exp (σ * s)) (Real.exp (σ * t) * σ) t :=
        (Real.hasDerivAt_exp (σ * t)).comp t hlin
      have h1 : HasDerivAt (fun s : ℝ => X - s) (-1) t :=
        ((hasDerivAt_const t X).sub (hasDerivAt_id t)).congr_deriv (by ring)
      have h2 : HasDerivAt (fun s : ℝ => (X - s) / σ) ((-1) / σ) t := h1.div_const σ
      have h3 : HasDerivAt (fun s : ℝ => (X - s) / σ + 1 / σ ^ 2) ((-1) / σ) t :=
        h2.add_const (1 / σ ^ 2)
      have hmain := hexp.mul h3
      refine hmain.congr_deriv ?_
      field_simp
      ring
    have hInt : IntervalIntegrable (fun t : ℝ => Real.exp (σ * t) * (X - t))
        MeasureTheory.volume (0:ℝ) X :=
      (by fun_prop : Continuous (fun t : ℝ => Real.exp (σ * t) * (X - t))).intervalIntegrable _ _
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hInt]
    rw [tentFm, if_neg hσ]
    simp only [mul_zero, Real.exp_zero, sub_self, zero_div, zero_add, sub_zero, one_mul]
    field_simp
    ring

end Work.ZeroFreeTables
