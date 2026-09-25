import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Submission.Commons.Analysis.Integral.exp_neg_mul_rpow_integrableOn_Ioi

open MeasureTheory Set Filter

noncomputable section

namespace Commons.Analysis.Real

/-! Integrability of `(log t) ^ 10 / (t * sqrt t)` on `(a, ∞)` for `a ≥ 2`.

We substitute `y = log t`: on the tail the integrand equals
`t⁻¹ · g (log t)` with `g y = y ^ 10 · exp (-(1 / 2) * y)`, which is
integrable (Γ-type exponential decay), and `integrableOn_comp_log_Ioi`
transfers integrability back. -/

private lemma exp_half_log_eq_sqrt {t : ℝ} (ht : 0 < t) :
    Real.exp ((1 / 2 : ℝ) * Real.log t) = Real.sqrt t := by
  rw [Real.sqrt_eq_rpow]
  rw [Real.rpow_def_of_pos ht]
  congr 1
  ring

private lemma inv_sqrt_eq_exp_half {t : ℝ} (ht : 0 < t) :
    (Real.sqrt t)⁻¹ = Real.exp (-(1 / 2 : ℝ) * Real.log t) := by
  have hmul : Real.sqrt t * Real.exp (-(1 / 2 : ℝ) * Real.log t) = 1 := by
    rw [← exp_half_log_eq_sqrt ht]
    rw [← Real.exp_add]
    have h : (1 / 2 : ℝ) * Real.log t + (-(1 / 2 : ℝ) * Real.log t) = 0 := by ring
    rw [h, Real.exp_zero]
  exact inv_eq_of_mul_eq_one_right hmul

private lemma log10_div_sqrt_pointwise (t : ℝ) (ht : 0 < t) :
    (Real.log t) ^ 10 / (t * Real.sqrt t)
      = t⁻¹ * ((Real.log t) ^ 10 * Real.exp (-(1 / 2 : ℝ) * Real.log t)) := by
  calc
    (Real.log t) ^ 10 / (t * Real.sqrt t)
        = (Real.log t) ^ 10 * (t * Real.sqrt t)⁻¹ := by rw [div_eq_mul_inv]
    _ = (Real.log t) ^ 10 * (t⁻¹ * (Real.sqrt t)⁻¹) := by rw [mul_inv]
    _ = (Real.log t) ^ 10 * (t⁻¹ * Real.exp (-(1 / 2 : ℝ) * Real.log t)) := by
        rw [inv_sqrt_eq_exp_half ht]
    _ = t⁻¹ * ((Real.log t) ^ 10 * Real.exp (-(1 / 2 : ℝ) * Real.log t)) := by ring

/-- `y ↦ y ^ 10 * exp (-(1 / 2) * y)` is integrable on `(0, ∞)`
(`Γ`-type exponential decay). -/
private lemma integrableOn_gamma_log10 :
    IntegrableOn (fun y : ℝ => y ^ 10 * Real.exp (-((1 / 2 : ℝ) * y))) (Ioi (0 : ℝ)) := by
  have hA := Commons.Analysis.Integral.exp_neg_mul_rpow_integrableOn_Ioi (c := (1 / 2 : ℝ))
    (σ := (11 : ℝ)) (by norm_num : 0 < (1 / 2 : ℝ)) (by norm_num : 0 < (11 : ℝ))
  have hA1 : IntegrableOn (fun r : ℝ => Real.exp (-((1 / 2 : ℝ) * r)) * r ^ 10) (Ioi (0 : ℝ)) := by
    refine hA.congr_fun ?_ measurableSet_Ioi
    intro r _
    norm_num
  simpa [mul_comm, mul_left_comm, mul_assoc] using hA1

/-- Same integrability on `(c, ∞)` for any `0 < c`. -/
private lemma integrableOn_g {c : ℝ} (hc : 0 < c) :
    IntegrableOn (fun y : ℝ => y ^ 10 * Real.exp (-((1 / 2 : ℝ) * y))) (Ioi c) := by
  exact integrableOn_gamma_log10.mono_set (Set.Ioi_subset_Ioi (le_of_lt hc))

/-- `(log t) ^ 10 / (t * sqrt t)` is integrable on `(a, ∞)` for `a ≥ 2`. -/
theorem integrableOn_log10_div_sqrt {a : ℝ} (ha : 2 ≤ a) :
    MeasureTheory.IntegrableOn (fun t : ℝ => (Real.log t) ^ 10 / (t * Real.sqrt t))
      (Set.Ioi a) MeasureTheory.volume := by
  have ha_pos : 0 < a := lt_of_lt_of_le (by norm_num) ha
  have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num : (1 : ℝ) < 2)
  have hlog_a_pos : 0 < Real.log a :=
    lt_of_lt_of_le hlog2pos (Real.log_le_log (by norm_num : (0 : ℝ) < 2) ha)
  let g : ℝ → ℝ := fun y => y ^ 10 * Real.exp (-((1 / 2 : ℝ) * y))
  have hg : IntegrableOn g (Ioi (Real.log a)) := by
    simpa [g] using integrableOn_g hlog_a_pos
  have hsub : IntegrableOn (fun t : ℝ => t⁻¹ • g (Real.log t)) (Ioi a) :=
    (MeasureTheory.integrableOn_comp_log_Ioi (g := g) ha_pos).mpr hg
  refine hsub.congr_fun ?_ measurableSet_Ioi
  intro t ht
  have ht0 : 0 < t := lt_trans ha_pos ht
  dsimp only
  rw [smul_eq_mul]
  rw [log10_div_sqrt_pointwise t ht0]
  simp [g]

end Commons.Analysis.Real
