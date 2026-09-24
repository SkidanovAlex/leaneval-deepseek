import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

namespace Commons.Analysis.Integral

open MeasureTheory

theorem inv_sqrt_sq_sum_integral_le :
    ∃ C : ℝ, 0 < C ∧ ∀ (c T : ℝ), 0 < c → 1 ≤ T →
      (∫ t in (-T)..T, 1 / Real.sqrt (c ^ 2 + t ^ 2)) ≤ C * Real.log (2 * T / c + 2) := by
  refine ⟨2 * Real.sqrt 2, by positivity, ?_⟩
  intro c T hc hT
  have hT0 : 0 < T := lt_of_lt_of_le one_pos hT
  set f : ℝ → ℝ := fun t => 1 / Real.sqrt (c ^ 2 + t ^ 2) with hf
  have hfpos : ∀ t : ℝ, 0 < Real.sqrt (c ^ 2 + t ^ 2) := by
    intro t
    apply Real.sqrt_pos.mpr
    have hc2 : 0 < c ^ 2 := by positivity
    nlinarith [sq_nonneg t]
  have hfcont : Continuous f := by
    rw [hf]
    exact continuous_const.div (Real.continuous_sqrt.comp (by continuity))
      (fun t => ne_of_gt (hfpos t))
  have heven : ∀ t : ℝ, f (-t) = f t := by
    intro t
    rw [hf]
    simp only
    rw [neg_sq]
  have hleft : (∫ t in (-T)..(0:ℝ), f t) = ∫ t in (0:ℝ)..T, f t := by
    have h1 : (∫ t in (-T)..(0:ℝ), f t) = ∫ t in (-T)..(0:ℝ), f (-t) := by
      apply intervalIntegral.integral_congr
      intro t _
      exact (heven t).symm
    rw [h1, intervalIntegral.integral_comp_neg]
    simp
  have hsymm : (∫ t in (-T)..T, f t) = 2 * ∫ t in (0:ℝ)..T, f t := by
    have hadd := intervalIntegral.integral_add_adjacent_intervals
      (hfcont.intervalIntegrable (μ := volume) (-T) 0)
      (hfcont.intervalIntegrable (μ := volume) (0:ℝ) T)
    rw [← hadd, hleft]
    ring
  have hle : ∀ x ∈ Set.Icc (0:ℝ) T, f x ≤ Real.sqrt 2 / (c + x) := by
    intro x hx
    have hcx : 0 < c + x := by linarith [hx.1, hc]
    have hsq : (c + x) ^ 2 ≤ 2 * (c ^ 2 + x ^ 2) := by nlinarith [sq_nonneg (c - x)]
    have hstep : c + x ≤ Real.sqrt 2 * Real.sqrt (c ^ 2 + x ^ 2) := by
      have h4 : Real.sqrt ((c + x) ^ 2) ≤ Real.sqrt (2 * (c ^ 2 + x ^ 2)) :=
        Real.sqrt_le_sqrt hsq
      rwa [Real.sqrt_sq (le_of_lt hcx),
        Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 2) (c ^ 2 + x ^ 2)] at h4
    rw [hf]
    simp only
    rw [div_le_div_iff₀ (hfpos x) hcx]
    simpa using hstep
  have hgcont : ContinuousOn (fun x : ℝ => Real.sqrt 2 / (c + x)) (Set.uIcc (0:ℝ) T) := by
    apply ContinuousOn.div continuousOn_const (continuousOn_const.add continuousOn_id)
    intro x hx
    have hx0 : 0 ≤ x := by
      have : x ∈ Set.Icc (0:ℝ) T := by rwa [Set.uIcc_of_le (le_of_lt hT0)] at hx
      exact this.1
    simpa only [Pi.add_apply, id_eq] using (ne_of_gt (by linarith [hc, hx0] : (0:ℝ) < c + x))
  have hgint : IntervalIntegrable (fun x : ℝ => Real.sqrt 2 / (c + x)) volume (0:ℝ) T :=
    hgcont.intervalIntegrable
  have hgval : (∫ x in (0:ℝ)..T, Real.sqrt 2 / (c + x))
      = Real.sqrt 2 * Real.log ((c + T) / c) := by
    have h1 : (∫ x in (0:ℝ)..T, Real.sqrt 2 / (c + x))
        = Real.sqrt 2 * ∫ x in (0:ℝ)..T, (c + x)⁻¹ := by
      rw [← intervalIntegral.integral_const_mul (Real.sqrt 2) (fun x : ℝ => (c + x)⁻¹)]
      apply intervalIntegral.integral_congr
      intro x _
      simp only [div_eq_mul_inv]
    rw [h1]
    have h2 : (∫ x in (0:ℝ)..T, (c + x)⁻¹) = ∫ u in c + 0..c + T, u⁻¹ :=
      intervalIntegral.integral_comp_add_left (fun u : ℝ => u⁻¹) c
    rw [h2, integral_inv_of_pos (by linarith : (0:ℝ) < c + 0) (by linarith : (0:ℝ) < c + T)]
    simp
  have hmono : (∫ t in (0:ℝ)..T, f t) ≤ ∫ x in (0:ℝ)..T, Real.sqrt 2 / (c + x) :=
    intervalIntegral.integral_mono_on (le_of_lt hT0)
      (hfcont.intervalIntegrable (μ := volume) (0:ℝ) T) hgint hle
  have hlog : Real.log ((c + T) / c) ≤ Real.log (2 * T / c + 2) := by
    apply Real.log_le_log
    · exact div_pos (by linarith) hc
    · rw [div_le_iff₀ hc]
      have hcm : (2 * T / c + 2) * c = 2 * T + 2 * c := by
        rw [add_mul, div_mul_cancel₀ _ (ne_of_gt hc)]
      rw [hcm]
      linarith
  calc (∫ t in (-T)..T, f t) = 2 * ∫ t in (0:ℝ)..T, f t := hsymm
    _ ≤ 2 * ∫ x in (0:ℝ)..T, Real.sqrt 2 / (c + x) := by linarith [hmono]
    _ = 2 * Real.sqrt 2 * Real.log ((c + T) / c) := by rw [hgval]; ring
    _ ≤ 2 * Real.sqrt 2 * Real.log (2 * T / c + 2) := by
        apply mul_le_mul_of_nonneg_left hlog
        positivity

end Commons.Analysis.Integral