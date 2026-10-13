import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# Analyticity of the integral `z ↦ ∫ s in z₀..z, h s`

If `h : ℝ → ℝ` is real analytic at `z₀`, then its primitive `z ↦ ∫ s in z₀..z, h s` is real
analytic at `z₀` as well.

The proof is the classical one: expand `h` around `z₀` in its Taylor power series
`h (z₀ + t) = ∑ cₙ tⁿ` and integrate term by term, which turns the primitive into the power
series `∑ c_{n-1} zⁿ / n`; the latter has positive radius of convergence because dividing the
`n`-th coefficient by `n` and shifting preserves the geometric decay of the coefficients.
-/

namespace Work.Coercivity

open MeasureTheory Set

/-- Comparison test used for the radius of convergence of the integrated series: if
`∑ ‖aₙ‖ (2r)ⁿ` converges then so does `∑ ‖a_{n-1}‖ rⁿ / n`. -/
theorem summable_coeff_div_shift {a : ℕ → ℝ} {r : NNReal}
    (ha : Summable fun n => ‖a n‖ * (2 * (r : ℝ)) ^ n) :
    Summable fun n => ‖a (n - 1) * (↑n : ℝ)⁻¹‖ * (r : ℝ) ^ n := by
  rw [← summable_nat_add_iff 1]
  refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_)
    (Summable.mul_left (2 * (r : ℝ)) ha)
  have hr' : (0 : ℝ) ≤ (r : ℝ) := r.coe_nonneg
  have h2 : (r : ℝ) ≤ 2 * (r : ℝ) := by linarith
  have hcoe : ‖a (n + 1 - 1) * (↑(n + 1) : ℝ)⁻¹‖ ≤ ‖a n‖ := by
    rw [Nat.add_sub_cancel, norm_mul]
    have hpos : (0 : ℝ) < (↑(n + 1) : ℝ) := by positivity
    rw [Real.norm_of_nonneg (inv_nonneg.mpr hpos.le)]
    nth_rewrite 2 [← mul_one ‖a n‖]
    gcongr
    exact inv_le_one_of_one_le₀ (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.succ_ne_zero n))
  calc ‖a (n + 1 - 1) * (↑(n + 1) : ℝ)⁻¹‖ * (r : ℝ) ^ (n + 1)
      ≤ ‖a n‖ * (r : ℝ) ^ (n + 1) := by gcongr
    _ = ‖a n‖ * ((r : ℝ) ^ n * (r : ℝ)) := by rw [pow_succ]
    _ ≤ ‖a n‖ * ((2 * (r : ℝ)) ^ n * (2 * (r : ℝ))) := by gcongr
    _ = (2 * (r : ℝ)) * (‖a n‖ * (2 * (r : ℝ)) ^ n) := by ring

/-- Term-by-term integration of a power series: the primitive of `h (z₀ + ·)` has power series
with coefficients `c_{n-1}/n`. -/
theorem hasSum_antideriv_ofScalars {h : ℝ → ℝ} {z₀ : ℝ} {c : ℕ → ℝ} {ρ : ENNReal}
    (hp : HasFPowerSeriesOnBall h (FormalMultilinearSeries.ofScalars ℝ c) z₀ ρ)
    {y : ℝ} (hy : ENNReal.ofReal ‖y‖ < ρ) :
    HasSum (fun n : ℕ => c (n - 1) * (↑n : ℝ)⁻¹ * y ^ n) (∫ s in z₀..(z₀ + y), h s) := by
  have hInt : (∫ s in z₀..(z₀ + y), h s) = ∫ t in 0..y, h (t + z₀) := by
    rw [intervalIntegral.integral_comp_add_right (a := 0) (b := y) h z₀]
    simp only [zero_add, add_comm z₀ y]
  rw [hInt]
  have hyρ : ((‖y‖₊ : NNReal) : ENNReal) < ρ := by
    rw [← ENNReal.ofReal_coe_nnreal (p := ‖y‖₊)]
    exact hy
  have hsumm : Summable (fun n => ‖c n‖ * (‖y‖ : ℝ) ^ n) := by
    have hrad : ((‖y‖₊ : NNReal) : ENNReal) <
        (FormalMultilinearSeries.ofScalars ℝ c).radius := lt_of_lt_of_le hyρ hp.r_le
    have h := (FormalMultilinearSeries.ofScalars ℝ c).summable_norm_mul_pow (r := ‖y‖₊) hrad
    simpa [FormalMultilinearSeries.ofScalars_norm] using h
  have htabs' : ∀ {t : ℝ}, t ∈ uIoc 0 y → |t| ≤ |y| := by
    intro t ht
    rcases mem_uIcc.mp (uIoc_subset_uIcc ht) with ⟨h0, h1⟩ | ⟨h1, h0⟩
    · rw [abs_of_nonneg h0, abs_of_nonneg (le_trans h0 h1)]; exact h1
    · rw [abs_of_nonpos h0, abs_of_nonpos (le_trans h1 h0)]; linarith
  have hDCT : HasSum (fun n => ∫ t in 0..y, c n * t ^ n) (∫ t in 0..y, h (t + z₀)) := by
    refine intervalIntegral.hasSum_integral_of_dominated_convergence
      (μ := volume) (a := 0) (b := y)
      (F := fun n t => c n * t ^ n) (f := fun t => h (t + z₀))
      (bound := fun n t => ‖c n‖ * ‖y‖ ^ n) ?_ ?_ ?_ ?_ ?_
    · intro n
      exact (continuous_const.mul (continuous_id.pow n)).aestronglyMeasurable.mono_measure
        Measure.restrict_le_self
    · intro n
      filter_upwards with t ht
      have htabs := htabs' ht
      have hnorm : ‖c n * t ^ n‖ = |c n| * |t| ^ n := by
        rw [norm_mul, norm_pow]
        simp only [Real.norm_eq_abs]
      rw [hnorm, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (abs_nonneg t) htabs n) (abs_nonneg _)
    · filter_upwards with t ht
      simpa using hsumm
    · exact intervalIntegrable_const
    · filter_upwards with t ht
      have htabs := htabs' ht
      have htρ : ENNReal.ofReal ‖t‖ < ρ :=
        lt_of_le_of_lt (ENNReal.ofReal_le_ofReal htabs) hy
      have := hp.hasSum (Metric.mem_eball.mpr (by
        rw [edist_dist, dist_zero_right]; exact htρ))
      simpa [FormalMultilinearSeries.ofScalars_apply_eq, add_comm, smul_eq_mul, mul_comm] using this
  have hterm : ∀ n, (∫ t in 0..y, c n * t ^ n) = c n * y ^ (n + 1) / (↑n + 1) := by
    intro n
    rw [intervalIntegral.integral_const_mul, integral_pow]
    simp only [zero_pow (Nat.succ_ne_zero n), sub_zero]
    ring
  have hDCT' : HasSum (fun n => c n * y ^ (n + 1) / (↑n + 1)) (∫ t in 0..y, h (t + z₀)) := by
    simpa only [hterm] using hDCT
  refine (hasSum_nat_add_iff'
    (f := fun n : ℕ => c (n - 1) * (↑n : ℝ)⁻¹ * y ^ n) 1).mp ?_
  rw [Finset.sum_range_one]
  have hf0 : c ((0 : ℕ) - 1) * (↑(0 : ℕ) : ℝ)⁻¹ * y ^ (0 : ℕ) = 0 := by norm_num
  rw [hf0, sub_zero]
  convert hDCT' using 1
  ext n
  simp only [Nat.add_sub_cancel, div_eq_mul_inv]
  push_cast
  ring

theorem analyticAt_intervalIntegral {h : ℝ → ℝ} {z₀ : ℝ} (hh : AnalyticAt ℝ h z₀) :
    AnalyticAt ℝ (fun z => ∫ s in z₀..z, h s) z₀ := by
  set c : ℕ → ℝ := fun n => iteratedDeriv n h z₀ / (n.factorial : ℝ) with hc
  have hp : HasFPowerSeriesAt h (FormalMultilinearSeries.ofScalars ℝ c) z₀ := by
    rw [hc]; exact hh.hasFPowerSeriesAt
  obtain ⟨ρ, hρ⟩ := hp
  obtain ⟨r, hr0, hrρ⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp hρ.r_pos
  have hr0' : (0 : NNReal) < r := by simpa using hr0
  set T : NNReal := r / 2 with hT
  have hT0 : 0 < T := by rw [hT]; exact half_pos hr0'
  have hTle : (T : ENNReal) ≤ ρ := by
    rw [hT]
    exact (ENNReal.coe_le_coe.mpr (half_le_self hr0'.le)).trans hrρ.le
  have h2T : ((2 * T : NNReal) : ENNReal) = (r : ENNReal) := by
    rw [hT]; congr 1; ring
  have hsumm_base : Summable (fun n => ‖c n‖ * (2 * (T : ℝ)) ^ n) := by
    have hlt : ((2 * T : NNReal) : ENNReal) <
        (FormalMultilinearSeries.ofScalars ℝ c).radius := by
      rw [h2T]; exact hrρ.trans_le hρ.r_le
    have h := (FormalMultilinearSeries.ofScalars ℝ c).summable_norm_mul_pow (r := 2 * T) hlt
    simpa [FormalMultilinearSeries.ofScalars_norm, NNReal.coe_mul] using h
  set q : FormalMultilinearSeries ℝ ℝ ℝ :=
    FormalMultilinearSeries.ofScalars ℝ (fun n => c (n - 1) * (↑n : ℝ)⁻¹) with hq
  have hsumm_q : Summable (fun n => ‖q n‖ * (T : ℝ) ^ n) := by
    have h := summable_coeff_div_shift (a := c) (r := T) hsumm_base
    simpa [hq, FormalMultilinearSeries.ofScalars_norm] using h
  have hqradius : (T : ENNReal) ≤ q.radius :=
    FormalMultilinearSeries.le_radius_of_summable q hsumm_q
  refine ⟨q, ⟨(T : ENNReal), hqradius, ?_, ?_⟩⟩
  · exact_mod_cast hT0
  · intro y hy
    have hy1 : edist y 0 < (T : ENNReal) := hy
    have hy2 : ENNReal.ofReal ‖y‖ < (T : ENNReal) := by
      rw [edist_dist] at hy1
      simpa using hy1
    have hyρ : ENNReal.ofReal ‖y‖ < ρ := hy2.trans_le hTle
    have h := hasSum_antideriv_ofScalars hρ hyρ
    simpa [hq, FormalMultilinearSeries.ofScalars_apply_eq, mul_comm] using h

end Work.Coercivity
