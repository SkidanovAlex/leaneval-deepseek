import Mathlib
import Submission.Work.NumberTheory.Chen.APSwitchUpper.riPhiSharpCrude
import Submission.Work.NumberTheory.Chen.APSwitchUpper.crudeV_integral_le
import Submission.Work.NumberTheory.Chen.APSwitchUpper.logExpLeft
import Submission.Work.NumberTheory.Chen.APSwitchUpper.logExpRight

namespace Work.NumberTheory.Chen.APSwitchUpper

noncomputable section

open MeasureTheory

/-!
# `APSwitchUpper.crudePairHypotheses` — the crude pair `(crudeU, crudeV)` is a supersolution

`riPhiSharpCrude` defines the explicit pair

* `crudeU s = 8` for `s < 1`, `(9 − s)/s` for `1 ≤ s ≤ 3`, `2·exp (3 − s)` for `3 < s`,
* `crudeV s = 6·exp (2 − s)`,

whose purpose is to dominate the delay family `profC` and its sums
(`riPhi_le_of_supersolution`).  This file discharges all six hypotheses of that
comparison principle for the pair: the two local-integrability statements, the base
inequality `profC 0 ≤ crudeU`, the clamping inequality on `[1,3]`, and the two fixed
point inequalities of the delay system.

The mathematics: `∫_{s−1}^b crudeU` is a sum of the elementary integrals
`∫ (9−u)/u = 9 log u − u` (on `[1,3]`) and `∫ 2 exp (3−u) = 2` (on the tail), so the
first fixed point inequality reduces to the one-variable inequality
`9 log (3/σ) + σ − 1 ≤ 6 (σ+1) exp (1−σ)` for `σ = s−1 ∈ [1,3]`, which is provided by
`logExpLeft`/`logExpRight`; the second reduces to
`6 exp (2−max(s−1,2)) ≤ s · crudeU s`.
-/

/-! ## Membership in `uIcc` -/

theorem uIcc_left {a b x : ℝ} (hab : a ≤ b) (hx : x ∈ Set.uIcc a b) : a ≤ x := by
  rw [Set.uIcc_of_le hab] at hx; exact hx.1

theorem uIcc_right {a b x : ℝ} (hab : a ≤ b) (hx : x ∈ Set.uIcc a b) : x ≤ b := by
  rw [Set.uIcc_of_le hab] at hx; exact hx.2

/-! ## Local integrability -/

theorem crudeU_measurable : Measurable crudeU := by
  unfold crudeU
  refine Measurable.ite (measurableSet_lt measurable_id measurable_const)
    measurable_const ?_
  refine Measurable.ite (measurableSet_le measurable_id measurable_const) ?_ ?_
  · exact (measurable_const.sub measurable_id).div measurable_id
  · exact measurable_const.mul
      (Real.continuous_exp.measurable.comp (measurable_const.sub measurable_id))

theorem crudeU_norm_le (s : ℝ) : ‖crudeU s‖ ≤ 8 := by
  rw [Real.norm_eq_abs]
  unfold crudeU
  by_cases h1 : s < 1
  · rw [if_pos h1]; norm_num
  · rw [if_neg h1]
    by_cases h3 : s ≤ 3
    · rw [if_pos h3]
      have hs0 : 0 < s := by linarith [not_lt.mp h1]
      have hnn : 0 ≤ (9 - s) / s := div_nonneg (by linarith [h3]) (le_of_lt hs0)
      rw [abs_of_nonneg hnn, div_le_iff₀ hs0]
      linarith [not_lt.mp h1]
    · rw [if_neg h3]
      have h3' : 3 < s := not_le.mp h3
      have hpos : 0 < 2 * Real.exp (3 - s) := by positivity
      rw [abs_of_pos hpos]
      have hexp : Real.exp (3 - s) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
      nlinarith [Real.exp_pos (3 - s)]

theorem crudeU_intervalIntegrable (a b : ℝ) : IntervalIntegrable crudeU volume a b :=
  ⟨Integrable.of_bound crudeU_measurable.aestronglyMeasurable 8
      (Filter.Eventually.of_forall crudeU_norm_le),
    Integrable.of_bound crudeU_measurable.aestronglyMeasurable 8
      (Filter.Eventually.of_forall crudeU_norm_le)⟩

theorem crudeV_continuous : Continuous crudeV := by
  unfold crudeV; fun_prop

theorem crudeV_intervalIntegrable (a b : ℝ) : IntervalIntegrable crudeV volume a b :=
  crudeV_continuous.intervalIntegrable a b

/-! ## The two elementary conjuncts -/

theorem profC_zero_le_crudeU (s : ℝ) : profC 0 s ≤ crudeU s := by
  rw [profC_zero]
  by_cases h : 1 ≤ s ∧ s ≤ 3
  · rw [if_pos h, crudeU_of_mem h.1 h.2]
    exact div_le_div_of_nonneg_right (by linarith [h.1]) (by linarith [h.1])
  · rw [if_neg h]
    exact crudeU_nonneg s

theorem crudeU_linear (t : ℝ) (h1 : 1 ≤ t) (h3 : t ≤ 3) :
    (3 - t + 3 * crudeU 3) / t ≤ crudeU t := by
  have hkey : (3 : ℝ) - t + 3 * crudeU 3 = 9 - t := by rw [crudeU_three]; ring
  rw [hkey, crudeU_of_mem h1 h3]

/-! ## Integral evaluations -/

/-- `crudeU u = 2 exp (3-u)` for `u ≥ 3`. -/
theorem crudeU_of_three_le {u : ℝ} (h : 3 ≤ u) : crudeU u = 2 * Real.exp (3 - u) := by
  rcases eq_or_lt_of_le h with h' | h'
  · rw [← h', crudeU_three]; norm_num
  · exact crudeU_of_three_lt h'

/-- The tail integral: `∫_a^b 2 exp (3-u) = 2 (exp (3-a) - exp (3-b))`. -/
theorem integral_exp3 (a b : ℝ) :
    ∫ u in a..b, 2 * Real.exp (3 - u) = 2 * (Real.exp (3 - a) - Real.exp (3 - b)) := by
  rw [intervalIntegral.integral_const_mul,
    intervalIntegral.integral_comp_sub_left (fun x : ℝ => Real.exp x) 3, integral_exp]

/-- The affine part: `∫_a^b (9-u)/u = 9 log (b/a) - (b - a)` for `0 < a ≤ b`. -/
theorem integral_nine_sub_div (a b : ℝ) (ha : 0 < a) (hab : a ≤ b) :
    ∫ u in a..b, ((9 : ℝ) - u) / u = 9 * Real.log (b / a) - (b - a) := by
  have h0 : (0 : ℝ) ∉ Set.uIcc a b := by
    intro hmem
    have := uIcc_left hab hmem
    linarith
  have hcont : ContinuousOn (fun u : ℝ => 9 * u⁻¹) (Set.uIcc a b) := by
    refine ContinuousOn.const_mul ?_ 9
    refine ContinuousOn.inv₀ continuousOn_id ?_
    intro x hx
    exact ne_of_gt (lt_of_lt_of_le ha (uIcc_left hab hx))
  have hcongr : (∫ u in a..b, ((9 : ℝ) - u) / u) = ∫ u in a..b, (9 * u⁻¹ - 1) := by
    refine intervalIntegral.integral_congr (fun u hu => ?_)
    have hu0 : u ≠ 0 := ne_of_gt (lt_of_lt_of_le ha (uIcc_left hab hu))
    rw [sub_div, div_self hu0, div_eq_mul_inv]
  have hI : IntervalIntegrable (fun u : ℝ => 9 * u⁻¹) volume a b := hcont.intervalIntegrable
  have hI2 : IntervalIntegrable (fun _ : ℝ => (1 : ℝ)) volume a b := intervalIntegrable_const
  rw [hcongr, intervalIntegral.integral_sub hI hI2, intervalIntegral.integral_const_mul,
    integral_inv h0, intervalIntegral.integral_const, smul_eq_mul, mul_one]

/-! ## The one-variable inequality -/

/-- `9 log (3/σ) + σ - 1 ≤ 6 (σ+1) exp (1-σ)` for `σ ∈ [1,3]`. -/
theorem crude_log_exp (σ : ℝ) (h1 : 1 ≤ σ) (h3 : σ ≤ 3) :
    9 * Real.log (3 / σ) + σ - 1 ≤ 6 * (σ + 1) * Real.exp (1 - σ) := by
  by_cases h : σ ≤ 2
  · exact logExpLeft σ h1 h
  · exact logExpRight σ (le_of_lt (not_le.mp h)) h3

/-- The form used below: for `2 ≤ s ≤ 4`, `9 log (3/(s-1)) + s - 2 ≤ 6 s exp (2-s)`. -/
theorem crude_log_exp' (s : ℝ) (h2 : 2 ≤ s) (h4 : s ≤ 4) :
    9 * Real.log (3 / (s - 1)) + s - 2 ≤ 6 * s * Real.exp (2 - s) := by
  have h1 : (1 : ℝ) ≤ s - 1 := by linarith
  have h3 : s - 1 ≤ 3 := by linarith
  have hkey := crude_log_exp (s - 1) h1 h3
  have hkey' : 9 * Real.log (3 / (s - 1)) + ((s : ℝ) - 1) - 1
      ≤ 6 * s * Real.exp (2 - s) := by
    simpa only [show ((s : ℝ) - 1 + 1) = s by ring,
      show (1 : ℝ) - (s - 1) = 2 - s by ring] using hkey
  linarith

theorem crudeU_integral_le :
    ∀ s : ℝ, 2 ≤ s → ∀ b : ℝ, s - 1 ≤ b →
      ∫ u in (s - 1)..b, crudeU u
      ≤ s * crudeV s := by
  intro s hs b hb
  have hcv : s * crudeV s = 6 * s * Real.exp (2 - s) := by
    simp only [crudeV]; ring
  rcases le_or_gt 4 s with hs4 | hs4
  · -- `s ≥ 4`: on `[s-1,b]` one has `u ≥ 3`, so `crudeU u = 2 exp (3-u)`.
    have hcongr : (∫ u in (s - 1)..b, crudeU u) = ∫ u in (s - 1)..b, 2 * Real.exp (3 - u) :=
      intervalIntegral.integral_congr
        (fun u hu => crudeU_of_three_le (by linarith [uIcc_left hb hu]))
    rw [hcongr, integral_exp3, hcv]
    have hstep : 2 * (Real.exp (3 - (s - 1)) - Real.exp (3 - b))
        ≤ 2 * Real.exp (3 - (s - 1)) := by
      have := Real.exp_pos (3 - b); linarith
    refine le_trans hstep ?_
    rw [show 3 - (s - 1) = 2 + (2 - s) by ring, Real.exp_add]
    have hexp2 : Real.exp 2 ≤ 9 := by
      have h3 := Real.exp_one_lt_three
      have hp := Real.exp_pos (1 : ℝ)
      calc Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
        _ ≤ 9 := by nlinarith
    have hEs : 0 < Real.exp (2 - s) := Real.exp_pos _
    have h1 : 2 * Real.exp 2 ≤ 6 * s := by nlinarith
    calc 2 * (Real.exp 2 * Real.exp (2 - s)) = (2 * Real.exp 2) * Real.exp (2 - s) := by ring
      _ ≤ (6 * s) * Real.exp (2 - s) := mul_le_mul_of_nonneg_right h1 (le_of_lt hEs)
      _ = 6 * s * Real.exp (2 - s) := by ring
  · -- `2 ≤ s ≤ 4`: extend `b` to `B = max b 3` (nonnegative integrand) and split at `3`.
    have hs4' : s ≤ 4 := le_of_lt hs4
    set B : ℝ := max b 3 with hB
    have hBb : b ≤ B := le_max_left _ _
    have hsB : s - 1 ≤ B := le_trans hb hBb
    have h3B : (3 : ℝ) ≤ B := le_max_right _ _
    have hmono : (∫ u in (s - 1)..b, crudeU u) ≤ ∫ u in (s - 1)..B, crudeU u := by
      have hadd : (∫ u in (s - 1)..b, crudeU u) + ∫ u in b..B, crudeU u
          = ∫ u in (s - 1)..B, crudeU u :=
        intervalIntegral.integral_add_adjacent_intervals (crudeU_intervalIntegrable _ _)
          (crudeU_intervalIntegrable _ _)
      have hnn : 0 ≤ ∫ u in b..B, crudeU u :=
        intervalIntegral.integral_nonneg_of_forall hBb (fun u => crudeU_nonneg u)
      linarith
    refine le_trans hmono ?_
    have h3s : s - 1 ≤ 3 := by linarith
    have hsplit : (∫ u in (s - 1)..(3 : ℝ), crudeU u) + ∫ u in (3 : ℝ)..B, crudeU u
        = ∫ u in (s - 1)..B, crudeU u :=
      intervalIntegral.integral_add_adjacent_intervals (crudeU_intervalIntegrable _ _)
        (crudeU_intervalIntegrable _ _)
    have hleft : (∫ u in (s - 1)..(3 : ℝ), crudeU u)
        = 9 * Real.log (3 / (s - 1)) - (3 - (s - 1)) := by
      refine Eq.trans (intervalIntegral.integral_congr
        (fun u hu => crudeU_of_mem (by linarith [uIcc_left h3s hu]) (uIcc_right h3s hu))) ?_
      exact integral_nine_sub_div (s - 1) 3 (by linarith) h3s
    have hright : (∫ u in (3 : ℝ)..B, crudeU u) ≤ 2 := by
      have hcongr : (∫ u in (3 : ℝ)..B, crudeU u) = ∫ u in (3 : ℝ)..B, 2 * Real.exp (3 - u) :=
        intervalIntegral.integral_congr (fun u hu => crudeU_of_three_le (uIcc_left h3B hu))
      rw [hcongr, integral_exp3]
      have hpos := Real.exp_pos (3 - B)
      have hone : Real.exp (3 - (3 : ℝ)) = 1 := by norm_num
      rw [hone]
      linarith
    rw [← hsplit, hleft, hcv]
    have hstar := crude_log_exp' s hs hs4'
    have h3s' : (3 : ℝ) - (s - 1) = 4 - s := by ring
    linarith [hright, hstar, h3s']

theorem crudePairHypotheses :
    (∀ a b : ℝ, IntervalIntegrable Work.NumberTheory.Chen.APSwitchUpper.crudeU volume a b)
  ∧ (∀ a b : ℝ, IntervalIntegrable Work.NumberTheory.Chen.APSwitchUpper.crudeV volume a b)
  ∧ (∀ s : ℝ, Work.NumberTheory.Chen.APSwitchUpper.profC 0 s ≤ Work.NumberTheory.Chen.APSwitchUpper.crudeU s)
  ∧ (∀ t : ℝ, 1 ≤ t → t ≤ 3 →
      (3 - t + 3 * Work.NumberTheory.Chen.APSwitchUpper.crudeU 3) / t
        ≤ Work.NumberTheory.Chen.APSwitchUpper.crudeU t)
  ∧ (∀ s : ℝ, 2 ≤ s → ∀ b : ℝ, max (s - 1) 2 ≤ b →
      (3 - s) * (if s ≤ 3 then (1 : ℝ) else 0)
        + ∫ u in (max (s - 1) 2)..b, Work.NumberTheory.Chen.APSwitchUpper.crudeV u
      ≤ s * Work.NumberTheory.Chen.APSwitchUpper.crudeU s)
  ∧ (∀ s : ℝ, 2 ≤ s → ∀ b : ℝ, s - 1 ≤ b →
      ∫ u in (s - 1)..b, Work.NumberTheory.Chen.APSwitchUpper.crudeU u
      ≤ s * Work.NumberTheory.Chen.APSwitchUpper.crudeV s) := by
  exact ⟨crudeU_intervalIntegrable, crudeV_intervalIntegrable, profC_zero_le_crudeU,
    crudeU_linear, crudeV_integral_le, crudeU_integral_le⟩

end

end Work.NumberTheory.Chen.APSwitchUpper
