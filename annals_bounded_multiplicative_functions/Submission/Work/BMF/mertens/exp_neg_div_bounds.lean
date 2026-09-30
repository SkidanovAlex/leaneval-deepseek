import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF.mertens

open MeasureTheory intervalIntegral

/-- The definite integral of `v ↦ exp (-v)`: `∫_a^b e^{-v} dv = e^{-a} - e^{-b}`. -/
lemma integral_exp_neg (a b : ℝ) :
    ∫ v in a..b, Real.exp (-v) = Real.exp (-a) - Real.exp (-b) := by
  rw [intervalIntegral.integral_comp_neg (fun x => Real.exp x)]
  rw [integral_exp]

/-- Upper bound for the integral of `v ↦ e^{-v}/v` over `[δ, U]` with `0 < δ ≤ U`:
the integrand is dominated by `e^{-v}/δ`, whose integral is `(e^{-δ} - e^{-U})/δ ≤ e^{-δ}/δ`. -/
lemma exp_neg_div_integral_le (δ U : ℝ) (hδ : 0 < δ) (hδU : δ ≤ U) :
    ∫ v in δ..U, Real.exp (-v) / v ≤ Real.exp (-δ) / δ := by
  have hcont1 : ContinuousOn (fun v : ℝ => Real.exp (-v) / v) (Set.uIcc δ U) := by
    rw [Set.uIcc_of_le hδU]
    apply ContinuousOn.div
    · exact Real.continuous_exp.comp_continuousOn continuousOn_id.neg
    · exact continuousOn_id
    · intro v hv; exact ne_of_gt (lt_of_lt_of_le hδ hv.1)
  have hcont2 : ContinuousOn (fun v : ℝ => Real.exp (-v) / δ) (Set.uIcc δ U) := by
    rw [Set.uIcc_of_le hδU]
    exact ContinuousOn.div_const (Real.continuous_exp.comp_continuousOn continuousOn_id.neg) δ
  have h1 : ∫ v in δ..U, Real.exp (-v) / v ≤ ∫ v in δ..U, Real.exp (-v) / δ := by
    apply integral_mono_on hδU
    · exact hcont1.intervalIntegrable
    · exact hcont2.intervalIntegrable
    · intro v hv
      have hle : 1 / v ≤ 1 / δ := one_div_le_one_div_of_le hδ hv.1
      calc Real.exp (-v) / v = Real.exp (-v) * (1 / v) := by ring
        _ ≤ Real.exp (-v) * (1 / δ) :=
              mul_le_mul_of_nonneg_left hle (le_of_lt (Real.exp_pos _))
        _ = Real.exp (-v) / δ := by ring
  have h2 : ∫ v in δ..U, Real.exp (-v) / δ = (Real.exp (-δ) - Real.exp (-U)) / δ := by
    rw [intervalIntegral.integral_div]
    congr 1
    rw [intervalIntegral.integral_comp_neg (fun x => Real.exp x), integral_exp]
  have h3 : (Real.exp (-δ) - Real.exp (-U)) / δ ≤ Real.exp (-δ) / δ := by
    apply div_le_div_of_nonneg_right _ (le_of_lt hδ)
    linarith [Real.exp_pos (-U)]
  calc ∫ v in δ..U, Real.exp (-v) / v ≤ ∫ v in δ..U, Real.exp (-v) / δ := h1
    _ = (Real.exp (-δ) - Real.exp (-U)) / δ := h2
    _ ≤ Real.exp (-δ) / δ := h3

/-- Lower bound for the integral of `v ↦ e^{-v}/v` over `[δ, U]` with `0 < δ ≤ 1 ≤ U`:
on `[δ, 1]` the pointwise bound `e^{-v} ≥ 1 - v` gives `e^{-v}/v ≥ 1/v - 1`, whose
integral is `log (1/δ) - (1 - δ) ≥ log (1/δ) - 1`; the piece over `[1, U]` is nonnegative. -/
lemma exp_neg_div_integral_ge (δ U : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (h1U : 1 ≤ U) :
    Real.log (1 / δ) - 1 ≤ ∫ v in δ..U, Real.exp (-v) / v := by
  have hcontD1 : ContinuousOn (fun v : ℝ => Real.exp (-v) / v) (Set.uIcc δ 1) := by
    rw [Set.uIcc_of_le hδ1]
    apply ContinuousOn.div
    · exact Real.continuous_exp.comp_continuousOn continuousOn_id.neg
    · exact continuousOn_id
    · intro v hv; exact ne_of_gt (lt_of_lt_of_le hδ hv.1)
  have hcont1U : ContinuousOn (fun v : ℝ => Real.exp (-v) / v) (Set.uIcc 1 U) := by
    rw [Set.uIcc_of_le h1U]
    apply ContinuousOn.div
    · exact Real.continuous_exp.comp_continuousOn continuousOn_id.neg
    · exact continuousOn_id
    · intro v hv; exact ne_of_gt (lt_of_lt_of_le zero_lt_one hv.1)
  have hsplit := integral_add_adjacent_intervals (μ := volume)
      hcontD1.intervalIntegrable hcont1U.intervalIntegrable
  have hnonneg : 0 ≤ ∫ v in 1..U, Real.exp (-v) / v := by
    apply integral_nonneg h1U
    intro v hv
    exact div_nonneg (le_of_lt (Real.exp_pos _)) (by linarith [hv.1])
  have hpoint : ∀ v ∈ Set.Icc δ 1, (1 - v) / v ≤ Real.exp (-v) / v := by
    intro v hv
    have hvpos : 0 < v := lt_of_lt_of_le hδ hv.1
    exact div_le_div_of_nonneg_right (Real.one_sub_le_exp_neg v) (le_of_lt hvpos)
  have hcont' : ContinuousOn (fun v : ℝ => (1 - v) / v) (Set.uIcc δ 1) := by
    rw [Set.uIcc_of_le hδ1]
    apply ContinuousOn.div
    · exact (continuousOn_const.sub continuousOn_id)
    · exact continuousOn_id
    · intro v hv; exact ne_of_gt (lt_of_lt_of_le hδ hv.1)
  have hmono : ∫ v in δ..1, (1 - v) / v ≤ ∫ v in δ..1, Real.exp (-v) / v :=
    integral_mono_on hδ1 hcont'.intervalIntegrable hcontD1.intervalIntegrable hpoint
  have hcontInv : ContinuousOn (fun v : ℝ => 1 / v) (Set.uIcc δ 1) := by
    rw [Set.uIcc_of_le hδ1]
    exact ContinuousOn.div continuousOn_const continuousOn_id
      (fun v hv => ne_of_gt (lt_of_lt_of_le hδ hv.1))
  have hval : ∫ v in δ..1, (1 - v) / v = Real.log (1 / δ) - (1 - δ) := by
    have hcongr : ∫ v in δ..1, (1 - v) / v = ∫ v in δ..1, (1 / v - 1) := by
      apply integral_congr
      intro v hv
      rw [Set.uIcc_of_le hδ1] at hv
      have hv0 : v ≠ 0 := ne_of_gt (lt_of_lt_of_le hδ hv.1)
      field_simp
    rw [hcongr, intervalIntegral.integral_sub hcontInv.intervalIntegrable
      continuousOn_const.intervalIntegrable,
      integral_one_div_of_pos hδ zero_lt_one, integral_one]
  have hmid : Real.log (1 / δ) - 1 ≤ ∫ v in δ..1, Real.exp (-v) / v := by
    linarith [hmono, hval]
  linarith [hsplit, hmid, hnonneg, hsplit.ge]

/-- Nonnegativity of the integral of `v ↦ e^{-v}/v` over `[δ, U]` with `1 ≤ δ ≤ U`. -/
lemma exp_neg_div_integral_nonneg (δ U : ℝ) (hδ : 1 ≤ δ) (hδU : δ ≤ U) :
    0 ≤ ∫ v in δ..U, Real.exp (-v) / v := by
  apply integral_nonneg hδU
  intro v hv
  exact div_nonneg (le_of_lt (Real.exp_pos _)) (by linarith [hv.1, hδ])

theorem exp_neg_div_bounds :
    (∀ δ U : ℝ, 0 < δ → δ ≤ U →
        ∫ v in δ..U, Real.exp (-v) / v ≤ Real.exp (-δ) / δ) ∧
    (∀ δ U : ℝ, 0 < δ → δ ≤ 1 → 1 ≤ U →
        Real.log (1 / δ) - 1 ≤ ∫ v in δ..U, Real.exp (-v) / v) ∧
    (∀ δ U : ℝ, 1 ≤ δ → δ ≤ U → 0 ≤ ∫ v in δ..U, Real.exp (-v) / v) :=
  ⟨exp_neg_div_integral_le, exp_neg_div_integral_ge, exp_neg_div_integral_nonneg⟩

end Work.BMF.mertens
