import Mathlib.MeasureTheory.Covering.OneDim
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Almost everywhere convergence of interval averages

This file proves a Lebesgue-differentiation-type statement: for an integrable
function `g : ℝ → ℝ`, for almost every `x`, the averages of `g` over the
intervals `[x - a, x + b]` (with `a, b ≥ 0`) converge to `g x` as the length
`a + b` tends to `0`. Since the point `x` is allowed to sit anywhere inside the
interval, including at an endpoint, this genuinely requires the *one-sided*
Lebesgue differentiation theorem (from the left and from the right), which is
obtained here from the general Vitali-family differentiation theorem
`VitaliFamily.ae_tendsto_average` applied to `IsUnifLocDoublingMeasure.vitaliFamily`
and to the one-dimensional intervals from `MeasureTheory.Covering.OneDim`.
-/

open MeasureTheory Set Filter Topology
open scoped Topology

namespace Commons.Analysis.Measure

/-- For `h > 0`, the set average of `g` over `Icc x (x + h)` is `h⁻¹` times the
interval integral `∫ y in x..(x+h), g y`. -/
private lemma setAverage_Icc_right_eq (g : ℝ → ℝ) {x h : ℝ} (hh : 0 < h) :
    ⨍ z in Icc x (x+h), g z ∂volume = h⁻¹ * ∫ z in x..(x+h), g z := by
  rw [setAverage_eq]
  have hx : x ≤ x + h := by linarith
  have hvol : volume.real (Icc x (x + h)) = h := by
    rw [Measure.real_def, Real.volume_Icc]
    have : x + h - x = h := by ring
    rw [this, ENNReal.toReal_ofReal hh.le]
  rw [hvol, smul_eq_mul]
  congr 1
  rw [intervalIntegral.integral_of_le hx, integral_Icc_eq_integral_Ioc]

/-- For `h > 0`, the set average of `g` over `Icc (x - h) x` is `h⁻¹` times the
interval integral `∫ y in (x-h)..x, g y`. -/
private lemma setAverage_Icc_left_eq (g : ℝ → ℝ) {x h : ℝ} (hh : 0 < h) :
    ⨍ z in Icc (x-h) x, g z ∂volume = h⁻¹ * ∫ z in (x-h)..x, g z := by
  rw [setAverage_eq]
  have hx : x - h ≤ x := by linarith
  have hvol : volume.real (Icc (x - h) x) = h := by
    rw [Measure.real_def, Real.volume_Icc]
    have : x - (x - h) = h := by ring
    rw [this, ENNReal.toReal_ofReal hh.le]
  rw [hvol, smul_eq_mul]
  congr 1
  rw [intervalIntegral.integral_of_le hx, integral_Icc_eq_integral_Ioc]

/-- One-sided Lebesgue differentiation theorem, to the right of `x`:
for almost every `x`, `h⁻¹ ∫ y in x..(x+h), g y → g x` as `h → 0⁺`. -/
lemma ae_tendsto_intervalAverage_right (g : ℝ → ℝ) (hg : Integrable g) :
    ∀ᵐ x ∂(volume : Measure ℝ),
      Tendsto (fun h : ℝ => h⁻¹ * ∫ y in x..(x+h), g y) (𝓝[>] 0) (𝓝 (g x)) := by
  have hf : LocallyIntegrable g volume := hg.locallyIntegrable
  have hv := (IsUnifLocDoublingMeasure.vitaliFamily (volume : Measure ℝ) 1).ae_tendsto_average hf
  filter_upwards [hv] with x hx
  have hcomp := hx.comp (Real.tendsto_Icc_vitaliFamily_right x)
  have htrans : Tendsto (fun h : ℝ => x + h) (𝓝[>] 0) (𝓝[>] x) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨?_, ?_⟩
    · have h0 : Tendsto (fun h : ℝ => x + h) (𝓝 (0:ℝ)) (𝓝 x) := by
        simpa using (tendsto_const_nhds (x := x) (f := 𝓝 (0:ℝ))).add tendsto_id
      exact h0.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with h hh
      show x + h ∈ Ioi x
      simp only [mem_Ioi] at hh ⊢
      linarith
  have h2 := hcomp.comp htrans
  refine h2.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with h hh
  exact setAverage_Icc_right_eq g hh

/-- One-sided Lebesgue differentiation theorem, to the left of `x`:
for almost every `x`, `h⁻¹ ∫ y in (x-h)..x, g y → g x` as `h → 0⁺`. -/
lemma ae_tendsto_intervalAverage_left (g : ℝ → ℝ) (hg : Integrable g) :
    ∀ᵐ x ∂(volume : Measure ℝ),
      Tendsto (fun h : ℝ => h⁻¹ * ∫ y in (x-h)..x, g y) (𝓝[>] 0) (𝓝 (g x)) := by
  have hf : LocallyIntegrable g volume := hg.locallyIntegrable
  have hv := (IsUnifLocDoublingMeasure.vitaliFamily (volume : Measure ℝ) 1).ae_tendsto_average hf
  filter_upwards [hv] with x hx
  have hcomp := hx.comp (Real.tendsto_Icc_vitaliFamily_left x)
  have htrans : Tendsto (fun h : ℝ => x - h) (𝓝[>] 0) (𝓝[<] x) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨?_, ?_⟩
    · have h0 : Tendsto (fun h : ℝ => x - h) (𝓝 (0:ℝ)) (𝓝 x) := by
        simpa using (tendsto_const_nhds (x := x) (f := 𝓝 (0:ℝ))).sub tendsto_id
      exact h0.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with h hh
      show x - h ∈ Iio x
      simp only [mem_Iio, mem_Ioi] at hh ⊢
      linarith
  have h2 := hcomp.comp htrans
  refine h2.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with h hh
  exact setAverage_Icc_left_eq g hh

theorem ae_tendsto_interval_average (g : ℝ → ℝ) (hg : MeasureTheory.Integrable g) :
    ∀ᵐ x ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ),
      ∀ ε > 0, ∃ δ > 0, ∀ a b : ℝ, 0 ≤ a → 0 ≤ b → a + b < δ → 0 < a + b →
        |(a + b)⁻¹ * (∫ y in (x - a)..(x + b), g y) - g x| < ε := by
  filter_upwards [ae_tendsto_intervalAverage_right g hg, ae_tendsto_intervalAverage_left g hg]
    with x hRx hLx
  intro ε hε
  have hε2 : 0 < ε / 2 := by linarith
  -- Extract the two one-sided thresholds.
  have hpR : {h : ℝ | |h⁻¹ * (∫ y in x..(x+h), g y) - g x| < ε/2} ∈ 𝓝[>] (0:ℝ) := by
    filter_upwards [hRx.eventually (Metric.ball_mem_nhds (g x) hε2)] with h hh
    rwa [Real.dist_eq] at hh
  obtain ⟨δR, hδRpos, hδRsub⟩ := mem_nhdsGT_iff_exists_Ioc_subset.mp hpR
  have hpL : {h : ℝ | |h⁻¹ * (∫ y in (x-h)..x, g y) - g x| < ε/2} ∈ 𝓝[>] (0:ℝ) := by
    filter_upwards [hLx.eventually (Metric.ball_mem_nhds (g x) hε2)] with h hh
    rwa [Real.dist_eq] at hh
  obtain ⟨δL, hδLpos, hδLsub⟩ := mem_nhdsGT_iff_exists_Ioc_subset.mp hpL
  refine ⟨min δR δL, lt_min hδRpos hδLpos, ?_⟩
  intro a b ha hb hab hpos
  -- Bound the left and right "centred" pieces.
  have hPbound : |(∫ y in (x-a)..x, g y) - a * g x| ≤ a * (ε/2) := by
    rcases eq_or_lt_of_le ha with ha' | ha'
    · rw [← ha']; simp
    · have ha_mem : a ∈ Ioc 0 δL :=
        ⟨ha', le_of_lt (lt_of_lt_of_le (lt_of_le_of_lt (le_add_of_nonneg_right hb) hab)
          (min_le_right _ _))⟩
      have hbnd := hδLsub ha_mem
      have heq : (∫ y in (x-a)..x, g y) - a * g x
          = a * (a⁻¹ * (∫ y in (x-a)..x, g y) - g x) := by
        rw [mul_sub, mul_inv_cancel_left₀ ha'.ne']
      rw [heq, abs_mul, abs_of_pos ha']
      exact le_of_lt (mul_lt_mul_of_pos_left hbnd ha')
  have hQbound : |(∫ y in x..(x+b), g y) - b * g x| ≤ b * (ε/2) := by
    rcases eq_or_lt_of_le hb with hb' | hb'
    · rw [← hb']; simp
    · have hb_mem : b ∈ Ioc 0 δR :=
        ⟨hb', le_of_lt (lt_of_lt_of_le (lt_of_le_of_lt (le_add_of_nonneg_left ha) hab)
          (min_le_left _ _))⟩
      have hbnd := hδRsub hb_mem
      have heq : (∫ y in x..(x+b), g y) - b * g x
          = b * (b⁻¹ * (∫ y in x..(x+b), g y) - g x) := by
        rw [mul_sub, mul_inv_cancel_left₀ hb'.ne']
      rw [heq, abs_mul, abs_of_pos hb']
      exact le_of_lt (mul_lt_mul_of_pos_left hbnd hb')
  -- Split the interval integral `∫_{x-a}^{x+b}` at `x`.
  have hdecomp : (a + b)⁻¹ * (∫ y in (x - a)..(x + b), g y) - g x
      = (a + b)⁻¹ * (((∫ y in (x-a)..x, g y) - a * g x)
          + ((∫ y in x..(x+b), g y) - b * g x)) := by
    have h1 : ∫ y in (x - a)..(x + b), g y = (∫ y in (x-a)..x, g y) + ∫ y in x..(x+b), g y :=
      (intervalIntegral.integral_add_adjacent_intervals (a := x - a) (b := x) (c := x + b)
        hg.intervalIntegrable hg.intervalIntegrable).symm
    rw [h1]
    have hne : (a + b) ≠ 0 := ne_of_gt hpos
    field_simp
    ring
  rw [hdecomp, abs_mul, abs_of_pos (inv_pos.mpr hpos)]
  calc (a + b)⁻¹ * |((∫ y in (x-a)..x, g y) - a * g x)
          + ((∫ y in x..(x+b), g y) - b * g x)|
      ≤ (a + b)⁻¹ * (|(∫ y in (x-a)..x, g y) - a * g x|
          + |(∫ y in x..(x+b), g y) - b * g x|) :=
        mul_le_mul_of_nonneg_left (abs_add_le _ _) (inv_nonneg.mpr hpos.le)
    _ ≤ (a + b)⁻¹ * (a * (ε/2) + b * (ε/2)) :=
        mul_le_mul_of_nonneg_left (add_le_add hPbound hQbound) (inv_nonneg.mpr hpos.le)
    _ = ε/2 := by
        rw [← add_mul, ← mul_assoc, inv_mul_cancel₀ (ne_of_gt hpos), one_mul]
    _ < ε := by linarith

end Commons.Analysis.Measure