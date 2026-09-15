import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

namespace Commons.Analysis.Integral

open scoped ENNReal
open MeasureTheory

/-- Weighted Minkowski (triangle) inequality for a finite family of nonnegative
functions and a nonnegative weight `W`: for `q ≥ 1`,
`(∫ (∑ᵢ uᵢ)^q W)^{1/q} ≤ ∑ᵢ (∫ uᵢ^q W)^{1/q}`.

This is the boundedness-free counterpart of `integral_rpow_finset_sum_mul_le`,
working with `AEMeasurable`/`Integrable` hypotheses instead of a uniform bound. -/
theorem integral_sum_rpow_mul_le_sum_integral_rpow_mul {α : Type*} [MeasurableSpace α]
    {μ : MeasureTheory.Measure α} [MeasureTheory.SFinite μ] {W : α → ℝ} (hW : Measurable W)
    (hW0 : ∀ x, 0 ≤ W x) (_hWint : MeasureTheory.Integrable W μ) {ι : Type*} [Fintype ι]
    {q : ℝ} (hq : 1 ≤ q) {u : ι → α → ℝ} (hu : ∀ i, AEMeasurable (u i) μ)
    (hu0 : ∀ i x, 0 ≤ u i x)
    (hint : ∀ i, MeasureTheory.Integrable (fun x => (u i x) ^ q * W x) μ)
    (hint2 : MeasureTheory.Integrable (fun x => (∑ i, u i x) ^ q * W x) μ) :
    (∫ x, (∑ i, u i x) ^ q * W x ∂μ) ^ (1 / q)
      ≤ ∑ i, (∫ x, (u i x) ^ q * W x ∂μ) ^ (1 / q) := by
  classical
  have hq0 : 0 < q := lt_of_lt_of_le zero_lt_one hq
  set ν : MeasureTheory.Measure α := μ.withDensity (fun x => ENNReal.ofReal (W x)) with hνdef
  have hWm : Measurable (fun x => ENNReal.ofReal (W x)) := hW.ennreal_ofReal
  have hQ0 : (ENNReal.ofReal q) ≠ 0 := ne_of_gt (ENNReal.ofReal_pos.mpr hq0)
  have hQtop : (ENNReal.ofReal q) ≠ ∞ := ENNReal.ofReal_ne_top
  have hq1enn : (1 : ℝ≥0∞) ≤ ENNReal.ofReal q := ENNReal.one_le_ofReal.mpr hq
  -- conversion of `ν`-integrals into weighted `μ`-integrals
  have hconv : ∀ g : α → ℝ, (∫ x, g x ∂ν) = ∫ x, g x * W x ∂μ := by
    intro g
    rw [hνdef, integral_withDensity_eq_integral_toReal_smul
      (f := fun x => ENNReal.ofReal (W x)) hWm
      (ae_of_all μ (fun x => ENNReal.ofReal_lt_top)) g]
    simp only [smul_eq_mul]
    exact integral_congr_ae (ae_of_all μ (fun x => by
      simp only [ENNReal.toReal_ofReal (hW0 x), mul_comm]))
  -- `μ`-measurability upgrades to `ν`-measurability
  have huν : ∀ i, AEMeasurable (u i) ν := fun i =>
    (hu i).mono_ac (withDensity_absolutelyContinuous μ (fun x => ENNReal.ofReal (W x)))
  -- weighted integrability gives `MemLp` w.r.t. `ν`
  have memLp_of_int : ∀ (h : α → ℝ), (∀ x, 0 ≤ h x) → AEMeasurable h ν →
      MeasureTheory.Integrable (fun x => h x ^ q * W x) μ → MemLp h (ENNReal.ofReal q) ν := by
    intro h hh0 hhν hint'
    rw [← integrable_norm_rpow_iff hhν.aestronglyMeasurable hQ0 hQtop]
    have h1 : (fun x => ‖h x‖ ^ (ENNReal.ofReal q).toReal) = fun x => h x ^ q := by
      funext x
      rw [ENNReal.toReal_ofReal hq0.le, Real.norm_of_nonneg (hh0 x)]
    rw [h1]
    rw [hνdef]
    rw [integrable_withDensity_iff_integrable_smul' hWm
      (ae_of_all μ (fun _ => ENNReal.ofReal_lt_top))]
    have h2 : (fun x => (ENNReal.ofReal (W x)).toReal • h x ^ q) = fun x => h x ^ q * W x := by
      funext x
      rw [ENNReal.toReal_ofReal (hW0 x), smul_eq_mul, mul_comm]
    rw [h2]
    exact hint'
  -- bridge: `eLpNorm` on `ν` equals the weighted `μ`-integral raised to `1/q`
  have hkey : ∀ (h : α → ℝ), (∀ x, 0 ≤ h x) → AEMeasurable h ν →
      MeasureTheory.Integrable (fun x => h x ^ q * W x) μ →
      eLpNorm h (ENNReal.ofReal q) ν = ENNReal.ofReal ((∫ x, h x ^ q * W x ∂μ) ^ (1 / q)) := by
    intro h hh0 hhν hint'
    have hmem := memLp_of_int h hh0 hhν hint'
    have hInt : (∫ a, ‖h a‖ ^ q ∂ν) = ∫ x, h x ^ q * W x ∂μ := by
      have h1 : (∫ a, ‖h a‖ ^ q ∂ν) = ∫ a, h a ^ q ∂ν := by
        apply integral_congr_ae
        filter_upwards with a
        rw [Real.norm_of_nonneg (hh0 a)]
      rw [h1, hconv (fun x => h x ^ q)]
    rw [hmem.eLpNorm_eq_integral_rpow_norm hQ0 hQtop]
    rw [show (ENNReal.ofReal q).toReal = q from ENNReal.toReal_ofReal hq0.le]
    simp only [one_div]
    rw [hInt]
  -- Minkowski in `L^q(ν)`
  have hsum_fun : (fun x => ∑ i, u i x) = ∑ i, u i := by
    funext x; simp
  have hsumν : AEMeasurable (fun x => ∑ i, u i x) ν := by
    rw [hsum_fun]
    exact Finset.aemeasurable_sum Finset.univ (fun i _ => huν i)
  have hMink : eLpNorm (fun x => ∑ i, u i x) (ENNReal.ofReal q) ν
      ≤ ∑ i, eLpNorm (u i) (ENNReal.ofReal q) ν := by
    have h := eLpNorm_sum_le (μ := ν) (f := fun i => u i) (s := Finset.univ)
      (fun i _ => (huν i).aestronglyMeasurable) hq1enn
    have h2 : (∑ i ∈ (Finset.univ : Finset ι), u i) = fun x => ∑ i, u i x := by
      funext x; simp
    rw [h2] at h
    simpa using h
  have hkeySum : eLpNorm (fun x => ∑ i, u i x) (ENNReal.ofReal q) ν
      = ENNReal.ofReal ((∫ x, (∑ i, u i x) ^ q * W x ∂μ) ^ (1 / q)) :=
    hkey (fun x => ∑ i, u i x) (fun x => Finset.sum_nonneg (fun i _ => hu0 i x)) hsumν hint2
  have hRHS : (∑ i, eLpNorm (u i) (ENNReal.ofReal q) ν)
      = ENNReal.ofReal (∑ i, (∫ x, (u i x) ^ q * W x ∂μ) ^ (1 / q)) := by
    rw [Finset.sum_congr rfl (fun i _ => hkey (u i) (hu0 i) (huν i) (hint i))]
    exact (ENNReal.ofReal_sum_of_nonneg (fun i _ => Real.rpow_nonneg
      (integral_nonneg (fun x => mul_nonneg (Real.rpow_nonneg (hu0 i x) q) (hW0 x))) _)).symm
  have hsum_nn : 0 ≤ ∑ i, (∫ x, (u i x) ^ q * W x ∂μ) ^ (1 / q) :=
    Finset.sum_nonneg (fun i _ => Real.rpow_nonneg
      (integral_nonneg (fun x => mul_nonneg (Real.rpow_nonneg (hu0 i x) q) (hW0 x))) _)
  refine (ENNReal.ofReal_le_ofReal_iff hsum_nn).mp ?_
  calc ENNReal.ofReal ((∫ x, (∑ i, u i x) ^ q * W x ∂μ) ^ (1 / q))
      = eLpNorm (fun x => ∑ i, u i x) (ENNReal.ofReal q) ν := hkeySum.symm
    _ ≤ ∑ i, eLpNorm (u i) (ENNReal.ofReal q) ν := hMink
    _ = ENNReal.ofReal (∑ i, (∫ x, (u i x) ^ q * W x ∂μ) ^ (1 / q)) := hRHS

theorem weighted_l2_minkowski_rpow {α : Type*} [MeasurableSpace α] {ι : Type*} [Fintype ι]
    {μ : MeasureTheory.Measure α} [MeasureTheory.SFinite μ] {w : α → ℝ} (hw0 : ∀ a, 0 ≤ w a)
    (hwm : Measurable w) (hwi : MeasureTheory.Integrable w μ) {p : ℝ} (hp : 2 ≤ p)
    {A : ι → α → ℝ} (hA0 : ∀ i a, 0 ≤ A i a)
    (hAm : ∀ i, MeasureTheory.AEStronglyMeasurable (A i) μ)
    (hint : ∀ i, MeasureTheory.Integrable (fun a => A i a * w a) μ)
    (hint2 : MeasureTheory.Integrable (fun a => (∑ i, (A i a) ^ (2 / p)) ^ (p / 2) * w a) μ) :
    ∫ a, (∑ i, (A i a) ^ (2 / p)) ^ (p / 2) * w a ∂μ
      ≤ (∑ i, (∫ a, A i a * w a ∂μ) ^ (2 / p)) ^ (p / 2) := by
  classical
  have hp0 : (0 : ℝ) < p := by linarith
  have hp2pos : (0 : ℝ) < p / 2 := by linarith
  have hq : (1 : ℝ) ≤ p / 2 := by linarith
  have hexp : (2 / p) * (p / 2) = 1 := by field_simp
  have hu : ∀ i, AEMeasurable (fun a => (A i a) ^ (2 / p)) μ := fun i =>
    ((Real.continuous_rpow_const (by positivity : (0 : ℝ) ≤ 2 / p)).comp_aestronglyMeasurable
      (hAm i)).aemeasurable
  have hu0 : ∀ i a, 0 ≤ (A i a) ^ (2 / p) := fun i a => Real.rpow_nonneg (hA0 i a) _
  have hint' : ∀ i, MeasureTheory.Integrable
      (fun a => ((A i a) ^ (2 / p)) ^ (p / 2) * w a) μ := by
    intro i
    refine (hint i).congr ?_
    filter_upwards with a
    rw [← Real.rpow_mul (hA0 i a) (2 / p) (p / 2), hexp, Real.rpow_one]
  have hmain := integral_sum_rpow_mul_le_sum_integral_rpow_mul (μ := μ) (W := w)
    hwm hw0 hwi hq (u := fun i a => (A i a) ^ (2 / p)) hu hu0 hint' hint2
  have hcongr_i : ∀ i, (∫ a, ((A i a) ^ (2 / p)) ^ (p / 2) * w a ∂μ)
      = ∫ a, A i a * w a ∂μ := by
    intro i
    apply integral_congr_ae
    filter_upwards with a
    rw [← Real.rpow_mul (hA0 i a) (2 / p) (p / 2), hexp, Real.rpow_one]
  have hstep : (∫ a, (∑ i, (A i a) ^ (2 / p)) ^ (p / 2) * w a ∂μ) ^ (2 / p)
      ≤ ∑ i, (∫ a, A i a * w a ∂μ) ^ (2 / p) := by
    have h := hmain
    simp only [one_div_div] at h
    have heq : (∑ i, (∫ a, ((A i a) ^ (2 / p)) ^ (p / 2) * w a ∂μ) ^ (2 / p))
        = ∑ i, (∫ a, A i a * w a ∂μ) ^ (2 / p) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [hcongr_i i]
    exact h.trans (le_of_eq heq)
  have hL_nn : 0 ≤ ∫ a, (∑ i, (A i a) ^ (2 / p)) ^ (p / 2) * w a ∂μ :=
    integral_nonneg (fun a => mul_nonneg
      (Real.rpow_nonneg (Finset.sum_nonneg (fun i _ => hu0 i a)) _) (hw0 a))
  have hfin := Real.rpow_le_rpow (Real.rpow_nonneg hL_nn (2 / p)) hstep (le_of_lt hp2pos)
  rw [← Real.rpow_mul hL_nn (2 / p) (p / 2), hexp, Real.rpow_one] at hfin
  exact hfin

end Commons.Analysis.Integral