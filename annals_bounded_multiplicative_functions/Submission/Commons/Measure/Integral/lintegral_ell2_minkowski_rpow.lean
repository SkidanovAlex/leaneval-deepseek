import Mathlib.MeasureTheory.Integral.MeanInequalities

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Commons.Measure.Integral

open MeasureTheory
open scoped BigOperators ENNReal

/-- **Minkowski's inequality for the `ℝ≥0∞`-valued Lebesgue integral**, finite-sum form:
for `1 ≤ r` and nonnegative measurable functions `F i`,
`(∫⁻ (∑ i ∈ s, F i x) ^ r) ^ (1/r) ≤ ∑ i ∈ s, (∫⁻ (F i x) ^ r) ^ (1/r)`.
It is proved by induction on the finite set from the two-term Minkowski inequality
`ENNReal.lintegral_Lp_add_le`. -/
theorem lintegral_finset_sum_rpow_le {α : Type*} [MeasurableSpace α] (μ : Measure α)
    {ι : Type*} {r : ℝ} (hr : 1 ≤ r) (s : Finset ι) {F : ι → α → ENNReal}
    (hF : ∀ i, AEMeasurable (F i) μ) :
    (∫⁻ x, (∑ i ∈ s, F i x) ^ r ∂μ) ^ (1 / r)
      ≤ ∑ i ∈ s, (∫⁻ x, (F i x) ^ r ∂μ) ^ (1 / r) := by
  classical
  have hr0 : 0 < r := by linarith
  induction s using Finset.induction with
  | empty =>
      have h0 : (0 : ENNReal) ^ r = 0 := ENNReal.zero_rpow_of_pos hr0
      simp only [Finset.sum_empty, h0, lintegral_zero]
      exact le_of_eq (ENNReal.zero_rpow_of_pos (by positivity))
  | insert a s ha ih =>
      have hFa : AEMeasurable (F a) μ := hF a
      have hFs : ∀ i ∈ s, AEMeasurable (F i) μ := fun i _ => hF i
      have hG : AEMeasurable (fun x => ∑ i ∈ s, F i x) μ := by
        have h := Finset.aemeasurable_sum s hFs
        rwa [Finset.sum_fn] at h
      have hkey := ENNReal.lintegral_Lp_add_le (f := F a) (g := fun x => ∑ i ∈ s, F i x) hFa hG hr
      have hcongr : (∫⁻ x, (∑ i ∈ insert a s, F i x) ^ r ∂μ)
          = (∫⁻ x, (F a x + ∑ i ∈ s, F i x) ^ r ∂μ) := by
        apply lintegral_congr
        intro x
        rw [Finset.sum_insert ha]
      rw [hcongr, Finset.sum_insert ha]
      exact hkey.trans (add_le_add le_rfl ih)

/-- **Minkowski's inequality for the `ℝ≥0∞`-valued Lebesgue integral**, `Fintype` form. -/
theorem lintegral_sum_rpow_le {α : Type*} [MeasurableSpace α] (μ : Measure α)
    {ι : Type*} [Fintype ι] {r : ℝ} (hr : 1 ≤ r) {F : ι → α → ENNReal}
    (hF : ∀ i, AEMeasurable (F i) μ) :
    (∫⁻ x, (∑ i, F i x) ^ r ∂μ) ^ (1 / r)
      ≤ ∑ i, (∫⁻ x, (F i x) ^ r ∂μ) ^ (1 / r) := by
  have h := lintegral_finset_sum_rpow_le μ hr Finset.univ (F := F) hF
  simpa using h

/-- **Minkowski's inequality for the `ℓ²`-norm of an `L^p` function (`2 ≤ p`), `ℝ≥0∞` form.**
For nonnegative measurable functions `f i` and `2 ≤ p`,
`‖(∑ i, f i ²)^{1/2}‖_{L^p} ≤ ‖(‖f i‖_{L^p})_i‖_{ℓ²}`. -/
theorem lintegral_ell2_minkowski_rpow {α : Type*} [MeasurableSpace α] (μ : MeasureTheory.Measure α)
    {ι : Type*} [Fintype ι] {p : ℝ} (hp : 2 ≤ p) (f : ι → α → ENNReal)
    (hf : ∀ i, AEMeasurable (f i) μ) :
    (MeasureTheory.lintegral μ (fun x => (∑ i, (f i x) ^ (2 : ℝ)) ^ (p / 2))) ^ (1 / p)
      ≤ (∑ i, (MeasureTheory.lintegral μ (fun x => (f i x) ^ p)) ^ (2 / p)) ^ ((1 : ℝ) / 2) := by
  have hp_half : 1 ≤ p / 2 := by linarith
  have hFmeas : ∀ i, AEMeasurable (fun x => (f i x) ^ (2 : ℝ)) μ := fun i => (hf i).pow_const _
  have hcore := lintegral_sum_rpow_le μ (r := p / 2) hp_half
    (F := fun i x => (f i x) ^ (2 : ℝ)) hFmeas
  have hL : (∫⁻ x, (∑ i, (f i x) ^ (2 : ℝ)) ^ (p / 2) ∂μ) ^ (1 / (p / 2))
      = (∫⁻ x, (∑ i, (f i x) ^ (2 : ℝ)) ^ (p / 2) ∂μ) ^ (2 / p) := by
    congr 1; ring
  have hR : (∑ i, (∫⁻ x, ((f i x) ^ (2 : ℝ)) ^ (p / 2) ∂μ) ^ (1 / (p / 2)))
      = ∑ i, (∫⁻ x, (f i x) ^ p ∂μ) ^ (2 / p) := by
    apply Finset.sum_congr rfl
    intro i _
    rw [show (1 : ℝ) / (p / 2) = 2 / p by ring]
    congr 1
    apply lintegral_congr
    intro x
    rw [← ENNReal.rpow_mul]
    congr 1
    ring
  have hcore2 : (∫⁻ x, (∑ i, (f i x) ^ (2 : ℝ)) ^ (p / 2) ∂μ) ^ (2 / p)
      ≤ ∑ i, (∫⁻ x, (f i x) ^ p ∂μ) ^ (2 / p) := by
    rw [hL, hR] at hcore
    exact hcore
  calc (∫⁻ x, (∑ i, (f i x) ^ (2 : ℝ)) ^ (p / 2) ∂μ) ^ (1 / p)
      = ((∫⁻ x, (∑ i, (f i x) ^ (2 : ℝ)) ^ (p / 2) ∂μ) ^ (2 / p)) ^ (1 / 2) := by
        rw [← ENNReal.rpow_mul]; congr 1; ring
    _ ≤ (∑ i, (∫⁻ x, (f i x) ^ p ∂μ) ^ (2 / p)) ^ (1 / 2) :=
        ENNReal.rpow_le_rpow hcore2 (by norm_num)

end Commons.Measure.Integral