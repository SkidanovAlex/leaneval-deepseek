import Mathlib.MeasureTheory.Integral.MeanInequalities

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Commons.Measure.Integral

open MeasureTheory

/-- Minkowski's inequality for `ENNReal`-valued functions, finite-sum form: for `r ≥ 1`, the
`ℒ^r` seminorm of a finite sum is bounded by the sum of the `ℒ^r` seminorms. -/
lemma lintegral_Lp_finset_sum_le {α : Type*} [MeasurableSpace α] (μ : MeasureTheory.Measure α)
    {ι : Type*} (s : Finset ι) {r : ℝ} (hr : 1 ≤ r) (g : ι → α → ENNReal)
    (hg : ∀ i, AEMeasurable (g i) μ) :
    (∫⁻ x, (∑ i ∈ s, g i x) ^ r ∂μ) ^ (1 / r) ≤
      ∑ i ∈ s, (∫⁻ x, (g i x) ^ r ∂μ) ^ (1 / r) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      have hr0 : (0:ℝ) < r := by linarith
      have hr1 : (0:ℝ) < 1 / r := by positivity
      simp only [Finset.sum_empty, ENNReal.zero_rpow_of_pos hr0, lintegral_zero,
        ENNReal.zero_rpow_of_pos hr1, le_refl]
  | insert a s ha ih =>
      have hmeas_sum : AEMeasurable (fun x => ∑ i ∈ s, g i x) μ := by
        convert Finset.aemeasurable_sum (f := g) s (fun i _ => hg i) using 1
        ext x
        simp [Finset.sum_apply]
      have hkey : (∫⁻ x, (g a x + ∑ i ∈ s, g i x) ^ r ∂μ) ^ (1 / r) ≤
          (∫⁻ x, (g a x) ^ r ∂μ) ^ (1 / r) +
            ∑ i ∈ s, (∫⁻ x, (g i x) ^ r ∂μ) ^ (1 / r) := by
        calc
          (∫⁻ x, (g a x + ∑ i ∈ s, g i x) ^ r ∂μ) ^ (1 / r)
              ≤ (∫⁻ x, (g a x) ^ r ∂μ) ^ (1 / r) +
                  (∫⁻ x, (∑ i ∈ s, g i x) ^ r ∂μ) ^ (1 / r) :=
                ENNReal.lintegral_Lp_add_le (f := g a)
                  (g := fun x => ∑ i ∈ s, g i x) (hg a) hmeas_sum hr
          _ ≤ (∫⁻ x, (g a x) ^ r ∂μ) ^ (1 / r) +
                  ∑ i ∈ s, (∫⁻ x, (g i x) ^ r ∂μ) ^ (1 / r) :=
                add_le_add_right ih _
      convert hkey using 1
      · simp only [Finset.sum_insert ha]
      · simp only [Finset.sum_insert ha]

theorem lintegral_ell2_minkowski_rpow_finset {α : Type*} [MeasurableSpace α] (μ : MeasureTheory.Measure α) {ι : Type*} (s : Finset ι) {p : ℝ} (hp : 2 ≤ p) (f : ι → α → ENNReal) (hf : ∀ i, AEMeasurable (f i) μ) : (MeasureTheory.lintegral μ (fun x => (∑ i ∈ s, (f i x) ^ (2:ℝ)) ^ (p / 2))) ^ (1 / p) ≤ (∑ i ∈ s, (MeasureTheory.lintegral μ (fun x => (f i x) ^ p)) ^ (2 / p)) ^ ((1:ℝ) / 2) := by
  have hp1 : (1:ℝ) ≤ p / 2 := by linarith
  have hp0 : p ≠ 0 := by linarith
  have hint : ∀ (i : ι) (x : α), ((f i x) ^ (2:ℝ)) ^ (p / 2) = (f i x) ^ p := by
    intro i x
    rw [← ENNReal.rpow_mul]
    rw [show (2:ℝ) * (p / 2) = p by ring]
  have hmeas : ∀ i, AEMeasurable (fun x => (f i x) ^ (2:ℝ)) μ :=
    fun i => (hf i).pow_const 2
  have key : (∫⁻ x, (∑ i ∈ s, (f i x) ^ (2:ℝ)) ^ (p / 2) ∂μ) ^ (1 / (p / 2)) ≤
      ∑ i ∈ s, (∫⁻ x, (f i x) ^ p ∂μ) ^ (1 / (p / 2)) := by
    have h := lintegral_Lp_finset_sum_le (r := p / 2) μ s hp1 (fun i x => (f i x) ^ (2:ℝ)) hmeas
    simp only [hint] at h
    exact h
  have h1 : (∫⁻ x, (∑ i ∈ s, (f i x) ^ (2:ℝ)) ^ (p / 2) ∂μ) ^ (1 / p) =
      ((∫⁻ x, (∑ i ∈ s, (f i x) ^ (2:ℝ)) ^ (p / 2) ∂μ) ^ (1 / (p / 2))) ^ (1 / 2 : ℝ) := by
    rw [← ENNReal.rpow_mul]
    congr 1
    field_simp
  have h2 : (∑ i ∈ s, (∫⁻ x, (f i x) ^ p ∂μ) ^ (1 / (p / 2))) =
      ∑ i ∈ s, (∫⁻ x, (f i x) ^ p ∂μ) ^ (2 / p) := by
    apply Finset.sum_congr rfl
    intro i _
    congr 1
    field_simp
  calc
    (∫⁻ x, (∑ i ∈ s, (f i x) ^ (2:ℝ)) ^ (p / 2) ∂μ) ^ (1 / p)
        = ((∫⁻ x, (∑ i ∈ s, (f i x) ^ (2:ℝ)) ^ (p / 2) ∂μ) ^ (1 / (p / 2))) ^ (1 / 2 : ℝ) :=
          h1
    _ ≤ ((∑ i ∈ s, (∫⁻ x, (f i x) ^ p ∂μ) ^ (1 / (p / 2))) ^ (1 / 2 : ℝ)) :=
          ENNReal.rpow_le_rpow key (by norm_num)
    _ = ((∑ i ∈ s, (∫⁻ x, (f i x) ^ p ∂μ) ^ (2 / p)) ^ (1 / 2 : ℝ)) := by rw [h2]

end Commons.Measure.Integral