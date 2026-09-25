import Mathlib
import Submission.Work.BourgainPlan.Maximal.restricted_defs
import Submission.Work.BourgainPlan.Maximal.foundations

namespace Work.BourgainPlan.Maximal

open Filter Finset Function MeasureTheory
open scoped BigOperators ENNReal Topology

/-- **Weighted power-mean inequality in `ℝ≥0∞`.**  If the weights `w` are sub-probabilistic
(`∑ i ∈ s, w i ≤ 1`), then the `q`-th power of the weighted sum of the `f i` is bounded by the
weighted sum of the `q`-th powers, for every real exponent `q ≥ 1`.  This is the pointwise heart of
the `ℓ^q` contraction of a sub-stochastic averaging operator (Hölder/weighted Jensen). -/
lemma rpow_sum_mul_le_sum_mul_rpow {ι : Type*} (s : Finset ι) (w f : ι → ℝ≥0∞)
    (hw : ∑ i ∈ s, w i ≤ 1) {q : ℝ} (hq : 1 ≤ q) :
    (∑ i ∈ s, w i * f i) ^ q ≤ ∑ i ∈ s, w i * f i ^ q := by
  have hq0 : (0 : ℝ) ≤ q := by linarith
  -- weighted Hölder: `∑ w f ≤ (∑ w)^(1-1/q) * (∑ w f^q)^(1/q)`
  have h1 := ENNReal.inner_le_weight_mul_Lp_of_nonneg (p := q) s hq w f
  have h2 : (∑ i ∈ s, w i * f i) ^ q
      ≤ ((∑ i ∈ s, w i) ^ (1 - q⁻¹) * (∑ i ∈ s, w i * f i ^ q) ^ q⁻¹) ^ q :=
    ENNReal.rpow_le_rpow h1 hq0
  refine le_trans h2 ?_
  rw [ENNReal.mul_rpow_of_nonneg _ _ hq0]
  have e1 : ((∑ i ∈ s, w i) ^ (1 - q⁻¹)) ^ q = (∑ i ∈ s, w i) ^ (q - 1) := by
    rw [← ENNReal.rpow_mul]
    congr 1
    field_simp
  have e2 : ((∑ i ∈ s, w i * f i ^ q) ^ q⁻¹) ^ q = ∑ i ∈ s, w i * f i ^ q := by
    rw [← ENNReal.rpow_mul, show q⁻¹ * q = 1 by field_simp, ENNReal.rpow_one]
  rw [e1, e2]
  calc (∑ i ∈ s, w i) ^ (q - 1) * ∑ i ∈ s, w i * f i ^ q
      ≤ 1 * ∑ i ∈ s, w i * f i ^ q :=
        mul_le_mul' (ENNReal.rpow_le_one hw (by linarith)) le_rfl
    _ = ∑ i ∈ s, w i * f i ^ q := one_mul _

/-- The single-scale absolute polynomial average is an `ℓ^q` contraction: for `1 ≤ q` and any `g`, `∫⁻ (Σ_j k_N(j)·|g(n+j)|)^q ≤ ∫⁻ |g|^q`. Here `absMaxSum P g n N = Σ_j polyKernel P N j * ‖g(n+j)‖ₑ` is the (nonnegative) density average of length `N`; the kernel is sub-probabilistic (`Σ_j polyKernel P N j ≤ 1`, `sum_polyKernel_le_one`). The case `q = 1` is the existing `absMaxSum_lintegral_le`. -/
theorem absMaxSumLpContraction (P : Polynomial ℤ) (N : ℕ) (g : ℕ → ℝ) {q : ℝ} (hq : 1 ≤ q) :
    ∫⁻ n : ℕ, (Work.BourgainPlan.Maximal.absMaxSum P g n N) ^ q ∂MeasureTheory.Measure.count
      ≤ ∫⁻ n : ℕ, ‖g n‖ₑ ^ q ∂MeasureTheory.Measure.count := by
  have hq0 : (0 : ℝ) ≤ q := by linarith
  -- the kernel is sub-probabilistic, also in `ℝ≥0∞`
  have hw1 : ∑ j ∈ Finset.range (Submission.polySupport P N),
      ENNReal.ofReal (Submission.polyKernel P N j) ≤ 1 := by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun j _ => polyKernel_nonneg P N j)]
    simpa using ENNReal.ofReal_le_ofReal (sum_polyKernel_le_one P N)
  -- pointwise power-mean bound
  have hpt : ∀ n : ℕ, (absMaxSum P g n N) ^ q
      ≤ ∑ j ∈ Finset.range (Submission.polySupport P N),
          ENNReal.ofReal (Submission.polyKernel P N j) * ‖g (n + j)‖ₑ ^ q := by
    intro n
    exact rpow_sum_mul_le_sum_mul_rpow _ _ _ hw1 hq
  -- the shift `n ↦ n + j` does not increase the `ℓ^q` mass
  have hshift : ∀ j : ℕ, ∫⁻ n : ℕ, ‖g (n + j)‖ₑ ^ q ∂Measure.count
      ≤ ∫⁻ n : ℕ, ‖g n‖ₑ ^ q ∂Measure.count := by
    intro j
    rw [MeasureTheory.lintegral_count, MeasureTheory.lintegral_count]
    exact ENNReal.tsum_comp_le_tsum_of_injective (f := fun n : ℕ => n + j)
      (fun a _ hab => Nat.add_right_cancel hab) (fun m => ‖g m‖ₑ ^ q)
  calc ∫⁻ n : ℕ, (absMaxSum P g n N) ^ q ∂Measure.count
      ≤ ∫⁻ n : ℕ, (∑ j ∈ Finset.range (Submission.polySupport P N),
            ENNReal.ofReal (Submission.polyKernel P N j) * ‖g (n + j)‖ₑ ^ q)
          ∂Measure.count :=
        lintegral_mono hpt
    _ = ∑ j ∈ Finset.range (Submission.polySupport P N),
          ∫⁻ n : ℕ, ENNReal.ofReal (Submission.polyKernel P N j) * ‖g (n + j)‖ₑ ^ q
            ∂Measure.count := by
        rw [MeasureTheory.lintegral_finsetSum]
        intro j _
        exact measurable_of_countable _
    _ = ∑ j ∈ Finset.range (Submission.polySupport P N),
          ENNReal.ofReal (Submission.polyKernel P N j)
            * ∫⁻ n : ℕ, ‖g (n + j)‖ₑ ^ q ∂Measure.count := by
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [MeasureTheory.lintegral_const_mul]
        exact measurable_of_countable _
    _ ≤ ∑ j ∈ Finset.range (Submission.polySupport P N),
          ENNReal.ofReal (Submission.polyKernel P N j)
            * ∫⁻ n : ℕ, ‖g n‖ₑ ^ q ∂Measure.count :=
        Finset.sum_le_sum fun j _ => mul_le_mul' le_rfl (hshift j)
    _ = (∑ j ∈ Finset.range (Submission.polySupport P N),
          ENNReal.ofReal (Submission.polyKernel P N j))
            * ∫⁻ n : ℕ, ‖g n‖ₑ ^ q ∂Measure.count := by
        rw [Finset.sum_mul]
    _ ≤ 1 * ∫⁻ n : ℕ, ‖g n‖ₑ ^ q ∂Measure.count := mul_le_mul' hw1 le_rfl
    _ = ∫⁻ n : ℕ, ‖g n‖ₑ ^ q ∂Measure.count := one_mul _

end Work.BourgainPlan.Maximal
