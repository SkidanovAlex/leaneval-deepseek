import Mathlib.Probability.Moments.SubGaussian
import Submission.Commons.Probability.Reflection.measure_exists_sum_le_le_two_mul

namespace Commons.Probability.Subgaussian

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

/-- If `μ s ≤ ofReal x` for some `x ≥ 0`, then `μ.real s ≤ x`. -/
private lemma measureReal_le_of_measure_le_ofReal {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {s : Set Ω} {x : ℝ} (hx : 0 ≤ x) (h : μ s ≤ ENNReal.ofReal x) :
    μ.real s ≤ x := by
  have h1 : (μ s).toReal ≤ (ENNReal.ofReal x).toReal := ENNReal.toReal_mono (by simp) h
  rwa [ENNReal.toReal_ofReal hx] at h1

theorem iid_maximal_abs_tail {Ω : Type*} [MeasurableSpace Ω] {μ : MeasureTheory.Measure Ω}
    [MeasureTheory.IsProbabilityMeasure μ] (X : ℕ → Ω → ℝ) (hX : ∀ n, Measurable (X n))
    (hindep : ProbabilityTheory.iIndepFun X μ)
    (hid : ∀ n, ProbabilityTheory.IdentDistrib (X n) (X 0) μ μ)
    (hsym : ProbabilityTheory.IdentDistrib (X 0) (fun ω => -X 0 ω) μ μ)
    {c : NNReal} (hsubG : ProbabilityTheory.HasSubgaussianMGF (X 0) c μ)
    {r : ℝ} (hr : 0 ≤ r) (K : ℕ) :
    μ.real {ω | ∃ k, k ≤ K ∧ r ≤ |∑ i ∈ Finset.range k, X i ω|}
      ≤ 4 * Real.exp (-r ^ 2 / (2 * (K : ℝ) * (c : ℝ))) := by
  classical
  set B : Set Ω := {ω | ∃ k, k ≤ K ∧ r ≤ |∑ i ∈ Finset.range k, X i ω|} with hB
  set Bp : Set Ω := {ω | ∃ k, k ≤ K ∧ r ≤ ∑ i ∈ Finset.range k, X i ω} with hBp
  set Bm : Set Ω := {ω | ∃ k, k ≤ K ∧ ∑ i ∈ Finset.range k, X i ω ≤ -r} with hBm
  set e : ℝ := Real.exp (-r ^ 2 / (2 * (K : ℝ) * (c : ℝ))) with he

  -- the negated sequence
  have hYmeas : ∀ n, Measurable (fun ω => -X n ω) := fun n => (hX n).neg
  have hYindep : iIndepFun (fun n ω => -X n ω) μ :=
    hindep.comp (fun _ x => -x) (fun _ => measurable_neg)
  have hYid : ∀ n, IdentDistrib (fun ω => -X n ω) (fun ω => -X 0 ω) μ μ := by
    intro n
    simpa [Function.comp_def] using (hid n).comp (u := fun x : ℝ => -x) measurable_neg
  have hYsym : IdentDistrib (fun ω => -X 0 ω) (fun ω => -(-X 0 ω)) μ μ := by
    simpa only [neg_neg] using hsym.symm
  -- sub-gaussianity of all the variables
  have hXsub : ∀ i < K, HasSubgaussianMGF (X i) c μ :=
    fun i _ => hsubG.congr_identDistrib (hid i).symm
  have hYsub : ∀ i < K, HasSubgaussianMGF (fun ω => -X i ω) c μ :=
    fun i hi => (hXsub i hi).neg
  -- one-sided Hoeffding bounds
  have hHoeffX : μ.real {ω | r ≤ ∑ i ∈ Finset.range K, X i ω} ≤ e := by
    exact ProbabilityTheory.HasSubgaussianMGF.measure_sum_range_ge_le_of_iIndepFun
      (μ := μ) hindep hXsub hr
  have hHoeffY : μ.real {ω | r ≤ ∑ i ∈ Finset.range K, -X i ω} ≤ e := by
    exact ProbabilityTheory.HasSubgaussianMGF.measure_sum_range_ge_le_of_iIndepFun
      (μ := μ) hYindep hYsub hr
  have hTp_enn : μ {ω | r ≤ ∑ i ∈ Finset.range K, X i ω} ≤ ENNReal.ofReal e := by
    rw [← ofReal_measureReal (μ := μ) (s := {ω | r ≤ ∑ i ∈ Finset.range K, X i ω})]
    exact ENNReal.ofReal_le_ofReal hHoeffX
  have hTm_enn : μ {ω | r ≤ ∑ i ∈ Finset.range K, -X i ω} ≤ ENNReal.ofReal e := by
    rw [← ofReal_measureReal (μ := μ) (s := {ω | r ≤ ∑ i ∈ Finset.range K, -X i ω})]
    exact ENNReal.ofReal_le_ofReal hHoeffY
  -- reflection on the negated sequence bounds the `≥` part
  have hset1 : {ω | ∃ k, k ≤ K ∧ (∑ i ∈ Finset.range k, -X i ω) ≤ -r} = Bp := by
    rw [hBp]; ext ω; constructor
    · rintro ⟨k, hk, hk'⟩
      refine ⟨k, hk, ?_⟩
      rw [Finset.sum_neg_distrib] at hk'; linarith
    · rintro ⟨k, hk, hk'⟩
      refine ⟨k, hk, ?_⟩
      rw [Finset.sum_neg_distrib]; linarith
  have hset2 : {ω | (∑ i ∈ Finset.range K, -X i ω) ≤ -r}
      = {ω | r ≤ ∑ i ∈ Finset.range K, X i ω} := by
    apply Set.ext; intro ω
    change ((∑ i ∈ Finset.range K, -X i ω) ≤ -r) ↔ (r ≤ ∑ i ∈ Finset.range K, X i ω)
    rw [Finset.sum_neg_distrib]; constructor <;> intro h <;> linarith
  have hreflY' : μ Bp ≤ 2 * μ {ω | r ≤ ∑ i ∈ Finset.range K, X i ω} := by
    have h := Commons.Probability.Reflection.measure_exists_sum_le_le_two_mul
      (fun n ω => -X n ω) hYmeas hYindep hYid hYsym (a := r) hr K
    simpa only [hset1, hset2] using h
  have hBp_le : μ.real Bp ≤ 2 * e := by
    have h2 : μ Bp ≤ ENNReal.ofReal (2 * e) := by
      calc μ Bp ≤ 2 * μ {ω | r ≤ ∑ i ∈ Finset.range K, X i ω} := hreflY'
        _ ≤ 2 * ENNReal.ofReal e := by gcongr
        _ = ENNReal.ofReal (2 * e) := by
              rw [show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by norm_num,
                ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
    exact measureReal_le_of_measure_le_ofReal (by positivity) h2
  -- reflection on the original sequence bounds the `≤ -r` part
  have hset3 : {ω | (∑ i ∈ Finset.range K, X i ω) ≤ -r}
      = {ω | r ≤ ∑ i ∈ Finset.range K, -X i ω} := by
    apply Set.ext; intro ω
    change ((∑ i ∈ Finset.range K, X i ω) ≤ -r) ↔ (r ≤ ∑ i ∈ Finset.range K, -X i ω)
    rw [Finset.sum_neg_distrib]; constructor <;> intro h <;> linarith
  have hreflX' : μ Bm ≤ 2 * μ {ω | r ≤ ∑ i ∈ Finset.range K, -X i ω} := by
    have h := Commons.Probability.Reflection.measure_exists_sum_le_le_two_mul
      X hX hindep hid hsym (a := r) hr K
    simpa only [← hBm, hset3] using h
  have hBm_le : μ.real Bm ≤ 2 * e := by
    have h2 : μ Bm ≤ ENNReal.ofReal (2 * e) := by
      calc μ Bm ≤ 2 * μ {ω | r ≤ ∑ i ∈ Finset.range K, -X i ω} := hreflX'
        _ ≤ 2 * ENNReal.ofReal e := by gcongr
        _ = ENNReal.ofReal (2 * e) := by
              rw [show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by norm_num,
                ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
    exact measureReal_le_of_measure_le_ofReal (by positivity) h2
  -- put the two parts together
  have hBsub : B ⊆ Bp ∪ Bm := by
    intro ω hω
    rw [hB] at hω
    obtain ⟨k, hk, hk'⟩ := hω
    by_cases hpos : 0 ≤ ∑ i ∈ Finset.range k, X i ω
    · left; rw [hBp]; exact ⟨k, hk, by rwa [abs_of_nonneg hpos] at hk'⟩
    · right
      have hneg : (∑ i ∈ Finset.range k, X i ω) < 0 := not_le.mp hpos
      rw [hBm]; exact ⟨k, hk, by rw [abs_of_neg hneg] at hk'; linarith⟩
  calc μ.real B ≤ μ.real (Bp ∪ Bm) := measureReal_mono hBsub
    _ ≤ μ.real Bp + μ.real Bm := measureReal_union_le _ _
    _ ≤ 2 * e + 2 * e := add_le_add hBp_le hBm_le
    _ = 4 * e := by ring

end Commons.Probability.Subgaussian