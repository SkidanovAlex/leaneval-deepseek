import Mathlib.Probability.Moments.SubGaussian

namespace Commons.Probability.Hoeffding

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

/-- Monotonicity of the sub-Gaussian parameter: a sub-Gaussian random variable with parameter
`c` is also sub-Gaussian with any larger parameter `c'`. -/
lemma hasSubgaussianMGF_mono {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {X : Ω → ℝ}
    {c c' : ℝ≥0} (h : HasSubgaussianMGF X c μ) (hcc : c ≤ c') :
    HasSubgaussianMGF X c' μ := by
  refine ⟨h.integrable_exp_mul, fun t => (h.mgf_le t).trans ?_⟩
  rw [Real.exp_le_exp]
  have h1 : (c : ℝ) ≤ (c' : ℝ) := by exact_mod_cast hcc
  have ht : (0 : ℝ) ≤ t ^ 2 / 2 := by positivity
  calc c * t ^ 2 / 2 = (c : ℝ) * (t ^ 2 / 2) := by ring
    _ ≤ (c' : ℝ) * (t ^ 2 / 2) := mul_le_mul_of_nonneg_right h1 ht
    _ = c' * t ^ 2 / 2 := by ring

/-- The sum of the squared weights `w i` equals the (coerced) sum of the squared nonnegative
norms `‖w i‖₊`; used to identify the exponents in the two forms of the Hoeffding bound. -/
private lemma coe_sum_sq_nnnorm {ι : Type*} [Fintype ι] (w : ι → ℝ) :
    ((∑ i, ‖w i‖₊ ^ 2 : ℝ≥0) : ℝ) = ∑ i, w i ^ 2 := by
  rw [NNReal.coe_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [NNReal.coe_pow, ← sq_abs (w i)]
  norm_cast

/-- One-sided Hoeffding bound in `μ.real` form for a sum of independent centred sub-Gaussian
random variables, with parameters `‖w i‖₊ ^ 2`. -/
private lemma sum_tail_le {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] {ι : Type*} [Fintype ι] (Y : ι → Ω → ℝ) (w : ι → ℝ)
    (hindep : iIndepFun Y μ) (hsubg : ∀ i, HasSubgaussianMGF (Y i) (‖w i‖₊ ^ 2) μ)
    {ε : ℝ} (hε : 0 ≤ ε) :
    μ.real {ω | ε ≤ ∑ i, Y i ω} ≤ Real.exp (-(ε ^ 2) / (2 * ∑ i, w i ^ 2)) := by
  have h := HasSubgaussianMGF.measure_sum_ge_le_of_iIndepFun hindep
    (s := Finset.univ) (c := fun i => ‖w i‖₊ ^ 2) (fun i _ => hsubg i) hε
  rwa [coe_sum_sq_nnnorm] at h

/-- Hoeffding/Chernoff inequality for a sum of independent bounded real random variables: if
`0 ≤ X i ≤ w i` almost surely and the `X i` are independent, then the probability that the sum
`∑ i, X i` deviates from its mean by at least `ε` is at most `2 * exp(-ε²/(2 * ∑ i, w i²))`.
This is the weighted Chernoff bound (Thm 4.1 of Kang-Kelly-Kuhn-Methuku-Osthus, "A proof of the
Erdos-Faber-Lovasz conjecture", Annals of Math. 198 (2) 2023) in its standard Hoeffding form; the
bound is the (weaker) two-sided Hoeffding bound, which follows from Hoeffding's inequality for
`X i ∈ [0, w i]`.

It should follow from `ProbabilityTheory.measure_sum_ge_le_of_iIndepFun` together with Hoeffding's
inequality `ProbabilityTheory.hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero` in
`Mathlib.Probability.Moments.SubGaussian`, applied to the centred variables `X i - ∫ X i`.  A
one-sided version, and versions phrased with `μ.real`, would also be welcome as separate results in
the same file.  Please use minimal imports (this file may be imported by a development in which the
unqualified identifier `Hypergraph` must keep resolving to a local abbreviation, so do not
`import Mathlib`). -/
theorem chernoff_weighted {Ω : Type*} [MeasurableSpace Ω] (μ : MeasureTheory.Measure Ω)
    [MeasureTheory.IsProbabilityMeasure μ]
    {ι : Type*} [Fintype ι] (X : ι → Ω → ℝ) (w : ι → ℝ)
    (hmeas : ∀ i, Measurable (X i)) (hindep : ProbabilityTheory.iIndepFun X μ)
    (hbound : ∀ i, ∀ᵐ ω ∂μ, 0 ≤ X i ω ∧ X i ω ≤ w i) (hw : ∀ i, 0 ≤ w i)
    (ε : ℝ) (hε : 0 ≤ ε) :
    μ {ω | ε ≤ |∑ i, X i ω - ∑ i, MeasureTheory.integral μ (fun ω => X i ω)|}
      ≤ ENNReal.ofReal (2 * Real.exp (-(ε ^ 2) / (2 * ∑ i, w i ^ 2))) := by
  classical
  -- the centred variables `X i - E[X i]`
  have hindep_cent : iIndepFun (fun i ω => X i ω - ∫ x, X i x ∂μ) μ :=
    hindep.comp (fun i x => x - ∫ y, X i y ∂μ) (fun i => measurable_id.sub_const _)
  have hsubg (i : ι) : HasSubgaussianMGF (fun ω => X i ω - ∫ x, X i x ∂μ) (‖w i‖₊ ^ 2) μ := by
    have hb : ∀ᵐ ω ∂μ, X i ω ∈ Set.Icc (0 : ℝ) (w i) := by
      filter_upwards [hbound i] with ω hω using hω
    have h := hasSubgaussianMGF_of_mem_Icc (X := X i) (a := 0) (b := w i)
      (hmeas i).aemeasurable hb
    have hp : ((‖w i - 0‖₊ / 2) ^ 2 : ℝ≥0) ≤ ‖w i‖₊ ^ 2 := by
      rw [sub_zero, ← NNReal.coe_le_coe]
      push_cast
      nlinarith [NNReal.coe_nonneg (‖w i‖₊)]
    exact hasSubgaussianMGF_mono h hp
  -- the reflected centred variables `E[X i] - X i`
  have hsubg_neg (i : ι) :
      HasSubgaussianMGF (fun ω => ∫ x, X i x ∂μ - X i ω) (‖w i‖₊ ^ 2) μ := by
    refine (hsubg i).neg.congr ?_
    filter_upwards with ω
    simp [neg_sub]
  have hindep_neg : iIndepFun (fun i ω => ∫ x, X i x ∂μ - X i ω) μ := by
    have h : iIndepFun (fun i ω => -(X i ω - ∫ x, X i x ∂μ)) μ :=
      hindep_cent.comp (fun _ x => -x) (fun _ => measurable_neg)
    simpa only [neg_sub] using h
  -- the two one-sided bounds
  have hpos : μ.real {ω | ε ≤ ∑ i, X i ω - ∑ i, ∫ x, X i x ∂μ}
      ≤ Real.exp (-(ε ^ 2) / (2 * ∑ i, w i ^ 2)) := by
    have h := sum_tail_le μ (fun i ω => X i ω - ∫ x, X i x ∂μ) w hindep_cent hsubg hε
    have hset : {ω : Ω | ε ≤ ∑ i, (X i ω - ∫ x, X i x ∂μ)}
        = {ω | ε ≤ ∑ i, X i ω - ∑ i, ∫ x, X i x ∂μ} := by
      ext ω
      simp only [Set.mem_setOf_eq, Finset.sum_sub_distrib]
    rw [hset] at h
    exact h
  have hneg : μ.real {ω | ε ≤ -(∑ i, X i ω - ∑ i, ∫ x, X i x ∂μ)}
      ≤ Real.exp (-(ε ^ 2) / (2 * ∑ i, w i ^ 2)) := by
    have h := sum_tail_le μ (fun i ω => ∫ x, X i x ∂μ - X i ω) w hindep_neg hsubg_neg hε
    have hsum (ω : Ω) :
        (∑ i, (∫ x, X i x ∂μ - X i ω)) = -(∑ i, X i ω - ∑ i, ∫ x, X i x ∂μ) := by
      rw [Finset.sum_sub_distrib]
      ring
    have hset : {ω : Ω | ε ≤ ∑ i, (∫ x, X i x ∂μ - X i ω)}
        = {ω | ε ≤ -(∑ i, X i ω - ∑ i, ∫ x, X i x ∂μ)} := by
      ext ω
      simp only [Set.mem_setOf_eq]
      rw [hsum ω]
    rw [hset] at h
    exact h
  -- combine the two tails
  have hfin (s : Set Ω) : μ s = ENNReal.ofReal (μ.real s) := by
    rw [Measure.real_def]
    exact (ENNReal.ofReal_toReal (measure_ne_top μ s)).symm
  have hsub : {ω | ε ≤ |∑ i, X i ω - ∑ i, ∫ x, X i x ∂μ|}
      ⊆ {ω | ε ≤ ∑ i, X i ω - ∑ i, ∫ x, X i x ∂μ}
        ∪ {ω | ε ≤ -(∑ i, X i ω - ∑ i, ∫ x, X i x ∂μ)} := by
    intro ω hω
    simp only [Set.mem_setOf_eq] at hω ⊢
    rcases le_abs.mp hω with h | h
    · exact Or.inl h
    · exact Or.inr h
  calc μ {ω | ε ≤ |∑ i, X i ω - ∑ i, ∫ x, X i x ∂μ|}
      ≤ μ ({ω | ε ≤ ∑ i, X i ω - ∑ i, ∫ x, X i x ∂μ}
          ∪ {ω | ε ≤ -(∑ i, X i ω - ∑ i, ∫ x, X i x ∂μ)}) := measure_mono hsub
    _ ≤ μ {ω | ε ≤ ∑ i, X i ω - ∑ i, ∫ x, X i x ∂μ}
          + μ {ω | ε ≤ -(∑ i, X i ω - ∑ i, ∫ x, X i x ∂μ)} := measure_union_le _ _
    _ = ENNReal.ofReal (μ.real {ω | ε ≤ ∑ i, X i ω - ∑ i, ∫ x, X i x ∂μ})
          + ENNReal.ofReal (μ.real {ω | ε ≤ -(∑ i, X i ω - ∑ i, ∫ x, X i x ∂μ)}) := by
        rw [hfin, hfin]
    _ ≤ ENNReal.ofReal (Real.exp (-(ε ^ 2) / (2 * ∑ i, w i ^ 2)))
          + ENNReal.ofReal (Real.exp (-(ε ^ 2) / (2 * ∑ i, w i ^ 2))) :=
        add_le_add (ENNReal.ofReal_le_ofReal hpos) (ENNReal.ofReal_le_ofReal hneg)
    _ = ENNReal.ofReal (2 * Real.exp (-(ε ^ 2) / (2 * ∑ i, w i ^ 2))) := by
        rw [← ENNReal.ofReal_add (Real.exp_pos _).le (Real.exp_pos _).le]
        congr 1
        ring

/-- One-sided (upper tail) form of the weighted Chernoff/Hoeffding bound: under the same
hypotheses as `chernoff_weighted`, the probability that `∑ i, X i` exceeds its mean by at least
`ε` is at most `exp(-ε²/(2 * ∑ i, w i²))`. -/
theorem chernoff_weighted_ge {Ω : Type*} [MeasurableSpace Ω] (μ : MeasureTheory.Measure Ω)
    [MeasureTheory.IsProbabilityMeasure μ]
    {ι : Type*} [Fintype ι] (X : ι → Ω → ℝ) (w : ι → ℝ)
    (hmeas : ∀ i, Measurable (X i)) (hindep : ProbabilityTheory.iIndepFun X μ)
    (hbound : ∀ i, ∀ᵐ ω ∂μ, 0 ≤ X i ω ∧ X i ω ≤ w i) (hw : ∀ i, 0 ≤ w i)
    (ε : ℝ) (hε : 0 ≤ ε) :
    μ {ω | ε ≤ ∑ i, X i ω - ∑ i, MeasureTheory.integral μ (fun ω => X i ω)}
      ≤ ENNReal.ofReal (Real.exp (-(ε ^ 2) / (2 * ∑ i, w i ^ 2))) := by
  have hindep_cent : iIndepFun (fun i ω => X i ω - ∫ x, X i x ∂μ) μ :=
    hindep.comp (fun i x => x - ∫ y, X i y ∂μ) (fun i => measurable_id.sub_const _)
  have hsubg (i : ι) : HasSubgaussianMGF (fun ω => X i ω - ∫ x, X i x ∂μ) (‖w i‖₊ ^ 2) μ := by
    have hb : ∀ᵐ ω ∂μ, X i ω ∈ Set.Icc (0 : ℝ) (w i) := by
      filter_upwards [hbound i] with ω hω using hω
    have h := hasSubgaussianMGF_of_mem_Icc (X := X i) (a := 0) (b := w i)
      (hmeas i).aemeasurable hb
    have hp : ((‖w i - 0‖₊ / 2) ^ 2 : ℝ≥0) ≤ ‖w i‖₊ ^ 2 := by
      rw [sub_zero, ← NNReal.coe_le_coe]
      push_cast
      nlinarith [NNReal.coe_nonneg (‖w i‖₊)]
    exact hasSubgaussianMGF_mono h hp
  have h := sum_tail_le μ (fun i ω => X i ω - ∫ x, X i x ∂μ) w hindep_cent hsubg hε
  have hset : {ω : Ω | ε ≤ ∑ i, (X i ω - ∫ x, X i x ∂μ)}
      = {ω | ε ≤ ∑ i, X i ω - ∑ i, ∫ x, X i x ∂μ} := by
    ext ω
    simp only [Set.mem_setOf_eq, Finset.sum_sub_distrib]
  rw [hset] at h
  rw [← ENNReal.ofReal_toReal (measure_ne_top μ _)]
  exact ENNReal.ofReal_le_ofReal h

/-- The weighted Chernoff/Hoeffding bound phrased with `μ.real`. -/
theorem chernoff_weighted_real {Ω : Type*} [MeasurableSpace Ω] (μ : MeasureTheory.Measure Ω)
    [MeasureTheory.IsProbabilityMeasure μ]
    {ι : Type*} [Fintype ι] (X : ι → Ω → ℝ) (w : ι → ℝ)
    (hmeas : ∀ i, Measurable (X i)) (hindep : ProbabilityTheory.iIndepFun X μ)
    (hbound : ∀ i, ∀ᵐ ω ∂μ, 0 ≤ X i ω ∧ X i ω ≤ w i) (hw : ∀ i, 0 ≤ w i)
    (ε : ℝ) (hε : 0 ≤ ε) :
    μ.real {ω | ε ≤ |∑ i, X i ω - ∑ i, MeasureTheory.integral μ (fun ω => X i ω)|}
      ≤ 2 * Real.exp (-(ε ^ 2) / (2 * ∑ i, w i ^ 2)) := by
  have h := chernoff_weighted μ X w hmeas hindep hbound hw ε hε
  calc μ.real {ω | ε ≤ |∑ i, X i ω - ∑ i, MeasureTheory.integral μ (fun ω => X i ω)|}
      = (μ {ω | ε ≤ |∑ i, X i ω - ∑ i, MeasureTheory.integral μ (fun ω => X i ω)|}).toReal :=
        rfl
    _ ≤ (ENNReal.ofReal (2 * Real.exp (-(ε ^ 2) / (2 * ∑ i, w i ^ 2)))).toReal :=
        ENNReal.toReal_mono ENNReal.ofReal_ne_top h
    _ = 2 * Real.exp (-(ε ^ 2) / (2 * ∑ i, w i ^ 2)) :=
        ENNReal.toReal_ofReal (by positivity)

end Commons.Probability.Hoeffding
