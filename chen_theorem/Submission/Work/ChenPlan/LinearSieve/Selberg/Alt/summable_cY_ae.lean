import Mathlib
import Submission.Work.ChenPlan.LinearSieve.Selberg.Alt.refsum_law
import Submission.Work.ChenPlan.LinearSieve.Selberg.Alt.ExpLaw

/-!
# Almost-sure summability of `Σ_k e^{-S_k}` under the canonical exponential law

Let `canonM = ⊗_{n ∈ ℕ} Exp(1)` on `ℝ^ℕ` and `cSum x k = x 0 + ⋯ + x (k-1)`.  We prove that
`Σ_{k ∈ ℕ} e^{-cSum x k}` converges for almost every `x`.

The strategy is a single application of the strong law of large numbers to the *bounded*
random variables `1[x i > 1]` (`i ∈ ℕ`): they are independent and identically distributed
under `canonM`, their mean is `e^{-1} > 0`, hence almost surely the number of `i < k` with
`x i > 1` grows like `k/e`.  Since the coordinates are almost surely non-negative, this
bounds `cSum x k` from below by a positive multiple of `k`, so `e^{-cSum x k}` is dominated
by a geometric series.

The main auxiliary facts are `hasExpLaw_expLaw` (the standard exponential law, used to
compute `expLaw (Ioi 1) = e^{-1}` and `expLaw (Iio 0) = 0`) and `ae_coord_nonneg`.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal Topology

namespace Work.ChenPlan.LinearSieve.Selberg.Alt

noncomputable section

/-! ### The standard exponential law on `expLaw` -/

lemma hasExpLaw_expLaw : HasExpLaw expLaw := by
  intro x
  rw [← ProbabilityTheory.ofReal_cdf (μ := expLaw) x]
  rw [expLaw, ProbabilityTheory.cdf_expMeasure_eq one_pos x]
  by_cases hx : 0 ≤ x
  · rw [if_pos hx]
    congr 1
    ring_nf
  · rw [if_neg hx]
    have h : (1 : ℝ) - Real.exp (-x) ≤ 0 := by
      have h1 : (0 : ℝ) ≤ -x := by linarith
      have h2 : 1 ≤ Real.exp (-x) := Real.one_le_exp_iff.mpr h1
      linarith
    exact ENNReal.ofReal_zero.trans (ENNReal.ofReal_of_nonpos h).symm

lemma expLaw_Iio_zero : expLaw (Set.Iio 0) = 0 :=
  measure_mono_null Set.Iio_subset_Iic_self (by
    rw [hasExpLaw_expLaw 0]; simp)

/-- Almost surely, every coordinate of the canonical exponential product is non-negative. -/
lemma ae_coord_nonneg : ∀ᵐ x ∂canonM, ∀ i : ℕ, 0 ≤ x i := by
  rw [ae_all_iff]
  intro i
  rw [ae_iff]
  have hmap : canonM.map (fun x : ℕ → ℝ => x i) = expLaw := by
    rw [canonM]
    exact Measure.infinitePi_map_eval (fun _ : ℕ => expLaw) i
  have h : canonM ((fun x : ℕ → ℝ => x i) ⁻¹' Set.Iio 0) = 0 := by
    rw [← Measure.map_apply (measurable_pi_apply i) measurableSet_Iio, hmap]
    exact expLaw_Iio_zero
  simpa [Set.preimage, not_le] using h

/-! ### The indicator variables `1[xᵢ > 1]` -/

/-- The indicator of `(1,∞)`, as a real-valued function. -/
def cInd (t : ℝ) : ℝ := (Set.Ioi 1).indicator (fun _ => (1 : ℝ)) t

lemma measurable_cInd : Measurable cInd :=
  Measurable.indicator measurable_const measurableSet_Ioi

lemma cInd_nonneg (t : ℝ) : 0 ≤ cInd t :=
  Set.indicator_nonneg (fun _ _ => zero_le_one) t

lemma cInd_le_one (t : ℝ) : cInd t ≤ 1 := by
  rw [cInd]
  by_cases h : t ∈ Set.Ioi 1
  · rw [Set.indicator_of_mem h]
  · rw [Set.indicator_of_notMem h]; norm_num

lemma cInd_le_self {t : ℝ} (ht : 0 ≤ t) : cInd t ≤ t := by
  rw [cInd]
  by_cases h : t ∈ Set.Ioi 1
  · rw [Set.indicator_of_mem h]; exact h.le
  · rw [Set.indicator_of_notMem h]; exact ht

/-- The `i`-th coordinate seen through the indicator `cInd`. -/
def XD (i : ℕ) (x : ℕ → ℝ) : ℝ := cInd (x i)

lemma measurable_XD (i : ℕ) : Measurable (XD i) :=
  measurable_cInd.comp (measurable_pi_apply i)

lemma XD_integrable : Integrable (XD 0) canonM := by
  refine Integrable.of_bound (measurable_XD 0).aestronglyMeasurable 1 ?_
  filter_upwards with x
  rw [XD, Real.norm_eq_abs, abs_of_nonneg (cInd_nonneg _)]
  exact cInd_le_one _

lemma XD_pairwise_indep :
    Pairwise (Function.onFun (fun a b : (ℕ → ℝ) → ℝ => a ⟂ᵢ[canonM] b) XD) := by
  intro i j hij
  have h := ProbabilityTheory.iIndepFun_infinitePi (P := fun _ : ℕ => expLaw)
    (X := fun (_ : ℕ) (t : ℝ) => cInd t) (fun _ => measurable_cInd)
  exact h.indepFun hij

lemma map_XD (i : ℕ) : canonM.map (XD i) = expLaw.map cInd := by
  have hfun : XD i = cInd ∘ fun x : ℕ → ℝ => x i := rfl
  rw [hfun, ← Measure.map_map measurable_cInd (measurable_pi_apply i), canonM,
    Measure.infinitePi_map_eval]

lemma XD_identDistrib : ∀ i : ℕ, IdentDistrib (XD i) (XD 0) canonM canonM :=
  fun i => ⟨(measurable_XD i).aemeasurable, (measurable_XD 0).aemeasurable, by
    rw [map_XD i, map_XD 0]⟩

/-- **Strong law for the indicator variables.**  Almost surely the density of the coordinates
exceeding `1` converges to `e^{-1}`. -/
lemma ae_tendsto_avg_cInd :
    ∀ᵐ x ∂canonM, Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, cInd (x i))
      atTop (𝓝 (∫ t : ℝ, cInd t ∂expLaw)) := by
  have h := ProbabilityTheory.strong_law_ae (μ := canonM) XD XD_integrable
    XD_pairwise_indep XD_identDistrib
  have hval : (∫ x : ℕ → ℝ, XD 0 x ∂canonM) = ∫ t : ℝ, cInd t ∂expLaw := by
    have h1 : (∫ x : ℕ → ℝ, XD 0 x ∂canonM)
        = ∫ y, cInd y ∂(canonM.map (fun x : ℕ → ℝ => x 0)) :=
      (MeasureTheory.integral_map (μ := canonM) (φ := fun x : ℕ → ℝ => x 0) (f := cInd)
        (measurable_pi_apply 0).aemeasurable measurable_cInd.aestronglyMeasurable).symm
    rw [h1, canonM, Measure.infinitePi_map_eval]
  filter_upwards [h] with x hx
  rw [hval] at hx
  simpa [XD] using hx

/-- The mean of `cInd` under the standard exponential law is `e^{-1}`. -/
lemma integral_cInd : (∫ t : ℝ, cInd t ∂expLaw) = Real.exp (-1) := by
  show (∫ t : ℝ, (Set.Ioi 1).indicator (fun _ => (1 : ℝ)) t ∂expLaw) = Real.exp (-1)
  rw [MeasureTheory.integral_indicator_const (1 : ℝ) measurableSet_Ioi, smul_eq_mul,
    mul_one, Measure.real_def, hasExpLaw_expLaw.Ioi (by norm_num : (0 : ℝ) ≤ 1),
    ENNReal.toReal_ofReal (Real.exp_nonneg (-1))]

/-! ### Summability -/

lemma exp_neg_mul_eq_pow (c : ℝ) (k : ℕ) :
    Real.exp (-((k : ℝ) * c)) = Real.exp (-c) ^ k := by
  rw [show -((k : ℝ) * c) = (k : ℝ) * (-c) by ring, Real.exp_nat_mul]

theorem summable_cY_ae : ∀ᵐ x ∂canonM, Summable (fun k : ℕ => Real.exp (-(cSum x k))) := by
  filter_upwards [ae_coord_nonneg, ae_tendsto_avg_cInd] with x hnn htend
  rw [integral_cInd] at htend
  -- almost surely `cSum x k ≥ k · e^{-1}/2` for all large `k`
  have hev : ∀ᶠ n : ℕ in atTop, (n : ℝ) * (Real.exp (-1) / 2) < cSum x n := by
    have h1 : ∀ᶠ n : ℕ in atTop,
        Real.exp (-1) / 2 < (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, cInd (x i) :=
      htend.eventually (Ioi_mem_nhds (by linarith [Real.exp_pos (-1)]))
    filter_upwards [h1, eventually_ge_atTop (a := 1)] with n hn hn1
    have hn0 : (0 : ℝ) < (n : ℝ) := by
      have : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
      linarith
    have hmul := mul_lt_mul_of_pos_left hn hn0
    have hS : (n : ℝ) * ((n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, cInd (x i))
        = ∑ i ∈ Finset.range n, cInd (x i) := by
      rw [← mul_assoc, mul_inv_cancel₀ (ne_of_gt hn0), one_mul]
    rw [hS] at hmul
    have hbound : (∑ i ∈ Finset.range n, cInd (x i)) ≤ cSum x n :=
      Finset.sum_le_sum (fun i _ => cInd_le_self (hnn i))
    linarith
  obtain ⟨N, hN⟩ := eventually_atTop.mp hev
  -- comparison with the geometric series of ratio `e^{-e^{-1}/2}`
  have hgeom : Summable (fun k : ℕ => Real.exp (-((k : ℝ) * (Real.exp (-1) / 2)))) := by
    have hξ : Summable (fun k : ℕ => Real.exp (-(Real.exp (-1) / 2)) ^ k) :=
      summable_geometric_iff_norm_lt_one.mpr (by
        rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
        exact Real.exp_lt_one_iff.mpr (by linarith [Real.exp_pos (-1)]))
    exact hξ.congr fun k => (exp_neg_mul_eq_pow (Real.exp (-1) / 2) k).symm
  have hmaj : Summable (fun n : ℕ => Real.exp (-(((n + N : ℕ) : ℝ) * (Real.exp (-1) / 2)))) :=
    (summable_nat_add_iff
      (f := fun k : ℕ => Real.exp (-((k : ℝ) * (Real.exp (-1) / 2)))) N).mpr hgeom
  have hsub : Summable (fun n : ℕ => Real.exp (-(cSum x (n + N)))) :=
    Summable.of_nonneg_of_le (g := fun n : ℕ => Real.exp (-(cSum x (n + N))))
      (fun n => (Real.exp_pos _).le)
      (fun n => Real.exp_le_exp.mpr (by have := hN (n + N) (by omega); linarith))
      hmaj
  exact (summable_nat_add_iff (f := fun k : ℕ => Real.exp (-(cSum x k))) N).mp hsub

end

end Work.ChenPlan.LinearSieve.Selberg.Alt
