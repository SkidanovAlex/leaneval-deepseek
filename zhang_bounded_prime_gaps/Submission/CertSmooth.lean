import Mathlib
import Submission.CertAnalytic
import Submission.Commons.MeasureTheory.Integral.tendsto_integral_sq_of_dominated
import Submission.Commons.MeasureTheory.Integral.tendsto_integral_sq_iterated_of_dominated_sf
import Submission.Commons.MeasureTheory.Measure.volume_coord_eq_zero
import Submission.Commons.MeasureTheory.Measure.volume_sum_eq_zero_ge_one

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000

open scoped BigOperators Topology
open Filter Finset MeasureTheory

/-!
# The smooth cutoff of the certificate simplex

The certificate function `certFun = certPoly · 1_{simplex 26/25}` is discontinuous on the facets
`t i = 0` of the orthant and on the boundary hyperplane `Σ t = 26/25`.  The tensor localisation
of §5.3 needs a *continuous* compactly supported input, so here we construct the smooth cutoff

  `smoothCut k c γ t = ∏ i χ (t i / γ) · χ ((c - Σ i, t i) / γ)`

(`χ = Real.smoothTransition`) and record: it is smooth, takes values in `[0,1]`, equals `1` on
the inner simplex `{∀ i, γ ≤ t i, Σt + γ ≤ c}` and vanishes outside the closed simplex
`{t ≥ 0, Σt ≤ c}`.  Consequently `certPoly · smoothCut` is a smooth compactly supported function
which agrees with `certFun` on the inner simplex and vanishes off the certificate simplex.
-/

namespace Commons.NumberTheory.MaynardSieve

noncomputable section

/-- The smooth cutoff of the enlarged simplex `{t ≥ 0, Σ t ≤ c}` of width `γ`. -/
def smoothCut (k : ℕ) (c γ : ℝ) (t : Fin k → ℝ) : ℝ :=
  (∏ i : Fin k, Real.smoothTransition (t i / γ)) * Real.smoothTransition ((c - ∑ i, t i) / γ)

theorem contDiff_smoothCut (k : ℕ) (c γ : ℝ) (n : ℕ∞) :
    ContDiff ℝ n (smoothCut k c γ) := by
  unfold smoothCut
  refine ContDiff.mul (contDiff_prod (fun i _ => ?_)) ?_
  · exact Real.smoothTransition.contDiff.comp ((contDiff_apply ℝ ℝ i).div_const γ)
  · exact Real.smoothTransition.contDiff.comp
      ((contDiff_const.sub (ContDiff.sum (fun i _ => contDiff_apply ℝ ℝ i))).div_const γ)

theorem continuous_smoothCut (k : ℕ) (c γ : ℝ) : Continuous (smoothCut k c γ) :=
  (contDiff_smoothCut k c γ 0).continuous

theorem smoothCut_nonneg {k : ℕ} {c γ : ℝ} (hγ : 0 < γ) (t : Fin k → ℝ) :
    0 ≤ smoothCut k c γ t := by
  unfold smoothCut
  refine mul_nonneg (Finset.prod_nonneg (fun i _ => Real.smoothTransition.nonneg _)) ?_
  by_cases h : 0 ≤ (c - ∑ i, t i) / γ
  · exact Real.smoothTransition.nonneg _
  · rw [Real.smoothTransition.zero_of_nonpos (le_of_not_ge h)]

theorem smoothCut_le_one {k : ℕ} {c γ : ℝ} (hγ : 0 < γ) (t : Fin k → ℝ) :
    smoothCut k c γ t ≤ 1 := by
  unfold smoothCut
  have h1 : (∏ i : Fin k, Real.smoothTransition (t i / γ)) ≤ 1 := by
    have h := Finset.prod_le_one (s := Finset.univ)
      (f := fun i : Fin k => Real.smoothTransition (t i / γ))
      (fun i _ => Real.smoothTransition.nonneg _) (fun i _ => Real.smoothTransition.le_one _)
    simpa using h
  have h0 : 0 ≤ ∏ i : Fin k, Real.smoothTransition (t i / γ) :=
    Finset.prod_nonneg (fun i _ => Real.smoothTransition.nonneg _)
  calc (∏ i : Fin k, Real.smoothTransition (t i / γ)) * Real.smoothTransition ((c - ∑ i, t i) / γ)
      ≤ (∏ i : Fin k, Real.smoothTransition (t i / γ)) * 1 :=
        mul_le_mul_of_nonneg_left (Real.smoothTransition.le_one _) h0
    _ ≤ 1 * 1 := by
        rw [mul_one]
        simpa using h1
    _ = 1 := by norm_num

theorem smoothCut_eq_one {k : ℕ} {c γ : ℝ} (hγ : 0 < γ) {t : Fin k → ℝ}
    (h1 : ∀ i : Fin k, γ ≤ t i) (h2 : γ ≤ c - ∑ i, t i) : smoothCut k c γ t = 1 := by
  unfold smoothCut
  have hprod : (∏ i : Fin k, Real.smoothTransition (t i / γ)) = 1 := by
    refine Finset.prod_eq_one (fun i _ => ?_)
    exact Real.smoothTransition.one_of_one_le (by rw [le_div_iff₀ hγ]; simpa using h1 i)
  rw [hprod, Real.smoothTransition.one_of_one_le (by rw [le_div_iff₀ hγ]; simpa using h2), mul_one]

theorem smoothCut_eq_zero_of_notMem {k : ℕ} {c γ : ℝ} (hγ : 0 < γ) {t : Fin k → ℝ}
    (h : t ∉ simplexSet k c) : smoothCut k c γ t = 0 := by
  unfold smoothCut
  rw [simplexSet, Set.mem_ofPred_eq, not_and_or] at h
  rcases h with h | h
  · push_neg at h
    obtain ⟨i, hi⟩ := h
    have hz : Real.smoothTransition (t i / γ) = 0 :=
      Real.smoothTransition.zero_of_nonpos (by rw [div_nonpos_iff]; exact Or.inr ⟨le_of_lt hi, hγ.le⟩)
    rw [Finset.prod_eq_zero (Finset.mem_univ i) hz, zero_mul]
  · push_neg at h
    have hz : Real.smoothTransition ((c - ∑ i, t i) / γ) = 0 :=
      Real.smoothTransition.zero_of_nonpos (by rw [div_nonpos_iff]; exact Or.inr ⟨by linarith, hγ.le⟩)
    rw [hz, mul_zero]

/-- The smoothed certificate function: the certificate polynomial times the smooth cutoff of the
enlarged simplex `(26/25)·R^50`. -/
def certSmooth (γ : ℝ) (t : Fin 50 → ℝ) : ℝ :=
  certPoly t * smoothCut 50 ((26 : ℝ) / 25) γ t

theorem continuous_certPoly : Continuous certPoly := by
  unfold certPoly
  exact continuous_finsetSum _ (fun j _ => continuous_certTerm j)

theorem continuous_certSmooth {γ : ℝ} (hγ : 0 < γ) : Continuous (certSmooth γ) :=
  continuous_certPoly.mul (continuous_smoothCut 50 _ γ)

theorem certSmooth_support {γ : ℝ} (hγ : 0 < γ) {t : Fin 50 → ℝ}
    (h : t ∉ simplexC 50 ((26 : ℝ) / 25)) : certSmooth γ t = 0 := by
  unfold certSmooth
  rw [smoothCut_eq_zero_of_notMem hγ (by simpa [simplexSet, simplexC] using h), mul_zero]

theorem hasCompactSupport_certSmooth {γ : ℝ} (hγ : 0 < γ) :
    HasCompactSupport (certSmooth γ) :=
  HasCompactSupport.of_support_subset_isCompact (isCompact_simplexC 50 ((26 : ℝ) / 25))
    (fun t ht => by
      simp only [Function.mem_support] at ht
      by_contra h
      exact ht (certSmooth_support hγ h))

theorem simplexC_eq_simplexSet (k : ℕ) (c : ℝ) : simplexC k c = simplexSet k c := by
  ext t; simp [simplexC, simplexSet]

/-- **The inner simplex converges to the certificate function.**  For `γ → 0⁺` the cutoff
`smoothCut` is eventually `1` on the inner simplex, so `certSmooth γ t → certPoly t` there. -/
theorem tendsto_certSmooth_of_mem {t : Fin 50 → ℝ} (ht : t ∈ simplexC 50 ((26 : ℝ) / 25))
    (h0 : ∀ i : Fin 50, t i ≠ 0) (hsum : ∑ i, t i ≠ (26 : ℝ) / 25) :
    Tendsto (fun n : ℕ => certSmooth ((1 : ℝ) / (n + 1)) t) atTop (𝓝 (certFun t)) := by
  have ht' : ∀ i : Fin 50, 0 < t i := fun i => lt_of_le_of_ne (ht.1 i) (Ne.symm (h0 i))
  have hc : ∑ i, t i < (26 : ℝ) / 25 := lt_of_le_of_ne ht.2 hsum
  have hγ : Tendsto (fun n : ℕ => (1 : ℝ) / (n + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have h1 : ∀ᶠ n : ℕ in atTop, ∀ i : Fin 50, (1 : ℝ) / (n + 1) < t i := by
    rw [Filter.eventually_all]
    intro i
    exact hγ.eventually (Iio_mem_nhds (ht' i))
  have h2 : ∀ᶠ n : ℕ in atTop, (1 : ℝ) / (n + 1) < (26 : ℝ) / 25 - ∑ i, t i :=
    hγ.eventually (Iio_mem_nhds (by linarith))
  have hev : ∀ᶠ n : ℕ in atTop, certSmooth ((1 : ℝ) / (n + 1)) t = certPoly t := by
    filter_upwards [h1, h2] with n hn1 hn2
    rw [certSmooth, smoothCut_eq_one (by positivity) (fun i => le_of_lt (hn1 i)) (le_of_lt hn2),
      mul_one]
  rw [certFun, Set.indicator_of_mem (by simpa [simplexC_eq_simplexSet] using ht)]
  exact tendsto_const_nhds.congr' (hev.mono (fun n hn => hn.symm))

/-- Outside the certificate simplex the smoothed function vanishes identically, as does
`certFun`. -/
theorem tendsto_certSmooth_of_notMem {t : Fin 50 → ℝ} (ht : t ∉ simplexC 50 ((26 : ℝ) / 25)) :
    Tendsto (fun n : ℕ => certSmooth ((1 : ℝ) / (n + 1)) t) atTop (𝓝 (certFun t)) := by
  have hz : ∀ n : ℕ, certSmooth ((1 : ℝ) / (n + 1)) t = 0 := by
    intro n
    have hγ : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    by_cases h : ∀ i : Fin 50, 0 ≤ t i
    · have h2 : (26 : ℝ) / 25 < ∑ i, t i := by
        by_contra hle
        exact ht ⟨h, le_of_not_gt hle⟩
      rw [certSmooth, smoothCut]
      have hfac : Real.smoothTransition (((26 : ℝ) / 25 - ∑ i, t i) / (1 / ((n : ℝ) + 1))) = 0 :=
        Real.smoothTransition.zero_of_nonpos (by
          rw [div_nonpos_iff]; exact Or.inr ⟨by linarith, le_of_lt hγ⟩)
      rw [hfac, mul_zero, mul_zero]
    · push Not at h
      obtain ⟨i, hi⟩ := h
      rw [certSmooth, smoothCut]
      have hfac : Real.smoothTransition (t i / (1 / ((n : ℝ) + 1))) = 0 :=
        Real.smoothTransition.zero_of_nonpos (by
          rw [div_nonpos_iff]; exact Or.inr ⟨le_of_lt hi, le_of_lt hγ⟩)
      rw [Finset.prod_eq_zero (Finset.mem_univ i) hfac, zero_mul, mul_zero]
  rw [certFun, Set.indicator_of_notMem (by simpa [simplexC_eq_simplexSet] using ht)]
  simp only [hz, Pi.zero_apply]
  exact tendsto_const_nhds

/-- **The smoothed certificate converges to `certFun` almost everywhere.** -/
theorem ae_tendsto_certSmooth :
    ∀ᵐ t : Fin 50 → ℝ ∂(volume : Measure (Fin 50 → ℝ)),
      Tendsto (fun n : ℕ => certSmooth ((1 : ℝ) / (n + 1)) t) atTop (𝓝 (certFun t)) := by
  rw [MeasureTheory.ae_iff]
  have h0 : (volume : Measure (Fin 50 → ℝ)) {t | ∃ i : Fin 50, t i = 0} = 0 := by
    have hset : {t : Fin 50 → ℝ | ∃ i, t i = 0} = ⋃ i, {t | t i = 0} := by
      ext t; simp
    rw [hset]
    exact measure_iUnion_null fun i =>
      Commons.MeasureTheory.Measure.volume_coord_eq_zero i 0
  have h1 : (volume : Measure (Fin 50 → ℝ)) {t | ∑ i, t i = (26 : ℝ) / 25} = 0 :=
    Commons.MeasureTheory.Measure.volume_sum_eq_zero_ge_one (by norm_num) _
  refine measure_mono_null ?_ (measure_union_null h0 h1)
  intro t ht
  simp only [Set.mem_setOf_eq, Set.mem_union] at ht ⊢
  by_contra hcon
  push Not at hcon
  obtain ⟨hne, hsum⟩ := hcon
  refine ht ?_
  by_cases hmem : t ∈ simplexC 50 ((26 : ℝ) / 25)
  · exact tendsto_certSmooth_of_mem hmem hne hsum
  · exact tendsto_certSmooth_of_notMem hmem

/-- The domination function for the smoothed certificate: the absolute value of the certificate
polynomial, cut off on the certificate simplex. -/
noncomputable def certBound (t : Fin 50 → ℝ) : ℝ :=
  |certPoly t| * (simplexC 50 ((26 : ℝ) / 25)).indicator (fun _ => (1 : ℝ)) t

theorem certSmooth_abs_le_certBound {γ : ℝ} (hγ : 0 < γ) (t : Fin 50 → ℝ) :
    |certSmooth γ t| ≤ certBound t := by
  by_cases h : t ∈ simplexC 50 ((26 : ℝ) / 25)
  · rw [certSmooth, certBound, Set.indicator_of_mem h, mul_one, abs_mul,
      abs_of_nonneg (smoothCut_nonneg hγ t)]
    exact mul_le_of_le_one_right (abs_nonneg _) (smoothCut_le_one hγ t)
  · rw [certSmooth_support hγ h, certBound, Set.indicator_of_notMem h, mul_zero, abs_zero]

theorem measurableSet_simplexC (k : ℕ) (c : ℝ) :
    MeasurableSet (simplexC k c) := (isClosed_simplexC k c).measurableSet

theorem integrable_certBound_sq :
    Integrable (fun t : Fin 50 → ℝ => (certBound t) ^ 2) volume := by
  have hS : MeasurableSet (simplexC 50 ((26 : ℝ) / 25)) := measurableSet_simplexC 50 _
  rw [show (fun t : Fin 50 → ℝ => (certBound t) ^ 2)
      = (simplexC 50 ((26 : ℝ) / 25)).indicator (fun t => (certPoly t) ^ 2) from by
        funext t
        rw [certBound]
        by_cases ht : t ∈ simplexC 50 ((26 : ℝ) / 25)
        · rw [Set.indicator_of_mem ht, Set.indicator_of_mem ht]
          simp only [mul_one]
          exact sq_abs _
        · rw [Set.indicator_of_notMem ht, Set.indicator_of_notMem ht]; simp]
  rw [integrable_indicator_iff hS]
  exact ContinuousOn.integrableOn_compact (isCompact_simplexC 50 _)
    ((continuous_certPoly.pow 2).continuousOn)

theorem aestronglyMeasurable_certFun :
    AEStronglyMeasurable certFun (volume : Measure (Fin 50 → ℝ)) := by
  unfold certFun
  exact ((continuous_certPoly.measurable.indicator (measurableSet_simplexC 50 _))).aestronglyMeasurable

/-- **The `I`-functional of the smoothed certificate converges to the certificate's `I`.** -/
theorem tendsto_IFuncOrth_certSmooth :
    Tendsto (fun n : ℕ => IFuncOrth 50 (certSmooth ((1 : ℝ) / (n + 1)))) atTop
      (𝓝 (IFuncOrth 50 certFun)) := by
  unfold IFuncOrth
  refine Commons.MeasureTheory.Integral.tendsto_integral_sq_of_dominated
    (fun n => (continuous_certSmooth (by positivity)).aestronglyMeasurable)
    aestronglyMeasurable_certFun ae_tendsto_certSmooth ?_ integrable_certBound_sq
  filter_upwards with t n
  exact certSmooth_abs_le_certBound (by positivity) t

end

end Commons.NumberTheory.MaynardSieve
