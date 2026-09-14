import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Order.CompletePartialOrder

open MeasureTheory Set Filter
open scoped ENNReal Topology Interval

namespace Commons.Analysis.Integral

/-- Cauchy--Schwarz for Bochner integrals: the square of the norm of the integral of `f` over `s`
is bounded by the measure of `s` times the integral of `‖f‖ ^ 2`, as soon as `‖f‖ ^ 2` is
integrable on `s` and `s` has finite measure. -/
lemma norm_setIntegral_sq_le {α : Type*} [MeasurableSpace α] {μ : Measure α} {s : Set α}
    (hμ : μ s < ⊤) {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {f : α → F}
    (hg : IntegrableOn (fun x ↦ ‖f x‖ ^ 2) s μ) :
    ‖∫ x in s, f x ∂μ‖ ^ 2 ≤ (μ s).toReal * ∫ x in s, ‖f x‖ ^ 2 ∂μ := by
  have hAESM2 : AEStronglyMeasurable (fun x ↦ ‖f x‖ ^ 2) (μ.restrict s) := hg.aestronglyMeasurable
  have hAEM1 : AEMeasurable (fun x ↦ ‖f x‖) (μ.restrict s) := by
    have h := hAESM2.aemeasurable.sqrt
    refine h.congr ?_
    filter_upwards with x
    rw [Real.sqrt_sq (norm_nonneg _)]
  have hMemLp : MemLp (fun x ↦ ‖f x‖) 2 (μ.restrict s) :=
    (memLp_two_iff_integrable_sq hAEM1.aestronglyMeasurable).2 hg
  have hMemLp1 : MemLp (fun _ : α ↦ (1 : ℝ)) 2 (μ.restrict s) := by
    rw [memLp_const_iff (by norm_num) (by norm_num)]
    right
    rw [Measure.restrict_apply MeasurableSet.univ, Set.univ_inter]
    exact hμ
  have hpq : (2 : ℝ).HolderConjugate 2 :=
    Real.holderConjugate_iff.mpr ⟨by norm_num, by norm_num⟩
  have hHold := integral_mul_le_Lp_mul_Lq_of_nonneg (μ := μ.restrict s) (p := 2) (q := 2)
    hpq (Eventually.of_forall fun x ↦ norm_nonneg _) (Eventually.of_forall fun _ ↦ zero_le_one)
    (by simpa using hMemLp) (by simpa using hMemLp1)
  have e1 : (∫ a, ‖f a‖ * (fun _ : α ↦ (1 : ℝ)) a ∂(μ.restrict s)) = ∫ x in s, ‖f x‖ ∂μ := by
    simp
  have e2 : (∫ a, ‖f a‖ ^ (2 : ℝ) ∂(μ.restrict s)) = ∫ x in s, ‖f x‖ ^ 2 ∂μ := by
    refine integral_congr_ae (Eventually.of_forall fun x ↦ ?_)
    exact Real.rpow_two (‖f x‖)
  have e3 : (∫ a, (fun _ : α ↦ (1 : ℝ)) a ^ (2 : ℝ) ∂(μ.restrict s)) = (μ s).toReal := by
    simp only [Real.one_rpow]
    rw [integral_const, Measure.real_def, Measure.restrict_apply MeasurableSet.univ, Set.univ_inter]
    simp
  rw [e1, e2, e3, ← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow] at hHold
  have hnorm : ‖∫ x in s, f x ∂μ‖ ≤ ∫ x in s, ‖f x‖ ∂μ := norm_integral_le_integral_norm _
  have hle : ‖∫ x in s, f x ∂μ‖
      ≤ Real.sqrt (∫ x in s, ‖f x‖ ^ 2 ∂μ) * Real.sqrt (μ s).toReal := le_trans hnorm hHold
  have hsq := pow_le_pow_left₀ (norm_nonneg _) hle 2
  have hA : 0 ≤ ∫ x in s, ‖f x‖ ^ 2 ∂μ :=
    integral_nonneg_of_ae (Eventually.of_forall fun x ↦ sq_nonneg _)
  have hB : 0 ≤ (μ s).toReal := ENNReal.toReal_nonneg
  have hsq' : ‖∫ x in s, f x ∂μ‖ ^ 2 ≤ (∫ x in s, ‖f x‖ ^ 2 ∂μ) * (μ s).toReal := by
    simpa only [mul_pow, Real.sq_sqrt hA, Real.sq_sqrt hB] using hsq
  calc ‖∫ x in s, f x ∂μ‖ ^ 2 ≤ (∫ x in s, ‖f x‖ ^ 2 ∂μ) * (μ s).toReal := hsq'
    _ = (μ s).toReal * ∫ x in s, ‖f x‖ ^ 2 ∂μ := by ring

/-- For a function `g : ℝ → F` with square-integrable restriction to the union `E` of a finite
pairwise disjoint family of half-open intervals `uIoc (x i) (y i)`, the sum of the norms of the
interval integrals of `g` over the pieces is bounded by `√K * √L`, where `K` bounds
`∫_E ‖g‖²` and `L = ∑ i, (y i - x i)` is the total length of `E`. -/
theorem sum_norm_intervalIntegral_le {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (g : ℝ → F) {n : ℕ} (x y : ℕ → ℝ) (hxy : ∀ i < n, x i ≤ y i)
    (hdisj : Set.PairwiseDisjoint (Finset.range n) (fun i ↦ uIoc (x i) (y i)))
    (hint : IntegrableOn (fun t ↦ ‖g t‖ ^ 2) (⋃ i ∈ Finset.range n, uIoc (x i) (y i)) volume)
    {K : ℝ} (hK0 : 0 ≤ K)
    (hK : ∫ t in (⋃ i ∈ Finset.range n, uIoc (x i) (y i)), ‖g t‖ ^ 2 ≤ K) :
    ∑ i ∈ Finset.range n, ‖∫ t in (x i)..(y i), g t‖ ≤
      Real.sqrt K * Real.sqrt (∑ i ∈ Finset.range n, (y i - x i)) := by
  set J : ℕ → ℝ := fun i ↦ ∫ t in uIoc (x i) (y i), ‖g t‖ ^ 2 with hJ
  have hJi : ∀ i, J i = ∫ t in uIoc (x i) (y i), ‖g t‖ ^ 2 := fun i ↦ by rw [hJ]
  have hInt : ∀ i ∈ Finset.range n, IntegrableOn (fun t ↦ ‖g t‖ ^ 2) (uIoc (x i) (y i)) volume :=
    fun i hi ↦ hint.mono_set (Set.subset_biUnion_of_mem (u := fun i ↦ uIoc (x i) (y i)) hi)
  have hJsum : (∑ i ∈ Finset.range n, J i)
      = ∫ t in (⋃ i ∈ Finset.range n, uIoc (x i) (y i)), ‖g t‖ ^ 2 := by
    rw [show (∑ i ∈ Finset.range n, J i)
        = ∑ i ∈ Finset.range n, ∫ t in uIoc (x i) (y i), ‖g t‖ ^ 2 from
      Finset.sum_congr rfl fun i _ ↦ hJi i]
    exact (MeasureTheory.integral_biUnion_finset (Finset.range n)
      (fun i _ ↦ measurableSet_uIoc) hdisj hInt).symm
  have hpiece : ∀ i ∈ Finset.range n,
      ‖∫ t in (x i)..(y i), g t‖ ≤ Real.sqrt (y i - x i) * Real.sqrt (J i) := by
    intro i hi
    have hin : i < n := Finset.mem_range.mp hi
    have hle : x i ≤ y i := hxy i hin
    have hvol : (volume (uIoc (x i) (y i))).toReal = y i - x i := by
      rw [Set.uIoc_of_le hle, Real.volume_Ioc, ENNReal.toReal_ofReal (sub_nonneg.mpr hle)]
    have hμ : volume (uIoc (x i) (y i)) < ⊤ := by
      rw [Set.uIoc_of_le hle, Real.volume_Ioc]; exact ENNReal.ofReal_lt_top
    have heq : (∫ t in (x i)..(y i), g t) = ∫ t in uIoc (x i) (y i), g t := by
      rw [intervalIntegral.integral_of_le hle, ← Set.uIoc_of_le hle]
    rw [heq]
    have hcs := norm_setIntegral_sq_le (μ := volume) (s := uIoc (x i) (y i)) hμ (hInt i hi)
    rw [hvol, ← hJi i] at hcs
    have h1 : ‖∫ t in uIoc (x i) (y i), g t‖ ≤ Real.sqrt ((y i - x i) * J i) := by
      rw [← Real.sqrt_sq (norm_nonneg (∫ t in uIoc (x i) (y i), g t))]
      exact Real.sqrt_le_sqrt hcs
    rwa [Real.sqrt_mul (sub_nonneg.mpr hle)] at h1
  have hsum1 : (∑ i ∈ Finset.range n, ‖∫ t in (x i)..(y i), g t‖)
      ≤ ∑ i ∈ Finset.range n, Real.sqrt (y i - x i) * Real.sqrt (J i) :=
    Finset.sum_le_sum hpiece
  have hCS : (∑ i ∈ Finset.range n, Real.sqrt (y i - x i) * Real.sqrt (J i))
      ≤ Real.sqrt (∑ i ∈ Finset.range n, (y i - x i))
        * Real.sqrt (∑ i ∈ Finset.range n, J i) := by
    have hcs := Finset.sum_mul_sq_le_sq_mul_sq (Finset.range n)
      (fun i ↦ Real.sqrt (y i - x i)) (fun i ↦ Real.sqrt (J i))
    have hu : (∑ i ∈ Finset.range n, (Real.sqrt (y i - x i)) ^ 2)
        = ∑ i ∈ Finset.range n, (y i - x i) :=
      Finset.sum_congr rfl fun i hi ↦
        Real.sq_sqrt (sub_nonneg.mpr (hxy i (Finset.mem_range.mp hi)))
    have hv : (∑ i ∈ Finset.range n, (Real.sqrt (J i)) ^ 2) = ∑ i ∈ Finset.range n, J i :=
      Finset.sum_congr rfl fun i _ ↦
        Real.sq_sqrt (by rw [hJi i]
                         exact integral_nonneg_of_ae (Eventually.of_forall fun t ↦ sq_nonneg _))
    rw [hu, hv] at hcs
    have hleft : 0 ≤ ∑ i ∈ Finset.range n, Real.sqrt (y i - x i) * Real.sqrt (J i) :=
      Finset.sum_nonneg fun i _ ↦ mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    have h2 : (∑ i ∈ Finset.range n, Real.sqrt (y i - x i) * Real.sqrt (J i))
        ≤ Real.sqrt ((∑ i ∈ Finset.range n, (y i - x i)) * ∑ i ∈ Finset.range n, J i) := by
      rw [← Real.sqrt_sq hleft]
      exact Real.sqrt_le_sqrt hcs
    have hA : 0 ≤ ∑ i ∈ Finset.range n, (y i - x i) :=
      Finset.sum_nonneg fun i hi ↦ sub_nonneg.mpr (hxy i (Finset.mem_range.mp hi))
    rwa [Real.sqrt_mul hA] at h2
  have hJleK : (∑ i ∈ Finset.range n, J i) ≤ K := by rw [hJsum]; exact hK
  have hsqrtJ : Real.sqrt (∑ i ∈ Finset.range n, J i) ≤ Real.sqrt K := Real.sqrt_le_sqrt hJleK
  calc (∑ i ∈ Finset.range n, ‖∫ t in (x i)..(y i), g t‖)
      ≤ ∑ i ∈ Finset.range n, Real.sqrt (y i - x i) * Real.sqrt (J i) := hsum1
    _ ≤ Real.sqrt (∑ i ∈ Finset.range n, (y i - x i))
          * Real.sqrt (∑ i ∈ Finset.range n, J i) := hCS
    _ ≤ Real.sqrt (∑ i ∈ Finset.range n, (y i - x i)) * Real.sqrt K :=
        mul_le_mul_of_nonneg_left hsqrtJ (Real.sqrt_nonneg _)
    _ = Real.sqrt K * Real.sqrt (∑ i ∈ Finset.range n, (y i - x i)) := by ring

end Commons.Analysis.Integral