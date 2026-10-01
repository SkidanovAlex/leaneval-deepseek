import Mathlib
import Submission.Commons.Analysis.Integral.layer_cake_interval_integral

open MeasureTheory Set
open scoped Interval

namespace Commons.Analysis.Integral

/-- **Layer-cake identity for a finite family of truncated functions.**

For a finite family of values `f i ∈ [0, K]` and arbitrary real coefficients `c i`,
the weighted sum `∑ i ∈ s, c i * f i` equals the integral over `[0, K]` of the
function which, at level `x`, collects the coefficients `c i` of those `i` whose
value exceeds the level `x`, i.e. `∑ i ∈ s, (if x ≤ f i then c i else 0)`. -/
theorem finset_layerCake {ι : Type*} (s : Finset ι) (c f : ι → ℝ) {K : ℝ} (hK : 0 ≤ K)
    (hf : ∀ i ∈ s, 0 ≤ f i ∧ f i ≤ K) :
    ∑ i ∈ s, c i * f i
      = ∫ x in (0 : ℝ)..K, ∑ i ∈ s, (if x ≤ f i then c i else 0) := by
  -- Each summand `i` is (as a function of the level `x`) the indicator of `[0, f i]`,
  -- scaled by `c i`; these are interval integrable, so the integral of the finite sum
  -- splits into the sum of the integrals.
  have hInt : ∀ i ∈ s, IntervalIntegrable
      (fun x : ℝ => (Set.Icc 0 (f i)).indicator (fun _ : ℝ => c i) x) volume 0 K := by
    intro i hi
    have hbase : IntegrableOn (fun _ : ℝ => c i) (Ι (0 : ℝ) K) volume := by
      rw [← intervalIntegrable_iff]
      exact intervalIntegrable_const
    have hind : IntegrableOn ((Set.Icc 0 (f i)).indicator (fun _ : ℝ => c i))
        (Ι (0 : ℝ) K) volume := hbase.indicator measurableSet_Icc
    rwa [intervalIntegrable_iff]
  calc ∑ i ∈ s, c i * f i
      = ∑ i ∈ s, ∫ x in (0 : ℝ)..K, (Set.Icc 0 (f i)).indicator (fun _ : ℝ => c i) x := by
        refine Finset.sum_congr rfl (fun i hi => ?_)
        rw [Commons.Analysis.Integral.intervalIntegral_indicator_Icc_eq (le_refl (0 : ℝ))
              (hf i hi).1 (hf i hi).2, intervalIntegral.integral_const]
        simp [smul_eq_mul, mul_comm]
    _ = ∫ x in (0 : ℝ)..K, ∑ i ∈ s, (Set.Icc 0 (f i)).indicator (fun _ : ℝ => c i) x := by
        rw [intervalIntegral.integral_finsetSum (s := s) hInt]
    _ = ∫ x in (0 : ℝ)..K, ∑ i ∈ s, (if x ≤ f i then c i else 0) := by
        -- Pointwise on `[0, K]` the indicator of `[0, f i]` agrees with `x ≤ f i`.
        apply intervalIntegral.integral_congr
        intro x hx
        have hx0 : 0 ≤ x := by
          have hx' := hx
          rw [Set.uIcc_of_le hK] at hx'
          exact (Set.mem_Icc.mp hx').1
        refine Finset.sum_congr rfl (fun i hi => ?_)
        by_cases h : x ≤ f i
        · rw [Set.indicator_of_mem (Set.mem_Icc.mpr ⟨hx0, h⟩), if_pos h]
        · rw [Set.indicator_of_notMem (fun hmem => h (Set.mem_Icc.mp hmem).2), if_neg h]

end Commons.Analysis.Integral
