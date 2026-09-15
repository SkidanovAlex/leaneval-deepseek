import Mathlib.Analysis.MeanInequalities

namespace Commons.Analysis.Convex

open Finset
open scoped BigOperators

/-- AM-GM combined with the power mean inequality: for nonnegative `a i`,
`∏_{i∈s} a i ≤ (1/|s|) ∑_{i∈s} a i ^ |s|`. -/
theorem prod_le_inv_card_mul_sum_pow {ι : Type*} (s : Finset ι) (a : ι → ℝ) (hne : s.Nonempty)
    (ha : ∀ i ∈ s, 0 ≤ a i) :
    ∏ i ∈ s, a i ≤ (s.card : ℝ)⁻¹ * ∑ i ∈ s, a i ^ s.card := by
  have hcard : s.card ≠ 0 := hne.card_ne_zero
  have key := Real.geom_mean_le_arith_mean_weighted s (fun _ => (s.card : ℝ)⁻¹)
    (fun i => a i ^ s.card)
    (fun i _ => inv_nonneg.mpr (Nat.cast_nonneg _))
    (by rw [Finset.sum_const, nsmul_eq_mul]; exact mul_inv_cancel₀ (Nat.cast_ne_zero.mpr hcard))
    (fun i hi => pow_nonneg (ha i hi) _)
  calc ∏ i ∈ s, a i
      = ∏ i ∈ s, (a i ^ s.card) ^ (s.card : ℝ)⁻¹ := by
        refine Finset.prod_congr rfl fun i hi => ?_
        rw [Real.pow_rpow_inv_natCast (ha i hi) hcard]
    _ ≤ ∑ i ∈ s, (s.card : ℝ)⁻¹ * a i ^ s.card := key
    _ = (s.card : ℝ)⁻¹ * ∑ i ∈ s, a i ^ s.card := by rw [Finset.mul_sum]

end Commons.Analysis.Convex