import Mathlib

namespace Work.FIArea7

/-- Cauchy–Schwarz style bound: for nonnegative `f` on `s`, the sum of `f a * f b`
over pairs `(a, b) ∈ s × s` satisfying `R` is at most `(∑ f z ^ 2) * √(card of the pair set)`.

The proof takes `T` to be the filtered set of pairs; Cauchy–Schwarz applied to the
functions `p ↦ f p.1 * f p.2` and `p ↦ 1` bounds the square of the sum by
`(∑_{p ∈ T} (f p.1 * f p.2)^2) * |T|`, and `∑_{p ∈ s × s} (f p.1 * f p.2)^2 = (∑ f z ^ 2)^2`. -/
theorem pair_sum_le_card_sqrt {ι : Type*} [DecidableEq ι] (s : Finset ι) (f : ι → ℝ)
    (hnn : ∀ i ∈ s, 0 ≤ f i) (R : ι → ι → Prop) [DecidableRel R] :
    (∑ p ∈ (s ×ˢ s).filter (fun p => R p.1 p.2), f p.1 * f p.2)
      ≤ (∑ z ∈ s, f z ^ 2)
        * Real.sqrt ((((s ×ˢ s).filter (fun p => R p.1 p.2)).card : ℕ) : ℝ) := by
  set T := (s ×ˢ s).filter (fun p => R p.1 p.2) with hT
  set S := ∑ z ∈ s, f z ^ 2 with hS
  set x := ∑ p ∈ T, f p.1 * f p.2 with hx
  have hk : (0:ℝ) ≤ (T.card : ℝ) := Nat.cast_nonneg _
  have hSnn : 0 ≤ S := by rw [hS]; exact Finset.sum_nonneg (fun z _ => sq_nonneg (f z))
  have hxnn : 0 ≤ x := by
    rw [hx]
    refine Finset.sum_nonneg (fun p hp => ?_)
    have hp' : p ∈ s ×ˢ s := by rw [hT] at hp; exact (Finset.mem_filter.mp hp).1
    rw [Finset.mem_product] at hp'
    exact mul_nonneg (hnn p.1 hp'.1) (hnn p.2 hp'.2)
  have hcs : x ^ 2 ≤ (∑ p ∈ T, (f p.1 * f p.2) ^ 2) * (T.card : ℝ) := by
    rw [hx]
    have h := Finset.sum_mul_sq_le_sq_mul_sq T (fun p => f p.1 * f p.2) (fun _ => (1:ℝ))
    simpa using h
  have hsq : (∑ p ∈ T, (f p.1 * f p.2) ^ 2) ≤ S ^ 2 := by
    rw [hS]
    have h1 : (∑ p ∈ T, (f p.1 * f p.2) ^ 2) ≤ ∑ p ∈ s ×ˢ s, (f p.1 * f p.2) ^ 2 := by
      refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
      · rw [hT]; exact Finset.filter_subset _ _
      · intro p _ _; positivity
    have h2 : (∑ p ∈ s ×ˢ s, (f p.1 * f p.2) ^ 2) = (∑ z ∈ s, f z ^ 2) ^ 2 := by
      rw [Finset.sum_product]
      simp_rw [mul_pow]
      rw [pow_two, Finset.sum_mul_sum]
    rw [h2] at h1
    exact h1
  have hx2 : x ^ 2 ≤ S ^ 2 * (T.card : ℝ) := by
    have := mul_le_mul_of_nonneg_right hsq hk
    linarith
  have main : x ≤ S * Real.sqrt (T.card : ℝ) := by
    calc x = Real.sqrt (x ^ 2) := (Real.sqrt_sq hxnn).symm
      _ ≤ Real.sqrt (S ^ 2 * (T.card : ℝ)) := Real.sqrt_le_sqrt hx2
      _ = S * Real.sqrt (T.card : ℝ) := by
          rw [Real.sqrt_mul (sq_nonneg S), Real.sqrt_sq_eq_abs, abs_of_nonneg hSnn]
  exact main

end Work.FIArea7
