import Mathlib.Analysis.SpecialFunctions.Log.Basic

namespace Commons.Analysis.Harmonic

open Finset Real

/-- Harmonic-sum bound by the integral: `∑_{i=0}^{L} 1/(x+i) ≤ 1/x + log(1 + L/x)` for `x > 0`. -/
lemma sum_range_inv_add_le {x : ℝ} (hx : 0 < x) (L : ℕ) :
    (∑ i ∈ Finset.range (L + 1), 1 / (x + (i : ℝ))) ≤ 1 / x + Real.log (1 + (L : ℝ) / x) := by
  have hterm : ∀ k ∈ Finset.range L,
      1 / (x + ((k : ℝ) + 1)) ≤ Real.log ((x + ((k : ℝ) + 1)) / (x + (k : ℝ))) := by
    intro k _
    have h := Real.one_sub_inv_le_log_of_pos
      (show (0 : ℝ) < (x + ((k : ℝ) + 1)) / (x + (k : ℝ)) by positivity)
    rw [inv_div] at h
    have heq : 1 - (x + (k : ℝ)) / (x + ((k : ℝ) + 1)) = 1 / (x + ((k : ℝ) + 1)) := by
      field_simp
      ring
    rwa [heq] at h
  have htel : ∑ k ∈ Finset.range L, Real.log ((x + ((k : ℝ) + 1)) / (x + (k : ℝ)))
      = Real.log (1 + (L : ℝ) / x) := by
    have hlog : ∀ k : ℕ, Real.log ((x + ((k : ℝ) + 1)) / (x + (k : ℝ)))
        = Real.log (x + ((k + 1 : ℕ) : ℝ)) - Real.log (x + (k : ℝ)) := by
      intro k
      rw [Real.log_div (by positivity) (by positivity)]
      congr 1
      push_cast
      ring
    simp_rw [hlog]
    rw [Finset.sum_range_sub (fun k : ℕ => Real.log (x + (k : ℝ)))]
    simp only [Nat.cast_zero, add_zero]
    have h1 : (1 : ℝ) + (L : ℝ) / x = (x + (L : ℝ)) / x := by
      field_simp
    rw [h1, Real.log_div (by positivity) (ne_of_gt hx)]
  have hsum : ∑ i ∈ Finset.range (L + 1), 1 / (x + (i : ℝ))
      = 1 / x + ∑ k ∈ Finset.range L, 1 / (x + ((k : ℝ) + 1)) := by
    rw [Finset.sum_range_succ' (fun k : ℕ => 1 / (x + (k : ℝ))) L]
    simp only [Nat.cast_zero, add_zero]
    rw [add_comm]
    congr 1
    apply Finset.sum_congr rfl
    intro k _
    congr 1
    push_cast
    ring
  rw [hsum]
  have h1 : ∑ k ∈ Finset.range L, 1 / (x + ((k : ℝ) + 1)) ≤ Real.log (1 + (L : ℝ) / x) := by
    have := Finset.sum_le_sum (s := Finset.range L) hterm
    rwa [htel] at this
  linarith

end Commons.Analysis.Harmonic