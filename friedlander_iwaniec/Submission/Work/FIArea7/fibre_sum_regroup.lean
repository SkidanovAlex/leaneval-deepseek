import Mathlib

namespace Work.FIArea7

/-- Regrouping a sum over a finite set by the fibres of `φ`, when every value of `φ` on `s`
is bounded by `K` and every fibre has at most `C` elements (in `ℝ`).

The sum `∑_{x ∈ s} f (φ x)` is rewritten as a sum over the possible values `d ∈ range (K+1)`
of `card (fibre d) * f d`, and each fibre cardinal is bounded by `C`. -/
theorem fibre_sum_regroup {α : Type*} (s : Finset α) (φ : α → ℕ) (K : ℕ)
    (C : ℝ) (f : ℕ → ℝ) (hf : ∀ d, 0 ≤ f d) (hK : ∀ x ∈ s, φ x ≤ K)
    (hC : ∀ d, ((s.filter (fun x => φ x = d)).card : ℝ) ≤ C) :
    ∑ x ∈ s, f (φ x) ≤ C * ∑ d ∈ Finset.range (K + 1), f d := by
  have hmap : ∀ x ∈ s, φ x ∈ Finset.range (K + 1) := by
    intro x hx
    rw [Finset.mem_range]
    exact Nat.lt_succ_of_le (hK x hx)
  rw [← Finset.sum_fiberwise_of_maps_to hmap (fun x => f (φ x))]
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro d _
  have hinner : (∑ x ∈ s.filter (fun x => φ x = d), f (φ x))
      = ((s.filter (fun x => φ x = d)).card : ℝ) * f d := by
    have h1 : (∑ x ∈ s.filter (fun x => φ x = d), f (φ x))
        = ∑ x ∈ s.filter (fun x => φ x = d), f d := by
      apply Finset.sum_congr rfl
      intro x hx
      simp only [Finset.mem_filter] at hx
      rw [hx.2]
    rw [h1, Finset.sum_const, nsmul_eq_mul]
  rw [hinner]
  exact mul_le_mul_of_nonneg_right (hC d) (hf d)

end Work.FIArea7
