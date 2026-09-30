import Mathlib
import Submission.Work.BMF.Defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF.SD

/--
Markov-type inequality used in the sieve/descent part of the argument.

If `A p ≥ 0` for `p ∈ S` and `∑_{p ∈ S} p · A p ≤ c H²`, then the weighted count of
those `p` for which `δ² H² < p² · A p` satisfies `∑ 1 / p ≤ c / δ²`.

Indeed, for such `p` one has `1/p · δ²H² ≤ p · A p`, so each term is dominated by
`(p · A p)/(δ² H²)` and the whole sum telescopes against the hypothesis.
-/
theorem markov_inv (S : Finset ℕ) (A : ℕ → ℝ) (c δ H : ℝ)
    (hA : ∀ p ∈ S, 0 ≤ A p) (hδ : 0 < δ) (hH : 0 < H) (hc : 0 ≤ c)
    (hbound : ∑ p ∈ S, ((p : ℕ) : ℝ) * A p ≤ c * H ^ 2) :
    ∑ p ∈ S.filter (fun p => δ ^ 2 * H ^ 2 < ((p : ℕ) : ℝ) ^ 2 * A p),
      1 / ((p : ℕ) : ℝ) ≤ c / δ ^ 2 := by
  have hk : 0 < δ ^ 2 * H ^ 2 := by positivity
  -- Pointwise domination: `1/p ≤ (p * A p)/(δ²H²)` on the filtered set.
  have key : ∀ p ∈ S.filter (fun p => δ ^ 2 * H ^ 2 < ((p : ℕ) : ℝ) ^ 2 * A p),
      1 / ((p : ℕ) : ℝ) ≤ (((p : ℕ) : ℝ) * A p) / (δ ^ 2 * H ^ 2) := by
    intro p hp
    have hfilt : δ ^ 2 * H ^ 2 < ((p : ℕ) : ℝ) ^ 2 * A p := (Finset.mem_filter.mp hp).2
    by_cases hx : ((p : ℕ) : ℝ) = 0
    · simp [hx]
    · have hxpos : 0 < ((p : ℕ) : ℝ) := by
        have hpne : p ≠ 0 := by intro h; exact hx (by simp [h])
        exact_mod_cast Nat.pos_of_ne_zero hpne
      rw [le_div_iff₀ hk]
      have h2 : δ ^ 2 * H ^ 2 / ((p : ℕ) : ℝ) ≤ ((p : ℕ) : ℝ) * A p := by
        rw [div_le_iff₀ hxpos]
        nlinarith [hfilt]
      have heq : 1 / ((p : ℕ) : ℝ) * (δ ^ 2 * H ^ 2) = δ ^ 2 * H ^ 2 / ((p : ℕ) : ℝ) := by
        ring
      rw [heq]; exact h2
  calc ∑ p ∈ S.filter (fun p => δ ^ 2 * H ^ 2 < ((p : ℕ) : ℝ) ^ 2 * A p), 1 / ((p : ℕ) : ℝ)
      ≤ ∑ p ∈ S.filter (fun p => δ ^ 2 * H ^ 2 < ((p : ℕ) : ℝ) ^ 2 * A p),
            (((p : ℕ) : ℝ) * A p) / (δ ^ 2 * H ^ 2) := Finset.sum_le_sum key
    _ = (∑ p ∈ S.filter (fun p => δ ^ 2 * H ^ 2 < ((p : ℕ) : ℝ) ^ 2 * A p),
            ((p : ℕ) : ℝ) * A p) / (δ ^ 2 * H ^ 2) := by rw [Finset.sum_div]
    _ ≤ (∑ p ∈ S, ((p : ℕ) : ℝ) * A p) / (δ ^ 2 * H ^ 2) := by
          apply div_le_div_of_nonneg_right _ (le_of_lt hk)
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · exact Finset.filter_subset _ _
          · intro x hxS _
            exact mul_nonneg (by positivity) (hA x hxS)
    _ ≤ (c * H ^ 2) / (δ ^ 2 * H ^ 2) := div_le_div_of_nonneg_right hbound (le_of_lt hk)
    _ = c / δ ^ 2 := by field_simp

end Work.BMF.SD
