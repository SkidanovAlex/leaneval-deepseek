import Mathlib.Data.Complex.BigOperators
import Mathlib.Data.Int.ConditionallyCompleteOrder
import Mathlib.Data.Int.Interval
import Mathlib.Data.Int.Star
import Mathlib.Tactic.Linarith.Frontend
import Mathlib.Algebra.Order.Ring.Star
import Submission.Work.UBBInputs3.MatLoc.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.UBBInputs3.MatLoc

/-- **Reindexing a double sum by the difference `k = j - i`.**

For a matrix `C` that vanishes outside `iRange n × iRange n` and any `f : ℤ → ℝ`,
the double sum over the index range can be regrouped according to the difference
`k = j - i`, which then runs over `[-(n-1), n-1]`.  For a fixed `k` the terms with
`i + k ∉ iRange n` are exactly the terms that are absent from the inner sum, and
they vanish by the support hypothesis `hC`; this is what allows the range of `k`
to be the full interval `[-(n-1), n-1]`. -/
theorem sum_diff_reindex (C : ℤ → ℤ → ℂ) (f : ℤ → ℝ) (n : ℕ)
    (hC : ∀ i, i ∈ Work.UBBInputs3.iRange n → ∀ j, j ∉ Work.UBBInputs3.iRange n → C i j = 0) :
    ∑ i ∈ Work.UBBInputs3.iRange n, ∑ j ∈ Work.UBBInputs3.iRange n, f (j - i) * (C i j).re
      = ∑ k ∈ Finset.Icc (-((n : ℤ) - 1)) ((n : ℤ) - 1),
          f k * (∑ i ∈ Work.UBBInputs3.iRange n, C i (i + k)).re := by
  -- For fixed `i` the inner sum over `j ∈ iRange n` is reindexed by `k = j - i`,
  -- which turns it into a sum over `k ∈ Icc (-i) ((n-1) - i)`.
  have hshift : ∀ i : ℤ, ∑ j ∈ Work.UBBInputs3.iRange n, f (j - i) * (C i j).re
      = ∑ k ∈ Finset.Icc (-i) (((n : ℤ) - 1) - i), f k * (C i (i + k)).re := by
    intro i
    have key := sum_Icc_shift (fun k => f k * (C i (i + k)).re) (-i) (((n : ℤ) - 1) - i) (-i)
    rw [show (-i - -i) = (0:ℤ) by ring,
        show ((↑n - 1 - i) - -i) = (↑n - 1) by ring] at key
    rw [← key]
    apply Finset.sum_congr rfl
    intro j hj
    simp only [sub_eq_add_neg]
    rw [show i + (j + -i) = j by ring]
  -- For `i ∈ iRange n` the range `Icc (-i) ((n-1) - i)` can be enlarged to the full
  -- range `K = Icc (-(n-1)) (n-1)`: the extra terms have `i + k ∉ iRange n` so
  -- `C i (i + k) = 0`.
  have hext : ∀ i : ℤ, i ∈ Work.UBBInputs3.iRange n →
      ∑ k ∈ Finset.Icc (-((n : ℤ) - 1)) ((n : ℤ) - 1), f k * (C i (i + k)).re
      = ∑ k ∈ Finset.Icc (-i) (((n : ℤ) - 1) - i), f k * (C i (i + k)).re := by
    intro i hi
    rw [Work.UBBInputs3.iRange, Finset.mem_Icc] at hi
    refine sum_Icc_congr_of_eq_zero_outside (fun k => f k * (C i (i + k)).re) ?_ ?_ ?_
    · linarith [hi.2]
    · linarith [hi.1]
    · intro t ht
      have hmem : i + t ∉ Work.UBBInputs3.iRange n := by
        intro hmem
        rw [Work.UBBInputs3.iRange, Finset.mem_Icc] at hmem
        exact ht (by rw [Finset.mem_Icc]; constructor <;> linarith [hmem.1, hmem.2])
      rw [hC i (by rw [Work.UBBInputs3.iRange, Finset.mem_Icc]; exact hi) (i + t) hmem]
      simp
  trans ∑ i ∈ Work.UBBInputs3.iRange n,
        ∑ k ∈ Finset.Icc (-((n : ℤ) - 1)) ((n : ℤ) - 1), f k * (C i (i + k)).re
  · exact Finset.sum_congr rfl (fun i hi => by rw [hshift i, hext i hi])
  · rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro k hk
    rw [Complex.re_sum, Finset.mul_sum]

end Work.UBBInputs3.MatLoc
