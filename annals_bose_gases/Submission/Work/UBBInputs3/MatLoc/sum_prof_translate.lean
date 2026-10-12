import Mathlib.Data.Int.ConditionallyCompleteOrder
import Mathlib.Data.Int.Interval
import Mathlib.Data.Real.Basic
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Tactic.Ring.RingNF
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Submission.Work.UBBInputs3.MatLoc.Rcorr_even
import Submission.Work.UBBInputs3.MatLoc.gamma_sum_shift
import Submission.Work.UBBInputs3.MatLoc.prof_zero_outside
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.UBBInputs3.MatLoc.sum_prof_translate`

For `i, j` in the index range `iRange n` of a length-`n` vector, the sum over the
translation parameter `m ∈ mRange p n` of `prof(i-m) * prof(j-m)` is the autocorrelation
`Rcorr p (j-i)`.

Since `prof p` is supported on `[-p,p]`, the summand vanishes unless `m ∈ [i-p, i+p]`; this
interval lies inside `mRange p n` because `i ∈ [0, n-1]`.  On `[i-p, i+p]` the substitution
`m = s + i` turns the summand into `prof(-s) * prof(j-i-s) = prof s * prof(s - (j-i))`,
which is exactly `Rcorr p (-(j-i)) = Rcorr p (j-i)` by evenness of the profile.
-/

noncomputable section

open scoped BigOperators
open Finset

namespace Work.UBBInputs3.MatLoc

theorem sum_prof_translate (n p : ℕ) (i j : ℤ)
    (hi : i ∈ Work.UBBInputs3.iRange n) (hj : j ∈ Work.UBBInputs3.iRange n) :
    ∑ m ∈ Work.UBBInputs3.mRange p n,
        Work.UBBInputs3.prof p (i - m) * Work.UBBInputs3.prof p (j - m)
      = Work.UBBInputs3.Rcorr p (j - i) := by
  -- The range hypothesis: `0 ≤ i ≤ n - 1`.
  have hi' : (0 : ℤ) ≤ i ∧ i ≤ (n : ℤ) - 1 := by
    have h := hi
    simp only [Work.UBBInputs3.iRange, Finset.mem_Icc] at h
    exact h
  obtain ⟨hi0, hin⟩ := hi'
  -- The summand, as a named function.
  set G : ℤ → ℝ := fun m => Work.UBBInputs3.prof p (i - m) * Work.UBBInputs3.prof p (j - m) with hG
  -- It vanishes outside the window `[i-p, i+p]`.
  have hzero : ∀ m, m ∉ Finset.Icc (i - (p : ℤ)) (i + (p : ℤ)) → G m = 0 := by
    intro m hm
    have hm' : m < i - (p : ℤ) ∨ i + (p : ℤ) < m := by
      simp only [Finset.mem_Icc, not_and_or, not_le] at hm
      exact hm
    have h1 : (p : ℤ) < |i - m| := by
      rcases hm' with h | h
      · rw [abs_of_pos (by omega : (0 : ℤ) < i - m)]; omega
      · rw [abs_of_neg (by omega : i - m < 0)]; omega
    simp only [hG]
    rw [prof_zero_outside p (i - m) h1, zero_mul]
  -- Restrict the sum from `mRange p n` to the window `[i-p, i+p]`.
  rw [Work.UBBInputs3.mRange]
  rw [sum_Icc_congr_of_eq_zero_outside G (by omega) (by omega) hzero]
  -- Reindex the window sum by `m = s + i`.
  rw [show Finset.Icc (i - (p : ℤ)) (i + (p : ℤ))
        = Finset.Icc (-(p : ℤ) + i) ((p : ℤ) + i) from by congr 1 <;> ring,
      ← sum_Icc_addConst G (-(p : ℤ)) (p : ℤ) i]
  -- Evaluate the summand and identify the result with `Rcorr p (-(j-i))`.
  have hkey : (∑ s ∈ Finset.Icc (-(p : ℤ)) (p : ℤ), G (s + i))
      = Work.UBBInputs3.Rcorr p (-(j - i)) := by
    unfold Work.UBBInputs3.Rcorr
    apply Finset.sum_congr rfl
    intro s hs
    simp only [hG]
    rw [show i - (s + i) = -s by ring,
        show j - (s + i) = -(s + (-(j - i))) by ring,
        prof_neg p s, prof_neg p (s + (-(j - i)))]
  rw [hkey]
  exact Rcorr_even p (j - i)

end Work.UBBInputs3.MatLoc
