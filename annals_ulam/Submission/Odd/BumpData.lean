import Mathlib
import Submission.Work.Odd.exists_small_flat_bump_Ioo

/-!
# The perturbation `h` of the odd-dimensional construction

The perturbation function `h` of Ryabogin's odd-dimensional argument is a smooth bump
supported in the window `[1 - 2τ, 1 - τ]` (`τ = 1/10`), flat at the left edge of the window,
whose derivatives up to a fixed order are as small as one pleases.  This file packages the
construction of `Work.Odd.exists_small_flat_bump_Ioo` in the form in which the odd-dimensional
arguments consume it.
-/

namespace Submission.Odd

open scoped ContDiff

set_option autoImplicit false

/-- There is a nonzero smooth bump `h` with support inside `(1 - 2τ, 1 - τ)`, flat on a
right neighbourhood of the left edge of the window, with `h` and its first `K` derivatives
bounded by `ε` in absolute value. -/
theorem exists_odd_bump (K : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ h : ℝ → ℝ, ContDiff ℝ ∞ h ∧
      Function.support h ⊆ Set.Ioo (1 - 2 * (1 / 10 : ℝ)) (1 - (1 / 10 : ℝ)) ∧
      Function.support h ⊆ Set.Icc (1 - 2 * (1 / 10 : ℝ)) (1 - (1 / 10 : ℝ)) ∧
      h ≠ 0 ∧ h 0 = 0 ∧
      (∃ η : ℝ, 0 < η ∧ ∀ s : ℝ, 1 - 2 * (1 / 10 : ℝ) ≤ s →
        s < 1 - 2 * (1 / 10 : ℝ) + η → h s = 0) ∧
      (∀ k : ℕ, k ≤ K → ∀ s : ℝ, |iteratedDeriv k h s| ≤ ε) ∧
      (∃ s : ℝ, 0 < s ∧ h s ≠ 0) := by
  obtain ⟨h, hh, hsupp, hne, hflat, hbnd⟩ :=
    Work.Odd.exists_small_flat_bump_Ioo K ε hε (1 - 2 * (1 / 10 : ℝ)) (1 - (1 / 10 : ℝ))
      (by norm_num)
  have hsuppIcc : Function.support h ⊆ Set.Icc (1 - 2 * (1 / 10 : ℝ)) (1 - (1 / 10 : ℝ)) :=
    fun s hs => ⟨le_of_lt (hsupp hs).1, le_of_lt (hsupp hs).2⟩
  refine ⟨h, hh, hsupp, hsuppIcc, hne, ?_, hflat, hbnd, ?_⟩
  · by_contra hc
    exact hc (by
      have h0mem : (0 : ℝ) ∈ Function.support h := by simpa [Function.mem_support] using hc
      have h0' := hsupp h0mem
      linarith [h0'.1])
  · obtain ⟨s, hs⟩ := Function.ne_iff.mp hne
    have hmem : s ∈ Function.support h := by simpa [Function.mem_support] using hs
    have hs' := hsupp hmem
    exact ⟨s, by linarith [hs'.1], hs⟩

end Submission.Odd
