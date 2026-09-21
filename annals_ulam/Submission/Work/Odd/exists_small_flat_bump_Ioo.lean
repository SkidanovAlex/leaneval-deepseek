import Mathlib
import Submission.Work.Odd.exists_small_flat_bump_smooth
import Submission.Work.Analysis.Calculus.exists_smooth_bump_support_Icc_deriv_small

open scoped ContDiff

namespace Work.Odd

/-- Given `a < b`, there is a sub interval `[a', b']` strictly inside `(a, b)` which does not
contain `0`. This lets us apply the closed-interval bump construction of
`exists_smooth_bump_support_Icc_deriv_small` (which needs `0 ∉ Icc a' b'`) while landing
strictly inside the open interval `(a, b)`. -/
lemma exists_subinterval_Icc_not_mem_zero (a b : ℝ) (hab : a < b) :
    ∃ a' b' : ℝ, a < a' ∧ a' < b' ∧ b' < b ∧ (0 : ℝ) ∉ Set.Icc a' b' := by
  by_cases ha : (0 : ℝ) ≤ a
  · -- the whole interval is on the nonnegative side: a third/two thirds points stay `> 0`
    refine ⟨(2 * a + b) / 3, (a + 2 * b) / 3, by linarith, by linarith, by linarith, ?_⟩
    intro hmem
    have hpos : 0 < (2 * a + b) / 3 := by linarith
    linarith [hmem.1]
  · have ha_neg : a < 0 := not_le.mp ha
    by_cases hb : b ≤ 0
    · -- the whole interval is on the nonpositive side
      refine ⟨(2 * a + b) / 3, (a + 2 * b) / 3, by linarith, by linarith, by linarith, ?_⟩
      intro hmem
      have hneg : (a + 2 * b) / 3 < 0 := by linarith
      linarith [hmem.2]
    · -- `a < 0 < b`: use two thirds and one third of `a`, which lie in `(a, 0)`
      have hb_pos : 0 < b := not_le.mp hb
      refine ⟨2 * a / 3, a / 3, by linarith, by linarith, by linarith, ?_⟩
      intro hmem
      have hneg : a / 3 < 0 := by linarith
      linarith [hmem.2]

lemma exists_small_flat_bump_Ioo (K : ℕ) (ε : ℝ) (hε : 0 < ε) (a b : ℝ) (hab : a < b) :
    ∃ h : ℝ → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) h ∧
      Function.support h ⊆ Set.Ioo a b ∧ h ≠ 0 ∧
      (∃ η : ℝ, 0 < η ∧ ∀ s : ℝ, a ≤ s → s < a + η → h s = 0) ∧
      (∀ k : ℕ, k ≤ K → ∀ s : ℝ, |iteratedDeriv k h s| ≤ ε) := by
  obtain ⟨a', b', haa', ha'b', hb'b, h0'⟩ := exists_subinterval_Icc_not_mem_zero a b hab
  obtain ⟨h, hh_smooth, _hh_nonneg, hh_supp, _hh0, hh_bounds, hh_ne⟩ :=
    Commons.Analysis.Calculus.exists_smooth_bump_support_Icc_deriv_small ha'b' h0' K hε
  refine ⟨h, hh_smooth, ?_, hh_ne, ?_, ?_⟩
  · -- support inside the open interval `(a, b)`
    intro x hx
    have hx' := hh_supp hx
    exact ⟨lt_of_lt_of_le haa' hx'.1, lt_of_le_of_lt hx'.2 hb'b⟩
  · -- flat on the initial segment `[a, a + (a' - a))`
    refine ⟨a' - a, by linarith, ?_⟩
    intro s _hs_left hs_right
    by_contra hne
    have hs_supp : s ∈ Function.support h := by simpa [Function.mem_support] using hne
    have hs' := hh_supp hs_supp
    linarith [hs'.1]
  · -- derivative bounds, inherited from the closed-interval construction
    intro k hk s
    exact hh_bounds k hk s

end Work.Odd
