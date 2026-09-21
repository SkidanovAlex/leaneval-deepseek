import Mathlib
import Submission.Work.Analysis.Calculus.exists_smooth_bump_support_Icc_deriv_small

open scoped ContDiff

namespace Work.Odd

/-- A small flat bump: a `C^∞` function supported in `[4/5, 9/10]`, vanishing on an initial
segment `[4/5, 4/5 + η)` of that interval, with all iterated derivatives up to order `K`
bounded by `ε`, and not identically zero. -/
lemma exists_small_flat_bump_smooth (K : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ h : ℝ → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) h ∧
      Function.support h ⊆ Set.Icc (1 - 2 * (1 / 10 : ℝ)) (1 - (1 / 10 : ℝ)) ∧
      h 0 = 0 ∧ h ≠ 0 ∧
      (∃ η : ℝ, 0 < η ∧ ∀ s : ℝ, 1 - 2 * (1 / 10 : ℝ) ≤ s →
        s < 1 - 2 * (1 / 10 : ℝ) + η → h s = 0) ∧
      (∀ k : ℕ, k ≤ K → ∀ s : ℝ, |iteratedDeriv k h s| ≤ ε) := by
  -- We build a bump supported in `[4/5 + 1/100, 9/10]`, which is contained in `[4/5, 9/10]`.
  have hab : (1 - 2 * (1 / 10 : ℝ) + 1 / 100) < (1 - (1 / 10 : ℝ)) := by norm_num
  have h0mem : (0 : ℝ) ∉ Set.Icc (1 - 2 * (1 / 10 : ℝ) + 1 / 100) (1 - (1 / 10 : ℝ)) := by
    intro hmem
    have hpos : (0 : ℝ) < 1 - 2 * (1 / 10 : ℝ) + 1 / 100 := by norm_num
    linarith [hmem.1]
  obtain ⟨h, hh_smooth, _hh_nonneg, hh_supp, hh0, hh_bounds, hh_ne⟩ :=
    Commons.Analysis.Calculus.exists_smooth_bump_support_Icc_deriv_small
      (a := 1 - 2 * (1 / 10 : ℝ) + 1 / 100) (b := 1 - (1 / 10 : ℝ)) hab h0mem K hε
  refine ⟨h, hh_smooth, ?_, hh0, hh_ne, ?_, ?_⟩
  · -- support inside `[4/5, 9/10]`
    intro x hx
    have hx' := hh_supp hx
    have hleft : (1 - 2 * (1 / 10 : ℝ)) ≤ 1 - 2 * (1 / 10 : ℝ) + 1 / 100 := by norm_num
    exact ⟨hleft.trans hx'.1, hx'.2⟩
  · -- vanishing on an initial segment `[4/5, 4/5 + 1/100)`
    refine ⟨1 / 100, by norm_num, ?_⟩
    intro s hs_left hs_right
    by_contra hne
    have hsupp : s ∈ Function.support h := by simpa [Function.mem_support] using hne
    have hs' := hh_supp hsupp
    linarith [hs'.1]
  · intro k hk s
    exact hh_bounds k hk s

end Work.Odd
