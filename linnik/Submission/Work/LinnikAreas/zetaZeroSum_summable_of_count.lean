import Mathlib
import Submission.Work.LinnikAreas.ZetaDev
import Submission.Commons.Analysis.InfiniteSum.summable_of_finset_tail_bound

namespace Work.LinnikAreas

open Complex
open scoped BigOperators

/-- Pointwise inverse-square bound for the Heath-Brown kernel `zetaHk q` at a zero of the
completed Riemann zeta function `Ξ = xiF`.  All zeros of `Ξ` lie in the closed critical strip
`0 ≤ Re u ≤ 1`, where `norm_Hk_strip_bound` applies. -/
private lemma norm_zetaHk_le_of_xiF_zero (q : ℕ) (hq : 2 ≤ q) {u : ℂ}
    (hzu : Commons.NumberTheory.Zeta.XiPF.xiF u = 0) :
    ‖zetaHk q u‖ ≤ max (5 * ((3 : ℝ) / 10) ^ 2) (20 / (Real.log (q : ℝ)) ^ 2) *
      (1 / (1 + ‖u‖ ^ 2)) := by
  have hstrip : u.re ≤ 1 :=
    (Commons.NumberTheory.Zeta.xiE_LG_zeros_strip
      (show Commons.NumberTheory.Zeta.xiE_LG u = 0 from hzu)).2
  exact norm_Hk_strip_bound q hq hstrip

theorem zetaZeroSum_summable_of_count (q : ℕ) (hq : 2 ≤ q) {C : ℝ}
    (hcount : ∀ s : Finset ℂ,
      Finset.sum s (fun u => (analyticOrderNatAt Commons.NumberTheory.Zeta.XiPF.xiF u : ℝ) *
        (1 / (1 + ‖u‖ ^ 2))) ≤ C) :
    Summable (fun u : ℂ => (analyticOrderNatAt Commons.NumberTheory.Zeta.XiPF.xiF u : ℂ) *
      Work.LinnikAreas.zetaHk q u) := by
  set M : ℝ := max (5 * ((3 : ℝ) / 10) ^ 2) (20 / (Real.log (q : ℝ)) ^ 2) with hMdef
  have hMnn : 0 ≤ M := by
    rw [hMdef]
    exact le_trans (by norm_num : (0 : ℝ) ≤ 5 * ((3 : ℝ) / 10) ^ 2) (le_max_left _ _)
  set f : ℂ → ℝ :=
    (fun u => (analyticOrderNatAt Commons.NumberTheory.Zeta.XiPF.xiF u : ℝ) * ‖zetaHk q u‖)
    with hfdef
  have hfnn : ∀ u : ℂ, 0 ≤ f u := by
    intro u
    rw [hfdef]
    exact mul_nonneg (Nat.cast_nonneg _) (norm_nonneg _)
  -- Finiteness of the zeros of `Ξ` in the closed disc of radius `2`.
  have hfin : ({u : ℂ | Commons.NumberTheory.Zeta.XiPF.xiF u = 0 ∧ ‖u‖ ≤ 2} : Set ℂ).Finite :=
    Commons.NumberTheory.Zeta.XiPF.xiF_zeroSet_finite (by norm_num)
  -- The low part of the sum: all terms outside the small zero set vanish.
  have hsmall : ∃ c : ℝ, ∀ s : Finset ℂ, (∀ u ∈ s, ‖u‖ ≤ 2) → ∑ u ∈ s, f u ≤ c := by
    refine ⟨∑ u ∈ hfin.toFinset, f u, ?_⟩
    intro s hs
    have hZmem : ∀ u : ℂ, u ∈ hfin.toFinset ↔
        Commons.NumberTheory.Zeta.XiPF.xiF u = 0 ∧ ‖u‖ ≤ 2 :=
      fun u => hfin.mem_toFinset
    have hzero : ∀ u ∈ s ∪ hfin.toFinset, u ∉ hfin.toFinset → f u = 0 := by
      intro u hu huz
      have hord : analyticOrderNatAt Commons.NumberTheory.Zeta.XiPF.xiF u = 0 := by
        by_contra hne
        have hzu : Commons.NumberTheory.Zeta.XiPF.xiF u = 0 :=
          apply_eq_zero_of_analyticOrderNatAt_ne_zero hne
        have hnorm : ‖u‖ ≤ 2 := by
          rcases Finset.mem_union.mp hu with h | h
          · exact hs u h
          · exact absurd h huz
        exact huz ((hZmem u).mpr ⟨hzu, hnorm⟩)
      rw [hfdef]
      simp [hord]
    calc ∑ u ∈ s, f u ≤ ∑ u ∈ s ∪ hfin.toFinset, f u :=
          Finset.sum_le_sum_of_subset_of_nonneg Finset.subset_union_left
            (fun i _ _ => hfnn i)
      _ = ∑ u ∈ hfin.toFinset, f u :=
          (Finset.sum_subset (s₁ := hfin.toFinset) (s₂ := s ∪ hfin.toFinset)
            Finset.subset_union_right hzero).symm
  -- The high part: dominated by the counting hypothesis.
  have htail : ∀ s : Finset ℂ, (∀ u ∈ s, 2 < ‖u‖) → ∑ u ∈ s, f u ≤ M * C := by
    intro s _
    have hpt : ∀ u ∈ s, f u ≤ M * ((analyticOrderNatAt Commons.NumberTheory.Zeta.XiPF.xiF u : ℝ) *
        (1 / (1 + ‖u‖ ^ 2))) := by
      intro u _
      by_cases h0 : analyticOrderNatAt Commons.NumberTheory.Zeta.XiPF.xiF u = 0
      · rw [hfdef]
        simp [h0]
      · have hzu : Commons.NumberTheory.Zeta.XiPF.xiF u = 0 :=
          apply_eq_zero_of_analyticOrderNatAt_ne_zero h0
        have hb := norm_zetaHk_le_of_xiF_zero q hq hzu
        rw [hfdef]
        calc (analyticOrderNatAt Commons.NumberTheory.Zeta.XiPF.xiF u : ℝ) * ‖zetaHk q u‖
            ≤ (analyticOrderNatAt Commons.NumberTheory.Zeta.XiPF.xiF u : ℝ) *
                (M * (1 / (1 + ‖u‖ ^ 2))) :=
              mul_le_mul_of_nonneg_left hb (Nat.cast_nonneg _)
          _ = M * ((analyticOrderNatAt Commons.NumberTheory.Zeta.XiPF.xiF u : ℝ) *
                (1 / (1 + ‖u‖ ^ 2))) := by ring
    calc ∑ u ∈ s, f u
        ≤ ∑ u ∈ s, M * ((analyticOrderNatAt Commons.NumberTheory.Zeta.XiPF.xiF u : ℝ) *
            (1 / (1 + ‖u‖ ^ 2))) := Finset.sum_le_sum hpt
      _ = M * ∑ u ∈ s, (analyticOrderNatAt Commons.NumberTheory.Zeta.XiPF.xiF u : ℝ) *
            (1 / (1 + ‖u‖ ^ 2)) := by rw [Finset.mul_sum]
      _ ≤ M * C := mul_le_mul_of_nonneg_left (hcount s) hMnn
  have hsumR : Summable f :=
    Commons.Analysis.InfiniteSum.summable_of_finset_tail_bound hfnn hsmall htail
  have hf_eq : f = fun u : ℂ => ‖(analyticOrderNatAt Commons.NumberTheory.Zeta.XiPF.xiF u : ℂ) *
      Work.LinnikAreas.zetaHk q u‖ := by
    rw [hfdef]
    funext u
    rw [norm_mul, Complex.norm_natCast]
  rw [hf_eq] at hsumR
  exact hsumR.of_norm

end Work.LinnikAreas
