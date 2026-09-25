import Mathlib
import Submission.Work.RHContract.Corpus
import Submission.Work.RHContract.A.caLevel_le

/-!
# `Work.RHContract.A.regionII.caNet2_eps_le`

For a colossally abundant number `N_ε` whose largest prime factor `ξ(ε) = caXi ε` is at
least `1530`, the parameter `ε` is at most `g(ξ) = log(1 + 1/ξ)/log ξ`.

Indeed `ξ` is the largest prime in the support `caSupport ε`, so by definition of the
support the exponent `⌊μ(ξ,ε)⌋₊ ≥ 1`, i.e. `μ(ξ,ε) ≥ 1`; by
`Commons.NumberTheory.Robin.caMu_ge_iff_caF` (equivalently `caMu_ge_iff_caFf`) this is
`ε ≤ F(ξ,1)`, and `F(ξ,1) = g(ξ) = caFf 1 ξ = caG ξ` collapses to the asserted
expression.
-/

namespace Work.RHContract.A.regionII

theorem caNet2_eps_le (ε : ℝ) (hε : 0 < ε) (hξ : 1530 ≤ (Work.RHPlan.caXi ε : ℝ)) :
    ε ≤ Real.log (1 + 1 / (Work.RHPlan.caXi ε : ℝ)) / Real.log (Work.RHPlan.caXi ε : ℝ) := by
  have hξne : Work.RHPlan.caXi ε ≠ 0 := by
    intro h0
    rw [h0] at hξ
    norm_num at hξ
  have hne : (Work.RHPlan.caSupport ε).Nonempty := by
    by_contra hc
    rw [Finset.not_nonempty_iff_eq_empty] at hc
    have h0 : Work.RHPlan.caXi ε = 0 := by simp [Work.RHPlan.caXi, hc]
    rw [h0] at hξ
    norm_num at hξ
  have hmax : Work.RHPlan.caXi ε = (Work.RHPlan.caSupport ε).max' hne := by
    rw [Work.RHPlan.caXi, Finset.max'_eq_sup', Finset.sup'_eq_sup hne]
  have hmem : Work.RHPlan.caXi ε ∈ Work.RHPlan.caSupport ε := by
    rw [hmax]
    exact Finset.max'_mem _ hne
  have hmem' : Work.RHPlan.caXi ε ∈
      ((Finset.range (Nat.ceil (Real.exp (2 / ε)) + 2)).filter Nat.Prime).filter
        (fun p : ℕ => 1 ≤ ⌊Work.RHPlan.caMu p ε⌋₊) := by
    simpa [Work.RHPlan.caSupport, Work.RHPlan.caMu] using hmem
  obtain ⟨hmem2, hexp⟩ := Finset.mem_filter.mp hmem'
  have hxprime : Nat.Prime (Work.RHPlan.caXi ε) := (Finset.mem_filter.mp hmem2).2
  have hmuPos : 0 < Work.RHPlan.caMu (Work.RHPlan.caXi ε) ε := by
    have h := Commons.NumberTheory.Robin.caMu_pos (p := Work.RHPlan.caXi ε) (ε := ε)
      hxprime.two_le hε
    simpa [Work.RHPlan.caMu] using h
  have hk_le_mu : ((1 : ℕ) : ℝ) ≤ Work.RHPlan.caMu (Work.RHPlan.caXi ε) ε :=
    le_trans (by exact_mod_cast hexp) (Nat.floor_le (le_of_lt hmuPos))
  have hεFf : ε ≤ Work.RHContract.A.caFf 1 ((Work.RHPlan.caXi ε : ℕ) : ℝ) :=
    (Work.RHContract.A.caMu_ge_iff_caFf (Work.RHPlan.caXi ε) hxprime.two_le ε hε 1 le_rfl).mp
      hk_le_mu
  have hgoal : ε ≤ Work.RHContract.A.caG ((Work.RHPlan.caXi ε : ℕ) : ℝ) := by
    rwa [Work.RHContract.A.caFf_one] at hεFf
  simpa [Work.RHContract.A.caG] using hgoal

end Work.RHContract.A.regionII
