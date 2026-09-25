import Mathlib
import Submission.Work.RHContract.Corpus

namespace Work.RHContract.A

/-- Every prime `p` with `ξ₂(ε) < p ≤ ξ(ε)` has colossally-abundant exponent exactly `1`.

The proof has three parts.

* The support `caSupport ε` is nonempty (otherwise `caXi ε = 0 < 2 ≤ p`), so `caXi ε` is
  the (true) maximum of the support; in particular `caXi ε ∈ caSupport ε` and hence
  `1 ≤ ⌊caMu (caXi ε) ε⌋₊`, while `caXi ε < ⌈e^{2/ε}⌉ + 2`.
* Since the CA exponent is non-increasing in the prime
  (`Commons.NumberTheory.Robin.caExp_anti_p`), `p ≤ caXi ε` gives
  `1 ≤ ⌊caMu p ε⌋₊`.
* If `2 ≤ ⌊caMu p ε⌋₊` then `p` lies in the exponent-`≥ 2` sub-support of `caXi2 ε`,
  so `p ≤ caXi2 ε`, contradicting `caXi2 ε < p`.

Hence `⌊caMu p ε⌋₊ ≥ 1` and `⌊caMu p ε⌋₊ < 2`, i.e. `⌊caMu p ε⌋₊ = 1`. -/
theorem ca_exp_eq_one_of_gt_xi2 (ε : ℝ) (hε : 0 < ε) (hξ : 1530 ≤ (Work.RHPlan.caXi ε : ℝ))
    {p : ℕ} (hp : Nat.Prime p) (h1 : Work.RHContract.Margin.caXi2 ε < p)
    (h2 : p ≤ Work.RHPlan.caXi ε) : ⌊Work.RHPlan.caMu p ε⌋₊ = 1 := by
  have hp2 : 2 ≤ p := hp.two_le
  -- the support is nonempty, since `p` is a prime below `caXi ε`
  have hne : (Work.RHPlan.caSupport ε).Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hempty
    have hzero : Work.RHPlan.caXi ε = 0 := by
      rw [Work.RHPlan.caXi, hempty]
      simp
    omega
  -- `caXi ε` is the maximum of the support, so it lies in it
  have hxisup : Work.RHPlan.caXi ε = (Work.RHPlan.caSupport ε).max' hne := by
    rw [Work.RHPlan.caXi]
    rw [← Finset.sup'_eq_sup hne id, ← Finset.max'_eq_sup']
  have hximem : Work.RHPlan.caXi ε ∈ Work.RHPlan.caSupport ε := by
    rw [hxisup]; exact Finset.max'_mem _ hne
  have hxi_exp : 1 ≤ ⌊Work.RHPlan.caMu (Work.RHPlan.caXi ε) ε⌋₊ := by
    have h := (Finset.mem_filter.mp hximem).2
    simpa only [Work.RHPlan.caMu] using h
  have hxi_lt_B : Work.RHPlan.caXi ε < Nat.ceil (Real.exp (2 / ε)) + 2 :=
    Finset.mem_range.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hximem).1).1
  -- lower bound: monotonicity of the exponent in the prime
  have hlow : 1 ≤ ⌊Work.RHPlan.caMu p ε⌋₊ := by
    rcases eq_or_lt_of_le h2 with h | h
    · rw [h]; exact hxi_exp
    · have hq2 : 2 ≤ Work.RHPlan.caXi ε := le_trans hp2 h2
      have hmono : ⌊Work.RHPlan.caMu (Work.RHPlan.caXi ε) ε⌋₊ ≤ ⌊Work.RHPlan.caMu p ε⌋₊ := by
        simpa only [Work.RHPlan.caMu] using
          Commons.NumberTheory.Robin.caExp_anti_p (p := p) (q := Work.RHPlan.caXi ε)
            (ε := ε) hp2 hq2 hε h
      exact le_trans hxi_exp hmono
  -- upper bound: `p` lies above the exponent-`≥ 2` sub-support
  have hup : ¬ 2 ≤ ⌊Work.RHPlan.caMu p ε⌋₊ := by
    intro h2le
    have hp_mem : p ∈ Work.RHPlan.caSupport ε := by
      refine Finset.mem_filter.mpr ⟨?_, ?_⟩
      · exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (lt_of_le_of_lt h2 hxi_lt_B), hp⟩
      · simpa only [Work.RHPlan.caMu] using hlow
    have hpξ2 : p ∈ (Work.RHPlan.caSupport ε).filter (fun q => 2 ≤ ⌊Work.RHPlan.caMu q ε⌋₊) :=
      Finset.mem_filter.mpr ⟨hp_mem, h2le⟩
    have hle : p ≤ Work.RHContract.Margin.caXi2 ε := by
      rw [Work.RHContract.Margin.caXi2]
      exact Finset.le_sup (f := id) hpξ2
    omega
  omega

end Work.RHContract.A
