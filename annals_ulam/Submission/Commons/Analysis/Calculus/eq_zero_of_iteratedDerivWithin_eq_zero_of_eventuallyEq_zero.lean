import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Calculus.Taylor

namespace Commons.Analysis.Calculus

open scoped ContDiff
open Set Filter Topology

/-- If `F` is `C^{n+1}` on `[a,b]`, has vanishing `(n+1)`-st derivative on `(a,b)`, and vanishes on a
neighbourhood of an interior point `c`, then `F` vanishes on `[a,b]`.

(Taylor's formula with the Lagrange remainder at `c`: the Taylor polynomial of degree `n+1` at `c`
vanishes because `F ≡ 0` near `c`, and so does the remainder because `F^{(n+1)} = 0`.) -/
theorem eq_zero_of_iteratedDerivWithin_eq_zero_of_eventuallyEq_zero
    (n : ℕ) {a c b : ℝ} (hac : a < c) (hcb : c < b) {F : ℝ → ℝ}
    (hF : ContDiffOn ℝ (n + 1) F (Set.Icc a b))
    (hd : ∀ s ∈ Set.Ioo a b, iteratedDerivWithin (n + 1) F (Set.Icc a b) s = 0)
    (hz : F =ᶠ[𝓝 c] 0) :
    ∀ s ∈ Set.Icc a b, F s = 0 := by
  have hab : a < b := lt_trans hac hcb
  intro s hs
  rcases eq_or_ne s c with rfl | hne
  · exact hz.eq_of_nhds
  have hsub : Set.uIcc c s ⊆ Set.Icc a b := by
    rcases lt_or_ge s c with hsc | hcs
    · rw [Set.uIcc_of_ge hsc.le]
      intro x hx
      exact ⟨le_trans hs.1 hx.1, le_trans hx.2 hcb.le⟩
    · rw [Set.uIcc_of_le hcs]
      intro x hx
      exact ⟨le_trans hac.le hx.1, le_trans hx.2 hs.2⟩
  have hsub2 : Set.uIoo c s ⊆ Set.Ioo a b := by
    rcases lt_or_ge s c with hsc | hcs
    · rw [Set.uIoo_of_ge hsc.le]
      intro x hx
      exact ⟨lt_of_le_of_lt hs.1 hx.1, lt_of_lt_of_le hx.2 hcb.le⟩
    · rw [Set.uIoo_of_le hcs]
      intro x hx
      exact ⟨lt_trans hac hx.1, lt_of_lt_of_le hx.2 hs.2⟩
  have hf : ContDiffOn ℝ (n + 1) F (Set.uIcc c s) := hF.mono hsub
  obtain ⟨x', hx', heq⟩ :=
    taylor_mean_remainder_lagrange_iteratedDeriv (f := F) (x := s) (x₀ := c) (n := n)
      hne.symm hf
  have hx'ab : x' ∈ Set.Ioo a b := hsub2 hx'
  have hcont : ContDiffAt ℝ (n + 1) F x' :=
    hF.contDiffAt (Icc_mem_nhds_iff.2 hx'ab)
  have huniq : UniqueDiffOn ℝ (Set.Icc a b) := uniqueDiffOn_Icc hab
  have hxd : iteratedDeriv (n + 1) F x' = iteratedDerivWithin (n + 1) F (Set.Icc a b) x' :=
    (iteratedDerivWithin_eq_iteratedDeriv huniq hcont ⟨hx'ab.1.le, hx'ab.2.le⟩).symm
  have hderiv_zero : iteratedDeriv (n + 1) F x' = 0 := by
    rw [hxd, hd x' hx'ab]
  have hpoly : taylorWithinEval F n (Set.uIcc c s) c s = 0 := by
    rw [taylor_within_apply]
    refine Finset.sum_eq_zero fun k _ => ?_
    have hzero : iteratedDerivWithin k F (Set.uIcc c s) c = 0 := by
      have h1 : F =ᶠ[𝓝[Set.uIcc c s] c] (0 : ℝ → ℝ) := hz.filter_mono nhdsWithin_le_nhds
      have h2 : F c = (0 : ℝ → ℝ) c := hz.eq_of_nhds
      rw [h1.iteratedDerivWithin_eq (n := k) h2]
      simp
    rw [hzero, smul_zero]
  have heq' : F s - taylorWithinEval F n (Set.uIcc c s) c s = 0 := by
    rw [heq, hderiv_zero]
    simp
  rw [hpoly, sub_zero] at heq'
  exact heq'

end Commons.Analysis.Calculus