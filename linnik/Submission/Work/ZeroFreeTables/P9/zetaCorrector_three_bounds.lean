import Mathlib
import Submission.Work.ZeroFreeTables.Rep9.principalRepair
import Submission.Work.ZeroFreeTables.P9.zetaLogDeriv_pole_split
import Submission.Work.ZeroFreeTables.P9.zetaExtPoleLemmas

open Complex Set Filter
open scoped Topology

noncomputable section

namespace Work.ZeroFreeTables.P9

/-- The `ζ`-corrector `-ζ'/ζ - 1/(s-1)` and its first two derivatives are bounded (in real part,
in absolute value) on the rectangle `1 < Re s ≤ 2`, `|Im s| ≤ 5`.

Since `ζ(s) = φ(s)/(s-1)` with `φ = zetaExtPole` holomorphic and nonzero on the closed rectangle
`1 ≤ Re s ≤ 2`, `|Im s| ≤ 5` (`φ(1) = 1`, and `ζ` has no zeros with `Re ≥ 1`), the corrector agrees
with `-logDeriv φ` on `Re s > 1`; and `logDeriv φ`, together with its first two derivatives, is
analytic — hence continuous — on the open set `zetaExtU ⊇ zetaRect5`, so their real parts are
bounded on the compact rectangle. -/
theorem zetaCorrector_three_bounds :
    ∃ C : ℝ, 0 < C ∧ ∀ s : ℂ, 1 < s.re → s.re ≤ 2 → |s.im| ≤ 5 →
      |(Work.ZeroFreeTables.Rep9.zetaCorrector s).re| ≤ C ∧
      |(iteratedDeriv 1 Work.ZeroFreeTables.Rep9.zetaCorrector s).re| ≤ C ∧
      |(iteratedDeriv 2 Work.ZeroFreeTables.Rep9.zetaCorrector s).re| ≤ C := by
  obtain ⟨C₁, hC₁pos, hC₁⟩ := logDeriv_iteratedDeriv_re_bdd zetaExtPole zetaExtU zetaRect5
    isOpen_zetaExtU isCompact_zetaRect5 zetaRect5_subset_zetaExtU analyticOn_zetaExtPole_of_U
    zetaExtPole_ne_zero_on_U
  refine ⟨C₁, hC₁pos, ?_⟩
  intro s hs1 hs2 hs3
  have hs : s ∈ zetaRect5 := ⟨le_of_lt hs1, hs2, hs3⟩
  obtain ⟨h0, h1, h2⟩ := hC₁ s hs
  obtain ⟨h0l, h0r⟩ := abs_le.mp h0
  obtain ⟨h1l, h1r⟩ := abs_le.mp h1
  obtain ⟨h2l, h2r⟩ := abs_le.mp h2
  -- the corrector agrees, near `s`, with minus the logarithmic derivative of the extension
  have heq : Work.ZeroFreeTables.Rep9.zetaCorrector =ᶠ[𝓝 s]
      fun z => -logDeriv zetaExtPole z := by
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds hs1] with z hz
    change Work.ZeroFreeTables.Rep9.zetaCorrector z = -logDeriv zetaExtPole z
    rw [Work.ZeroFreeTables.Rep9.zetaCorrector, logDeriv_zetaExtPole_eq z hz, one_div]
    ring
  have hd0 : (Work.ZeroFreeTables.Rep9.zetaCorrector s).re = -((logDeriv zetaExtPole s).re) := by
    have h := heq.iteratedDeriv_eq 0
    simp only [iteratedDeriv_zero] at h
    simpa using congrArg Complex.re h
  have hd1 : (iteratedDeriv 1 Work.ZeroFreeTables.Rep9.zetaCorrector s).re
      = -((iteratedDeriv 1 (logDeriv zetaExtPole) s).re) := by
    have h := heq.iteratedDeriv_eq 1
    simp only [iteratedDeriv_fun_neg] at h
    simpa using congrArg Complex.re h
  have hd2 : (iteratedDeriv 2 Work.ZeroFreeTables.Rep9.zetaCorrector s).re
      = -((iteratedDeriv 2 (logDeriv zetaExtPole) s).re) := by
    have h := heq.iteratedDeriv_eq 2
    simp only [iteratedDeriv_fun_neg] at h
    simpa using congrArg Complex.re h
  refine ⟨?_, ?_, ?_⟩
  · rw [hd0, abs_le]
    exact ⟨by linarith, by linarith⟩
  · rw [hd1, abs_le]
    exact ⟨by linarith, by linarith⟩
  · rw [hd2, abs_le]
    exact ⟨by linarith, by linarith⟩

end Work.ZeroFreeTables.P9
