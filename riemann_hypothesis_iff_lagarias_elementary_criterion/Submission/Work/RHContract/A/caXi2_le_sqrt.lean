import Mathlib
import Submission.Work.RHContract.Corpus
import Submission.Work.RHContract.MarginDefs
import Submission.Work.RHContract.A.caLevel_le

/-!
# `caXi2_le_sqrt`

`ξ₂(ε) = caXi2 ε` is the largest prime whose colossally abundant exponent is `≥ 2`.
Writing `caLevel ε 2` for the largest prime `< K(ε)` with exponent `≥ 2`
(`K(ε) = ⌈e^{2/ε}⌉ + 2` is the range bound of the CA product), the two are *the same*
finset construction: `caXi2` filters the support `{p < K(ε) prime : 1 ≤ ⌊μ(p,ε)⌋₊}`
by `2 ≤ ⌊μ(p,ε)⌋₊`, and `2 ≤ n` implies `1 ≤ n`, so

`caXi2 ε = caLevel ε 2`.

The level-`2` cut-off obeys the classical bound `caLevel ε 2 ≤ √(2.46·ξ)` proved in
`caLevel_le` (`k = 2`), and `√(2.46·ξ) ≤ √(2.5·ξ) ≤ √(2.5·ξ) + 1` for `ξ ≥ 1530 > 0`.
-/

namespace Work.RHContract.A

/-- `ξ₂(ε)` coincides with the level-`2` cut-off of the CA parametrisation: filtering the
support by `2 ≤ ⌊μ(p,ε)⌋₊` is the same as filtering the full prime range
`p < K(ε) = ⌈e^{2/ε}⌉ + 2` by it, since an exponent `≥ 2` is in particular `≥ 1`. -/
lemma caXi2_eq_caLevel_two (ε : ℝ) :
    Work.RHContract.Margin.caXi2 ε = caLevel ε 2 := by
  rw [Work.RHContract.Margin.caXi2, caLevel, Work.RHPlan.caSupport, caK, Finset.filter_filter]
  congr 1
  exact Finset.filter_congr
    (fun p _ => ⟨fun h => h.2, fun h => ⟨le_trans (by norm_num : 1 ≤ 2) h, h⟩⟩)

theorem caXi2_le_sqrt (ε : ℝ) (hε : 0 < ε) (hξ : 1530 ≤ (Work.RHPlan.caXi ε : ℝ)) :
    (Work.RHContract.Margin.caXi2 ε : ℝ) ≤ Real.sqrt (2.5 * (Work.RHPlan.caXi ε : ℝ)) + 1 := by
  rw [caXi2_eq_caLevel_two ε]
  set ξ : ℝ := (Work.RHPlan.caXi ε : ℝ) with hξdef
  have hξ1530 : 1530 ≤ ξ := hξ
  -- the level-`2` bound of `caLevel_le`
  have hle := caLevel_le ε hε hξ 2 (le_refl 2)
  rw [← hξdef] at hle
  -- turn the `(·) ^ (1/2)` into a square root
  have hcast2 : ((2 : ℕ) : ℝ) = (2 : ℝ) := by norm_num
  have h2 : (1.23 * ((2 : ℕ) : ℝ) * ξ) ^ (1 / ((2 : ℕ) : ℝ)) = Real.sqrt (1.23 * 2 * ξ) := by
    rw [hcast2]
    exact (Real.sqrt_eq_rpow _).symm
  rw [h2] at hle
  have h3 : Real.sqrt (1.23 * 2 * ξ) ≤ Real.sqrt (2.5 * ξ) := by
    apply Real.sqrt_le_sqrt
    nlinarith [hξ1530]
  have h4 : Real.sqrt (2.5 * ξ) ≤ Real.sqrt (2.5 * ξ) + 1 := by linarith
  linarith [hle, h3, h4]

end Work.RHContract.A
