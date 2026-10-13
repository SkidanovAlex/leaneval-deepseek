import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS.TransportS.flat_mixed_le
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.H2.RegQDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Real

namespace Work.FTS.H2.OpenPort

/-- **The `sin(2θ)`-gain of `CoefTh 3`.**  Every mixed derivative `D_z^b D_θ^a f` of a
`C^∞`-datum `f` on the open quadrant with `a ≥ 1` and `a + b ≤ 4` picks up one factor
`sin(2θ)` and is dominated by the flat angular coefficient norm `CoefTh 3 f`.

This combines the σ-gain `Work.FTS.TransportS.flat_mixed_le` (which needs a *uniform* bound
`K` on the mixed derivatives of `∂_θ f` of total order `≤ 3`) with the two facts relating
`CoefThMem 3 f` to the norm `CoefTh 3 f`: a `CoefThMem`-bound is a bound by `supAbsO`
(`Work.FTS.H2.le_supAbsO`), and each `supAbsO` occurring in `CoefTh` is dominated by the
sum itself (`Work.FTS.TransportS.supAbsO_le_coefTh`).  Hence `K := CoefTh 3 f` is admissible
and the conclusion follows. -/
theorem coefTh3_mixed_gain :
    ∃ C : ℝ, 0 < C ∧ ∀ (f : ℝ → ℝ → ℝ), Work.FTS.EllipticEst.SmoothOpen f →
      Work.FTS.VocabO.CoefThMem 3 f →
      ∀ (a b : ℕ), 1 ≤ a → a + b ≤ 4 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < π / 2 →
        |Work.Spaces.mixed b a f z θ| ≤ C * Real.sin (2 * θ) * Work.FTS.VocabO.CoefTh 3 f := by
  obtain ⟨C, hCpos, hC⟩ := Work.FTS.TransportS.flat_mixed_le 3
  refine ⟨C, hCpos, ?_⟩
  intro f hsf hmem a b ha hab z θ hz hθ hθ1
  refine hC f hsf (Work.FTS.VocabO.CoefTh 3 f)
    (Work.FTS.TransportS.coefTh_nonneg 3 f) ?_ a b ha hab z θ hz hθ hθ1
  intro b' i hbi z' θ' hz' hθ' hθ1'
  obtain ⟨K, hK⟩ := hmem b' i hbi
  exact le_trans (Work.FTS.H2.le_supAbsO hz' hθ' hθ1' hK)
    (Work.FTS.TransportS.supAbsO_le_coefTh hbi)

end Work.FTS.H2.OpenPort
