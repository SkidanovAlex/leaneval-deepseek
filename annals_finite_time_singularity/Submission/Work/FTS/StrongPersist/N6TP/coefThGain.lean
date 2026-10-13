import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS.TransportS.flat_mixed_le
import Submission.Work.FTS.TransportS.Defs
import Submission.Work.FTS.H2.RegQDefs
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.Spaces.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.N6TP

theorem coefThGain : ∃ C : ℝ, 0 < C ∧ ∀ (f : ℝ → ℝ → ℝ), Work.FTS.EllipticEst.SmoothOpen f →
    Work.FTS.VocabO.CoefThMem 5 f →
    ∀ (a b : ℕ), 1 ≤ a → a + b ≤ 6 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      |Work.Spaces.mixed b a f z θ| ≤ C * Real.sin (2 * θ) * Work.FTS.VocabO.CoefTh 5 f := by
  obtain ⟨C, hCpos, hle⟩ := Work.FTS.TransportS.flat_mixed_le 5
  refine ⟨C, hCpos, fun f hsm hcf a b ha hab z θ hz hθ hθ1 => ?_⟩
  refine hle f hsm (Work.FTS.VocabO.CoefTh 5 f)
    (Work.FTS.TransportS.coefTh_nonneg 5 f) ?_ a b ha hab z θ hz hθ hθ1
  intro b' i hbi z' θ' hz' hθ' hθ1'
  obtain ⟨K, hK⟩ := hcf b' i hbi
  exact le_trans (Work.FTS.H2.le_supAbsO hz' hθ' hθ1' hK)
    (Work.FTS.TransportS.supAbsO_le_coefTh hbi)

end Work.FTS.StrongPersist.N6TP
