import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.EllipticEst.H2W.Ae.Defs
import Submission.Work.FTS.EllipticEst.AngAWeak.Basic
import Submission.Work.FTS.EllipticEst.Cores.AeStep2Aux.aeMixedAe_mem
import Submission.Work.FTS.EllipticEst.Cores.AeStep2Aux.i1Paper_weakMixed
import Submission.Work.FTS.EllipticEst.H2W.AngBW.Chain.Step2Assembly

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.Cores.AeStep2Aux

theorem aeI1_fts : ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ) (u G : ℝ → ℝ → ℝ),
    Work.FTS.EllipticEst.H2W.Ae.AeData α u G →
      Work.Spaces.HkMem α 0 (fun z θ => z * Work.Spaces.pz u z θ) →
      - C * α ^ 2 *
          (Work.FTS.EllipticEst.AngSecond.IP (fun z θ => z * Work.Spaces.pz u z θ)
              (fun z θ => z * Work.Spaces.pz u z θ)
            + Real.sqrt (Work.FTS.EllipticEst.AngSecond.IP
                  (fun z θ => z * Work.Spaces.pz u z θ)
                  (fun z θ => z * Work.Spaces.pz u z θ))
              * Real.sqrt (Work.FTS.EllipticEst.AngSecond.IP (Work.Spaces.pthIter 2 u)
                    (Work.Spaces.pthIter 2 u)))
        ≤ α ^ 2 * Work.FTS.EllipticEst.AngSecond.IP
            (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 u z θ) (Work.Spaces.pthIter 2 u) := by
  -- The `I₁` bound with its positive term (`remov.AeI1Paper`), from the paper's computation
  -- run with the *weakened* mixed slot (`i1Paper_weakMixed`), whose hypotheses are supplied by
  -- `aeMixedAe_mem`.
  have hPaper : Work.FTS.EllipticEst.remov.AeI1Paper := by
    obtain ⟨C, hC, h⟩ := i1Paper_weakMixed
    refine ⟨C, hC, fun α u G hA hU => ?_⟩
    obtain ⟨hmix1, hmix2⟩ := aeMixedAe_mem α u G hA hU
    exact h α u G hA hU hmix1 hmix2
  -- Dropping the non-negative positive term gives the target.
  exact Work.FTS.EllipticEst.H2W.AngBW.i1Bare_of_paper hPaper

end Work.FTS.EllipticEst.Cores.AeStep2Aux
