import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.EpsEngine.ClassCStepEngine
import Submission.Work.FTS.EpsEngine.ThetaFromEpsLeafB.StripFacts
import Submission.Work.FTS.EpsEngine.ThetaFromEpsLeafB.StripPlumb
import Submission.Work.FTS.Galerkin.Inhabit.regPkg_zero

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EpsEngine.ThetaFromEpsLeafB

theorem tendsto_EpsSq_strip {α : ℝ} {g : Work.FTS.Galerkin.Fn} (hg : Work.FTS.StrongEps.EpsMem α g) :
    Filter.Tendsto (fun φ : ℝ => Work.FTS.StrongEps.EpsSq α
        (Work.FTS.EpsEngine.ThetaFromEps.stripLo φ g)) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) ∧
    Filter.Tendsto (fun φ : ℝ => Work.FTS.StrongEps.EpsSq α
        (Work.FTS.EpsEngine.ThetaFromEps.stripHi φ g)) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
  constructor
  · have hfun : (fun φ : ℝ => Work.FTS.StrongEps.EpsSq α
          (Work.FTS.EpsEngine.ThetaFromEps.stripLo φ g))
        = fun φ : ℝ => ∫ p in Work.Spaces.Iz ×ˢ Work.Spaces.Iθ,
            (if p.2 ≤ φ then (g p.1 p.2 * Work.FTS.StrongEps.epsW α p.1 p.2) ^ 2 else 0) :=
      funext fun φ => EpsSq_stripLo_eq α φ g hg
    rw [hfun]
    exact tendsto_setIntegral_Iic
      (F := fun p : ℝ × ℝ => (g p.1 p.2 * Work.FTS.StrongEps.epsW α p.1 p.2) ^ 2) hg
  · have hfun : (fun φ : ℝ => Work.FTS.StrongEps.EpsSq α
          (Work.FTS.EpsEngine.ThetaFromEps.stripHi φ g))
        = fun φ : ℝ => ∫ p in Work.Spaces.Iz ×ˢ Work.Spaces.Iθ,
            (if Real.pi / 2 - φ ≤ p.2 then
              (g p.1 p.2 * Work.FTS.StrongEps.epsW α p.1 p.2) ^ 2 else 0) :=
      funext fun φ => EpsSq_stripHi_eq α φ g hg
    rw [hfun]
    exact Work.FTS.EpsEngine.ThetaFromEpsLeafB.StripIci.tendsto_setIntegral_Ici
      (F := fun p : ℝ × ℝ => (g p.1 p.2 * Work.FTS.StrongEps.epsW α p.1 p.2) ^ 2) hg

end Work.FTS.EpsEngine.ThetaFromEpsLeafB
