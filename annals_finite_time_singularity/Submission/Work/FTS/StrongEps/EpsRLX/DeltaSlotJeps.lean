import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.StrongEps.EpsSpace
import Submission.Work.FTS.StrongEps.EpsSqTools.EpsSqIter_mixed_Jeps_le6
import Submission.Work.FTS.StrongEps.EpsSqTools.EpsSq_mixed_Jeps_le
import Submission.Work.FTS.StrongEps.EpsSqTools.LinAux.LinPartAux
import Submission.Work.FTS.StrongEps.JepsHkMem.AuxMeas

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.EpsRLX

open scoped Real Topology ENNReal
open MeasureTheory Set Filter
open Work.FTS.Galerkin (Fn)

set_option autoImplicit false
set_option maxHeartbeats 1000000

theorem DeltaSlotJeps (ρ : ℝ × ℝ → ℝ) (hρ : Work.FTS.StrongEps.IsSmoothKernel ρ) :
    ∃ C : ℝ, 0 < C ∧ ∀ α ∈ Set.Ioc 0 1, ∀ ε ∈ Set.Ioc 0 1, ∀ {δ : Work.FTS.Galerkin.Fn},
      Work.FTS.EllipticEst.SmoothOpen δ → Work.FTS.StrongEps.EpsMem α δ →
      ∀ b a : ℕ, a + b ≤ 4 →
        Work.FTS.StrongEps.EpsMem α (Work.Spaces.mixed b a (Work.FTS.StrongEps.Jeps ρ ε δ)) ∧
        Work.FTS.StrongEps.EpsSq α (Work.Spaces.mixed b a (Work.FTS.StrongEps.Jeps ρ ε δ))
          ≤ C * (C / ε) ^ (2 * (a + b)) * Work.FTS.StrongEps.EpsSq α δ := by
  obtain ⟨C, hCpos, hIter⟩ := Work.FTS.StrongEps.EpsSqTools.EpsSqIter_mixed_Jeps_le6 ρ hρ
  refine ⟨C, hCpos, ?_⟩
  intro α hα ε hε δ hδsm hδmem b a hab
  have hε0 : 0 < ε := hε.1
  have hδsm' : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry δ) Work.FTS.StrongEps.Quad :=
    (Work.FTS.EllipticEst.smoothOpen_iff_forall δ).mp hδsm
  obtain ⟨-, hlin⟩ := hIter α hα ε hε0 hε.2 δ hδsm' hδmem
  have hkey := hlin b a (by omega : b + a ≤ 6)
  have hab6 : (2 : ℕ) * (b + a) = 2 * (a + b) := by rw [Nat.add_comm b a]
  rw [hab6] at hkey
  constructor
  · exact Work.FTS.StrongEps.EpsSqTools.EpsMem_of_lintegral
      (Work.FTS.StrongEps.EpsSqTools.AK_of_uncurry
        (Work.FTS.StrongEps.JepsHkMem.aestronglyMeasurable_mixed_Jeps hρ.moll hε0 hδsm' b a))
      (lt_of_le_of_lt hkey ENNReal.ofReal_lt_top)
  · refine (ENNReal.ofReal_le_ofReal_iff ?_).mp ?_
    · exact mul_nonneg (mul_nonneg hCpos.le (pow_nonneg (div_nonneg hCpos.le hε0.le) _))
        (Work.FTS.StrongEps.EpsSq_nonneg α δ)
    · exact (Work.FTS.StrongEps.EpsSqTools.ofReal_EpsSq_le_iter α _).trans hkey

end Work.FTS.StrongEps.EpsRLX
