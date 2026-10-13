import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.Spaces.aesm_of_continuousOn_Qd
import Submission.Work.FTS.StrongPersist.N6Trans.SixRoute.pgfAux

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.EpsE4Thr.SlotWt

open MeasureTheory Set
open scoped Real Topology

/-- On the open quadrant `(0,∞) × (0,π/2)` the weight `w(z) ^ 2 * sin(2θ) ^ c` is continuous:
`w z = (1+z)^2 / z^2` is continuous off `z = 0` and `θ ↦ sin(2θ) ^ c` is continuous where
`sin (2θ) > 0`, which on the quadrant is everywhere. -/
theorem continuousOn_w_sq_mul_sin_rpow {c : ℝ} :
    ContinuousOn
      (fun p : ℝ × ℝ => (Work.Spaces.w p.1) ^ 2 * (Real.sin (2 * p.2)) ^ c)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) := by
  have hsinpos : ∀ p ∈ Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (0 : ℝ) (π / 2),
      0 < Real.sin (2 * p.2) := by
    intro p hp
    obtain ⟨-, hθ0, hθ1⟩ := hp
    exact Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos])
  have hsig : ContinuousOn (fun p : ℝ × ℝ => (Real.sin (2 * p.2)) ^ c)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) :=
    ((Real.continuous_sin.comp (continuous_const.mul continuous_snd)).continuousOn).rpow_const
      (fun p hp => Or.inl (ne_of_gt (hsinpos p hp)))
  have hw : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.w p.1)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) := by
    have hfun : (fun p : ℝ × ℝ => Work.Spaces.w p.1)
        = fun p : ℝ × ℝ => (1 + p.1) ^ 2 / p.1 ^ 2 := rfl
    rw [hfun]
    refine ContinuousOn.div ((continuousOn_const.add continuousOn_fst).pow 2)
      (continuousOn_fst.pow 2) (fun p hp => ?_)
    exact pow_ne_zero 2 (ne_of_gt hp.1)
  exact (hw.pow 2).mul hsig

theorem aesm_mixed_pair_weight {c : ℝ} {f h : ℝ → ℝ → ℝ} {j i : ℕ}
    (hsmf : Work.FTS.EllipticEst.SmoothOpen f) (hsmh : Work.FTS.EllipticEst.SmoothOpen h) :
    MeasureTheory.AEStronglyMeasurable
      (fun p : ℝ × ℝ => Work.Spaces.mixed j i f p.1 p.2 * Work.Spaces.mixed j i h p.1 p.2
        * ((Work.Spaces.w p.1) ^ 2 * (Real.sin (2 * p.2)) ^ c))
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) := by
  refine Work.Spaces.aesm_of_continuousOn_Qd _ ?_
  have hf : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.mixed j i f p.1 p.2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) := (hsmf.mixed j i).continuousOn
  have hg : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.mixed j i h p.1 p.2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) := (hsmh.mixed j i).continuousOn
  exact (hf.mul hg).mul continuousOn_w_sq_mul_sin_rpow

end Work.FTS.StrongEps.EpsE4Thr.SlotWt
