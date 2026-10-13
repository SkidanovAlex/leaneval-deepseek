import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS.CoercivityFix.Assembly.Comm2w
import Submission.Work.FTS.EllipticEst.RegQ.pthU_slot_alg

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Real Topology
open Set

namespace Work.FTS.CoercivityFix.Transfer

theorem BlocksCont_mul_factor (B R : ℝ → ℝ)
    (hB : ContDiffOn ℝ 3 B (Set.Ioo 0 (π / 2)))
    (hR : ContDiffOn ℝ 3 R (Set.Ioi 0)) :
    Work.FTS.CoercivityFix.Assembly.BlocksCont 3 (fun z θ : ℝ => B θ * R z) := by
  intro a b hab
  have hU : IsOpen (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo 0 (π / 2)) := isOpen_Ioi.prod isOpen_Ioo
  -- the separated product is `C^3` on the open quadrant
  have hF : ContDiffOn ℝ 3 (Function.uncurry (fun z θ : ℝ => B θ * R z))
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) := by
    have hfun : Function.uncurry (fun z θ : ℝ => B θ * R z)
        = (fun p : ℝ × ℝ => B p.2) * (fun p : ℝ × ℝ => R p.1) := by
      funext p; rcases p with ⟨z, θ⟩; rfl
    rw [hfun]
    refine ContDiffOn.mul ?_ ?_
    · exact hB.comp contDiffOn_snd (fun p hp => hp.2)
    · exact hR.comp contDiffOn_fst (fun p hp => hp.1)
  have ha : a ≤ 3 := by omega
  have hDth := Work.FTS.EllipticEst.RegQ.Q2.contDiffOn_DthIter_fin
    (G := fun z θ : ℝ => B θ * R z) hU hF a ha
  have hb : b ≤ 3 - a := by omega
  have hDz := Work.FTS.EllipticEst.RegQ.Q2.contDiffOn_DzIter_fin
    (G := Work.Spaces.DthIter a (fun z θ : ℝ => B θ * R z)) hU hDth b hb
  exact hDz.continuousOn

end Work.FTS.CoercivityFix.Transfer
