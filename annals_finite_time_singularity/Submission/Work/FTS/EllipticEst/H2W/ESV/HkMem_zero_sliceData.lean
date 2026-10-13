import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.Spaces.Defs
import Submission.Work.Elliptic.Defs
import Submission.Work.FTS.EllipticEst.TT.WeakDefs
import Submission.Work.FTS.EllipticEst.Defs
import Submission.Work.FTS.EllipticEst.TT.HkMem_descend_open
import Submission.Work.FTS.EllipticEst.H2W.z2pzIter2Comm
import Submission.Work.FTS.EllipticEst.remov.smoothOpen_slices_weak
import Submission.Work.Spaces.DzDthIterCommOn
import Submission.Work.FTS.LocData.HkMem_of_majorant
import Submission.Work.Spaces.HkSq_terms
import Submission.Work.FTS.EllipticEst.DzAmgm.ZsqPz2Comm
import Submission.Work.EllipticEst.H2W.pthIter2_DzIter_comm
import Submission.Work.FTS.EllipticEst.H2W.AeDataAof

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.H2W

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false
set_option maxHeartbeats 800000

/-- The `D_z`-iterates of a datum of the weak class are honest at level `0`.  The `j`-th
radial summand of the honest `ℋ²`-integrand is dominated by the whole integrand, and
continuity of the summand on the open quadrant (which is what the domination lemma needs)
comes from smoothness of `D_z^j` of the three fields of the class. -/
theorem HkMem_zero_sliceData (α : ℝ) (F Ψ : ℝ → ℝ → ℝ)
    (h : Work.FTS.EllipticEst.TT.EllWeakPos α 2 F Ψ) (j : ℕ) (hj : j ≤ 2) :
    Work.Spaces.HkMem α 0 (Work.Spaces.DzIter j F) ∧
      Work.Spaces.HkMem α 0
        (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 (Work.Spaces.DzIter j Ψ) z θ) ∧
      Work.Spaces.HkMem α 0 (Work.Spaces.pthIter 2 (Work.Spaces.DzIter j Ψ)) := by
  -- smoothness of the datum and of its fields on the open quadrant
  have hSΨ : Work.FTS.EllipticEst.SmoothOpen Ψ :=
    (Work.FTS.EllipticEst.smoothOpen_iff_forall Ψ).mpr h.smooth
  obtain ⟨hSFj, hSΨj, hSGj, hSBj⟩ :=
    Work.FTS.EllipticEst.remov.smoothOpen_slices_weak h j
  refine ⟨?_, ?_, ?_⟩
  · -- the source: the `j`-th radial summand of `HkIntegrand α 2 F`
    exact Work.FTS.EllipticEst.H2W.AeDataAofAux.excess_zsummand_mem α 2 j F
      hSFj.continuousOn h.memF hj
  · -- the radial second derivative: the same summand for `z²∂_z²Ψ`, transported along
    -- `z²∂_z²(D_z^jΨ) = D_z^j(z²∂_z²Ψ)` on the open quadrant
    have hG : Work.Spaces.HkMem α 0
        (Work.Spaces.DzIter j (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)) :=
      Work.FTS.EllipticEst.H2W.AeDataAofAux.excess_zsummand_mem α 2 j _
        hSGj.continuousOn h.memA hj
    have hS2 : Work.FTS.EllipticEst.SmoothOpen
        (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 (Work.Spaces.DzIter j Ψ) z θ) :=
      Work.FTS.EllipticEst.H2W.AeDataAofAux.smoothOpen_zsq_mul ((hSΨ.DzIter j).pzIter 2)
    refine Work.FTS.EllipticEst.H2W.AeDataAofAux.HkMem_zero_congr hS2.continuousOn ?_ hG
    intro z θ hz hθ hlt
    have hE := Work.FTS.EllipticEst.DzAmgm.ZsqPz2Comm Ψ hSΨ j 0
      (show ((z, θ) : ℝ × ℝ) ∈ Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2) from ⟨hz, hθ, hlt⟩)
    simpa only [Function.uncurry, Work.Spaces.mixed_zero_right] using hE
  · -- the angular second derivative: the same summand for `∂_θθΨ`, transported along
    -- `∂_θθ(D_z^jΨ) = D_z^j(∂_θθΨ)` on the open quadrant
    have hB : Work.Spaces.HkMem α 0
        (Work.Spaces.DzIter j (Work.Spaces.pthIter 2 Ψ)) :=
      Work.FTS.EllipticEst.H2W.AeDataAofAux.excess_zsummand_mem α 2 j _
        hSBj.continuousOn h.memB hj
    have hS3 : Work.FTS.EllipticEst.SmoothOpen
        (Work.Spaces.pthIter 2 (Work.Spaces.DzIter j Ψ)) :=
      Work.FTS.EllipticEst.Cert.smoothOpen_pthIter_bsl (hSΨ.DzIter j) 2
    refine Work.FTS.EllipticEst.H2W.AeDataAofAux.HkMem_zero_congr hS3.continuousOn ?_ hB
    intro z θ hz hθ hlt
    have hE := Work.EllipticEst.H2W.pthIter2_DzIter_comm hSΨ j
      (show ((z, θ) : ℝ × ℝ) ∈ Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2) from ⟨hz, hθ, hlt⟩)
    simpa only [Function.uncurry] using hE

end Work.FTS.EllipticEst.H2W
