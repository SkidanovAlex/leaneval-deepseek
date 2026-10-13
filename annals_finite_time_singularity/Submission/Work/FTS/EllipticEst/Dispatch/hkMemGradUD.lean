/-
Copyright: work module for the Elgindi finite-time singularity project.

# Honesty of `z ∂_z u` in the almost-everywhere class, with a self-contained import cone

`Work.FTS.EllipticEst.Dispatch.hkMem_gradUD`: for every datum `AeData α u G` of the
almost-everywhere class of the level-`0` elliptic estimate,
`Work.Spaces.HkMem α 0 (fun z θ => z * Work.Spaces.pz u z θ)`.

This is the statement of `Work.FTS.EllipticEst.H2W.Ae.hkMem_gradU`, proved here on top of the
*clean* copy `Work.FTS.EllipticEst.Dispatch.hkMem_uM` of `HkMem α 0 u` (whose import cone avoids
`Honest.firstOrderHonest`, which currently fails to build because it imports both copies of
`Honest.contDiffOn_slice`) and the self-contained Agmon–Nirenberg interpolation
`Work.Blocks.DzVamgm.HkNorm_Dz_amgm`.
-/
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.H2W.Ae.Defs
import Submission.Work.FTS.EllipticEst.Dispatch.hkMemUD
import Submission.Work.FTS.EllipticEst.AeS1.DzAgmonClean

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology

namespace Work.FTS.EllipticEst.Dispatch

set_option autoImplicit false

theorem hkMem_gradUD (α : ℝ) (u G : ℝ → ℝ → ℝ)
    (h : Work.FTS.EllipticEst.H2W.Ae.AeData α u G) :
    Work.Spaces.HkMem α 0 (Work.FTS.EllipticEst.H2W.Ae.grad u) := by
  obtain ⟨C, _hC, hmain⟩ := Work.Blocks.DzVamgm.HkNorm_Dz_amgm 0
  have hα1 : α ≤ 1 := by
    have h4 := h.hα4
    linarith
  have hu : Work.Spaces.HkMem α 0 u := hkMem_uM α u G h
  have hgrad : Work.Spaces.HkMem α 0 (Work.Spaces.Dz u) :=
    (hmain α u h.hα hα1 h.smooth hu h.memRad2).1
  exact hgrad

end Work.FTS.EllipticEst.Dispatch
