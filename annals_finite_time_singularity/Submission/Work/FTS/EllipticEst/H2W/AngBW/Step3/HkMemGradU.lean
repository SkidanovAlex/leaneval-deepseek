/-
Work module for the Elgindi finite-time-singularity project.

# `H2W.AngBW.S3.hkMem_gradU` — honesty of `z ∂_z u` in the almost-everywhere class

The level-`0` `ℋ`-membership of `D_z u = z ∂_z u` for a datum `AeData α u G`, obtained from the
radial Agmon–Nirenberg interpolation `Work.Blocks.DzVamgm.HkNorm_Dz_amgm 0`
(module `Submission.Work.FTS.EllipticEst.AeS1.DzAgmonClean`, a self-contained and
completely proved copy of the interpolation) applied to
`HkMem α 0 u` (proved in the sibling `Step3/HkMemU.lean`) and `HkMem α 0 (z²∂_z²u)`
(`AeData.memRad2`).

This is the same proof as `Submission/Work/FTS/EllipticEst/H2W/Ae/hkMem_gradU.lean` (and its
sibling `AeS1/HkMemGradU.lean`), carried out against the copy `S3.hkMem_u` so that the module
compiles without the currently unbuildable `H2W/Ae/hkMem_u.lean` in its import cone.
-/
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.H2W.Ae.Defs
import Submission.Work.FTS.EllipticEst.H2W.AngBW.Step3.HkMemU
import Submission.Work.FTS.EllipticEst.AeS1.DzAgmonClean

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology

namespace Work.FTS.EllipticEst.H2W.AngBW.S3

set_option autoImplicit false

theorem hkMem_gradU (α : ℝ) (u G : ℝ → ℝ → ℝ)
    (h : Work.FTS.EllipticEst.H2W.Ae.AeData α u G) :
    Work.Spaces.HkMem α 0 (Work.FTS.EllipticEst.H2W.Ae.grad u) := by
  obtain ⟨C, _hC, hmain⟩ := Work.Blocks.DzVamgm.HkNorm_Dz_amgm 0
  have hα1 : α ≤ 1 := by
    have h4 := h.hα4
    linarith
  have hu : Work.Spaces.HkMem α 0 u := hkMem_u α u G h
  have hgrad : Work.Spaces.HkMem α 0 (Work.Spaces.Dz u) :=
    (hmain α u h.hα hα1 h.smooth hu h.memRad2).1
  exact hgrad

end Work.FTS.EllipticEst.H2W.AngBW.S3
