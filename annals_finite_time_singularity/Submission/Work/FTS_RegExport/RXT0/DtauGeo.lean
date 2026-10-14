import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS_EllLimOK.Decay.DecayTools
import Submission.Work.FTS_RegExport.RXT.Sys.hasDerivAt_mixed_theta
import Submission.Work.FTS_RegExport.RXT.Sys.hasDerivAt_mixed_z
import Submission.Work.FTS_RegExport.RXT.st1_of_weighted
import Submission.Work.FTS_RegExport.RXT0.RHSJetsJointCont

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS_RegExport.RXT0.DtauGeo` — the Fréchet-derivative data of the slot map

For `β = (b,a)`, `a + b ≤ 2`, the spatial slice `(z,θ) ↦ D_z^bD_θ^a g(z,θ,τ)` is `C¹` on the
open quadrant (from the `C⁴`-regularity `RegPkgMin.c4`) with the explicit derivative `Lfun …`,
and that derivative is jointly continuous on the slab `z > 0, 0 < θ < π/2, τ ∈ [0,S]` (from
`jc3`).  These are the `hd`/`hL` hypotheses of `RXT0.slabC1`.
-/

noncomputable section
open scoped Real Topology NNReal
open Set Filter MeasureTheory

namespace Work.FTS_RegExport.RXT0

open Work.FTS.Galerkin (Fn Fam slice gdot)
open Work.FTS.Regularity (pExp)
open Work.FTS.FinalV2 (DynOK' Sol)
open Work.FTS.RegExportIface

set_option autoImplicit false

variable {α C₀ Ce Cs : ℝ} {Φs : Fn} {E : Fn →ₗ[ℝ] Fn} {g : Fam}

/-- The candidate spatial Fréchet derivative of the slot map `(z,θ) ↦ D_z^bD_θ^a g(z,θ,τ)`. -/
noncomputable def Lfun (g : Fam) (b a : ℕ) (p : ℝ × ℝ × ℝ) : (ℝ × ℝ) →L[ℝ] ℝ :=
  Work.FTS.PhiStar.Series.SmoothAux.cclm
    (Work.Spaces.mixed (b + 1) a (slice g p.2.2) p.1 p.2.1 / p.1,
     Work.Spaces.mixed b (a + 1) (slice g p.2.2) p.1 p.2.1 / Real.sin (2 * p.2.1))



end Work.FTS_RegExport.RXT0
