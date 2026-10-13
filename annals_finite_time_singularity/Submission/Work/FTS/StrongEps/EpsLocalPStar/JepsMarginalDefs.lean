/-
Copyright: work module for the Elgindi finite-time singularity project.

# `EpsLocalPStar/JepsMarginalDefs.lean` — the weighted angular energy `Ibd`

The quantity

  `Ibd α f z = ∫_{Iθ} sin(2σ)^{2-γ} (∂_θ f z σ)² dσ`   (`γ = gam α = 1 + α/10`)

is the weighted angular energy of the `z`-slice of `f` which appears on the right-hand side of
the boundary bound `hbd` of `JepsMarginalZero_{zero,Pi}` (it is the `L²`-factor produced by the
slice trace lemma `EpsLocalPStar.SliceTracePth`).  The trace transfer from the angular boundary
"sees" `f` only through this energy, so it is named here once and shared by the lemmas about the
dominating density.
-/
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.Spaces.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.EpsLocalPStar

open scoped Real Topology
open MeasureTheory Set Filter

/-- The weighted angular energy of the `z`-slice of `f`,

  `Ibd α f z = ∫_{σ ∈ Iθ} sin(2σ)^{2-γ} * (∂_θ f z σ)² dσ`,

with `γ = Work.Spaces.gam α`.  This is exactly the factor multiplying `100/(γ-1) * sin(2θ)^{γ-1}`
on the right-hand side of the boundary bound `hbd`. -/
noncomputable def Ibd (α : ℝ) (f : ℝ → ℝ → ℝ) (z : ℝ) : ℝ :=
  ∫ σ in Work.Spaces.Iθ,
    (Real.sin (2 * σ)) ^ (2 - Work.Spaces.gam α) * (Work.Spaces.pth f z σ) ^ 2

end Work.FTS.StrongEps.EpsLocalPStar
