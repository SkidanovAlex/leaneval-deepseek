import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.EllipticEst.integrableOn_HkIntegrand_terms
import Submission.Work.FTS.StrongPersist.N6Trans.T1SixAux.leibnizRem6
import Submission.Work.Spaces.HkSq_terms
import Submission.Work.Spaces.dthU_Gam

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.L3Rhs

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## The two radial factors -/

/-- The radial profile `z ↦ 2z/(1+z)²` of the star solution `F_*`. -/
def VfsRad (z : ℝ) : ℝ := 2 * z / (1 + z) ^ 2

/-- The second radial factor `z ↦ (Zop VfsRad) z = z ∂_z VfsRad z`. -/
def VfsRadZ (z : ℝ) : ℝ := Work.Spaces.Zop VfsRad z

/-! ## The two angular factors -/

/-- The angular profile `Γ(θ)/c(α)`. -/
def VfsGc (α : ℝ) (θ : ℝ) : ℝ := Work.Spaces.Gam α θ / Work.Spaces.c α

/-- The first angular factor of `Vfs`: `(3/2)·(dthU (Γ/c)) θ` (note `dthU ψ = sin 2θ · ψ'`
already carries the factor `sin 2θ` which comes from `pth F_* = sin 2θ · ∂_θ F_*`). -/
def VfsA1 (α : ℝ) (θ : ℝ) : ℝ :=
  (3 / 2) * Work.Spaces.dthU (VfsGc α) θ

/-- The second angular factor of `Vfs`: `-α·c₂(θ)·Γ(θ)/c(α)`. -/
def VfsA2 (α : ℝ) (θ : ℝ) : ℝ :=
  -α * Work.Construction.c2m θ * VfsGc α θ

/-! ## The angular majorants -/

/-- The angular majorant of a single angular profile `C` at order three: the angular factor
produced by `HkIntegrand_sep_le`. -/
def angMaj (α : ℝ) (C : ℝ → ℝ) (θ : ℝ) : ℝ :=
  (C θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
    + ∑ i ∈ Finset.range 4,
        (if 1 ≤ i then (Work.Spaces.dthU^[i] C θ) ^ 2
          * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) else 0)

/-- The angular majorant of the separated summand `Mf f · Vfs α`. -/
def VfsAngMaj (α : ℝ) (θ : ℝ) : ℝ := angMaj α (VfsA1 α) θ + angMaj α (VfsA2 α) θ

end Work.FTS.StrongPersist.L3Rhs
