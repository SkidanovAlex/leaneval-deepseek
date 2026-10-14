import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.CoreResiduals.Enstrophy
import Submission.Work.R1G.vecResid_eq_scalar_smul

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open FiniteTimeSingularity Set Gradient Matrix Filter Topology MeasureTheory
open scoped Topology Matrix NNReal ENNReal

namespace Work.CoreResiduals

/-- **The self-similar vorticity profile**
`W(r,z,t) = λ(t)⁻¹·F(ρ(r,z)^p/λ(t), Θ(r,z))`, `ρ = √(r²+z²)`, `Θ = arctan(z/r)`. -/
noncomputable def ssVort (p : ℝ) (lam : ℝ → ℝ) (F : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ → ℝ :=
  fun r z t => (lam t)⁻¹ * F ((Work.Cyl.rhoP r z) ^ p / lam t) (Work.Cyl.thetaP r z)

/-- **The self-similar stream function**.  The paper's self-similar stream function is `Ψ = λ⁻¹Φ`
and the *physical* stream function of the swirl field is `ψ = ρ²Ψ` (`Work.Elliptic`'s convention:
"in the self-similar variables `R = ρ^α`, `θ` with `ψ = ρ²Ψ(R,θ)`").  Hence

  `ψ(r,z,t) = ρ(r,z)²·λ(t)⁻¹·Φ(ρ(r,z)^p/λ(t), Θ(r,z))`. -/
noncomputable def ssPsi (p : ℝ) (lam : ℝ → ℝ) (Φ : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ → ℝ :=
  fun r z t => (Work.Cyl.rhoP r z) ^ 2 * ((lam t)⁻¹ * Φ
    ((Work.Cyl.rhoP r z) ^ p / lam t) (Work.Cyl.thetaP r z))

/-- **The residual of the meridian scalar equation** at `(r,z,t)`: the left-hand side minus the
right-hand side of
`∂ₜW + (∂_zψ)·∂_rW + (-(ψ/r) - ∂_rψ)·∂_zW = ((∂_zψ)/r)·W`. -/
noncomputable def meridianResid (W ψ : ℝ → ℝ → ℝ → ℝ) (r z t : ℝ) : ℝ :=
  deriv (fun s : ℝ => W r z s) t
    + Work.Cyl.pdZ (fun r' z' => ψ r' z' t) r z * Work.Cyl.pdR (fun r' z' => W r' z' t) r z
    + (-(ψ r z t / r) - Work.Cyl.pdR (fun r' z' => ψ r' z' t) r z)
        * Work.Cyl.pdZ (fun r' z' => W r' z' t) r z
    - (Work.Cyl.pdZ (fun r' z' => ψ r' z' t) r z / r) * W r z t

