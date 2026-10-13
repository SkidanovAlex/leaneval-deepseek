import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Submission.Work.FTS.BSIdent.Defs
import Submission.Work.FTS.Regularity.Defs
import Submission.Work.FTS.Regularity.physVort_support
import Submission.Work.FTS.BSSwirl.Defs
import Submission.Work.FTS.BSSwirl.Main

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.BSIdent.Weyl

/-- **The `τ`-slice of the physical vorticity is a swirl field.**

The physical vorticity of the reconstruction is, at each physical time `τ`,

  `physVort α A B g x τ = (A τ)⁻¹ • F(ρ(x)^{3α}/B(τ), θ(x), τ) • e_θ(x)`

with `F = profile (3α) (gSlice g τ)` the full self-similar profile at time `τ`.  Since the
cylindrical coordinates `(r, x₃)` of `ℝ³` and the polar coordinates `(ρ, θ)` are related by
`Cyl.rho x = Cyl.rhoP (Cyl.radial x) (Cyl.axial x)` and `Cyl.theta x = Cyl.thetaP (Cyl.radial x)
(Cyl.axial x)`, this field is the *swirl field* of the `(r, x₃)`-profile

  `(r, z) ↦ (A τ)⁻¹ · profile (3α) (gSlice g τ) (rhoP r z ^ 3α / B τ) (thetaP r z)`,

i.e. of the same formula written in the planar variables.  This is the bridge that lets the
vorticity of the construction be handled with the `BSSwirl` machinery (curl/div of a swirl field).
-/
theorem physVort_slice_eq_swirlField (α τ : ℝ) (A B : ℝ → ℝ) (g : ℝ → ℝ → ℝ → ℝ) :
    (Work.FTS.Regularity.physVort α A B g · τ)
      = Work.FTS.BSSwirl.swirlField (fun r z => (A τ)⁻¹ *
          Work.ConstructionInstance.profile (Work.FTS.Regularity.pExp α)
            (Work.FTS.Regularity.gSlice g τ)
            (Work.Cyl.rhoP r z ^ Work.FTS.Regularity.pExp α / B τ)
            (Work.Cyl.thetaP r z)) := by
  funext x
  -- both sides are `c x • Cyl.eTheta x`; unfold the two definitions of the fields
  simp only [Work.FTS.Regularity.physVort, Work.FTS.BSSwirl.swirlField,
    Work.ConstructionInstance.omegaSz]
  -- the scalar prefactor of the left side is `(A τ)⁻¹ * F(...)`
  rw [smul_smul, Work.ConstructionInstance.rho_eq_rhoP x]
  -- the angles agree definitionally: `θ(x) = arctan(x₃/r) = thetaP (radial x) (axial x)`
  simp only [Work.Cyl.theta, Work.Cyl.thetaP]

end Work.FTS.BSIdent.Weyl
