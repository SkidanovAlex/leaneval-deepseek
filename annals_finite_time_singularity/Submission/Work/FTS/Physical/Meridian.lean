import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.InnerProductSpace.PiL2
import Submission.Work.CoreResiduals.SelfSimReduction
import Submission.Work.FTS.Physical.Omega
import Submission.Work.Spaces.SmoothCompact_HkMem

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open FiniteTimeSingularity Set
open scoped Topology

set_option autoImplicit false

namespace Work.FTS.Physical

open PhysClock

/-- **The meridian profile of the reconstructed vorticity.**  The `e_θ`-coefficient of
`physOmega α A B g C (·, t)` as a function of the meridian coordinates `(r, z)`:

  `merProfile α A B g C r z t = A(τ(t))⁻¹ · profile (3α) (g·τ(t)) (ρP(r,z)^{3α}/B(τ(t))) (θP(r,z))`.

This is the scalar unknown of the scalar (meridian) form of the vorticity equation. -/
noncomputable def merProfile (α : ℝ) (A B : ℝ → ℝ) (g : ℝ → ℝ → ℝ → ℝ) (C : PhysClock) :
    ℝ → ℝ → ℝ → ℝ :=
  fun r z t => (A (clockInv C t))⁻¹ * Work.ConstructionInstance.profile
    (Work.FTS.Regularity.pExp α) (Work.FTS.Regularity.gSlice g (clockInv C t))
    (Work.Cyl.rhoP r z ^ Work.FTS.Regularity.pExp α / B (clockInv C t)) (Work.Cyl.thetaP r z)

/-- **The reconstructed vorticity is a swirl field**: at every time it is the meridian profile
times the angular unit vector. -/
theorem physOmega_eq_smul_eTheta (α : ℝ) (A B : ℝ → ℝ) (g : ℝ → ℝ → ℝ → ℝ) (C : PhysClock)
    (x : R3) (t : ℝ) :
    physOmega α A B g C x t
      = merProfile α A B g C (Work.Cyl.radial x) (Work.Cyl.axial x) t • Work.Cyl.eTheta x := by
  have hrho : Work.Cyl.rho x = Work.Cyl.rhoP (Work.Cyl.radial x) (Work.Cyl.axial x) := by
    rw [Work.Cyl.rho, Work.Cyl.rhoP, Work.Cyl.radial_sq]
  have htheta : Work.Cyl.theta x = Work.Cyl.thetaP (Work.Cyl.radial x) (Work.Cyl.axial x) := rfl
  simp only [physOmega_apply, Work.FTS.Regularity.physVort_apply,
    Work.ConstructionInstance.omegaSz_apply, smul_smul, merProfile, hrho, htheta]

/-! ## The scalar reduction -/


end Work.FTS.Physical
