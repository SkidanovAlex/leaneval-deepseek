/-
# `Work.FTS.Physical.Meridian` — the meridian (scalar) form of the physical vorticity equation

The physical vorticity of the reconstruction is a *swirl* field, `ω(x,t) = W(radial x, axial x, t) •
e_θ(x)`, with `W` the meridian profile.  For such a field the ℝ³ vorticity equation is equivalent to
a single **scalar** equation in the meridian variables `(r,z,t)`
(`Work.CoreResiduals.VorticityEquation.vorticityEquation_cylField_iff_scalar` /
`Work.CoreResiduals.meridianResid`).

This module

* defines `merProfile`, the meridian profile of the reconstructed vorticity
  `physOmega α A B g C`, and proves `physOmega_eq_smul_eTheta`
  (`physOmega α A B g C x t = merProfile … (radial x) (axial x) t • e_θ(x)`);
* proves `vorticityEquation_of_meridian`: **the ℝ³ vorticity equation for a stream-function velocity
  follows from the scalar meridian equation** for the meridian pair — the reduction that turns node
  N8's item 5 (the chain rule from N5's fake-time equation) into a scalar statement about the
  profile.

Together with the identification `BS ω = ±psiField ψ` (audit item 4, whose divergence half is
`Work.FTS.Physical.RegPkg.div_physVort_of_smoothFar`), this is the interface through which the
dynamically rescaled equation of node N5 reaches the physical fields: the remaining content of item 5
is the *scalar* implication "fake-time equation ⟹ `MeridianEq (merProfile …) Ψ`", which is where the
two-scaling chain rule of the dynamic rescaling lives.
-/
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.InnerProductSpace.PiL2
import Submission.Work.FTS.Physical.Omega
import Submission.Work.CoreResiduals.SelfSimReduction
import Submission.Work.Cyl.vorticity_psiField

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

/-- **The ℝ³ vorticity equation from the scalar meridian equation.**  If the meridian pair
`(W, Ψ)` satisfies the meridian equation `MeridianEq W Ψ`, then the stream-function velocity
`x ↦ psiField (Ψ · t) x` and the swirl vorticity `W(radial x, axial x, t) • e_θ(x)` satisfy the
vorticity equation in `ℝ³`.

This is the trivial direction of
`Work.CoreResiduals.VorticityEquation.vorticityEquation_cylField_iff_scalar` at the stream-function
data `u_r = ∂_zΨ`, `u_z = -(Ψ/r) - ∂_rΨ`; it is what removes the ℝ³-level hypothesis `hvort` from
the reconstruction. -/
theorem vorticityEquation_of_meridian {W Ψ : ℝ → ℝ → ℝ → ℝ}
    (hW : ∀ t r z : ℝ, 0 < r → Work.Cyl.DiffAt2 (fun r z => W r z t) r z)
    (hΨ : ∀ t r z : ℝ, 0 < r → ContDiffAt ℝ 2 (fun p : ℝ × ℝ => Ψ p.1 p.2 t) (r, z))
    (hme : Work.CoreResiduals.MeridianEq W Ψ) :
    Work.LWP.VorticityEquation (fun x t => Work.Cyl.psiField (fun r z => Ψ r z t) x)
      (fun x t => W (Work.Cyl.radial x) (Work.Cyl.axial x) t • Work.Cyl.eTheta x) := by
  refine (Work.CoreResiduals.VorticityEquation.vorticityEquation_cylField_iff_scalar
    (ur := fun r z t => Work.Cyl.pdZ (fun r' z' => Ψ r' z' t) r z)
    (uz := fun r z t => -(Ψ r z t / r) - Work.Cyl.pdR (fun r' z' => Ψ r' z' t) r z)
    (W := W) hW ?_).mpr ?_
  · intro t r z hr
    have h2 : ContDiffAt ℝ 2 (fun p : ℝ × ℝ => Ψ p.1 p.2 t) (r, z) := hΨ t r z hr
    refine ⟨?_, ?_⟩
    · exact Work.Cyl.differentiableAt_pdZ (fun r' z' => Ψ r' z' t) r z h2
    · have h1 : DifferentiableAt ℝ (fun p : ℝ × ℝ => Ψ p.1 p.2 t) (r, z) :=
        h2.differentiableAt (by norm_num)
      have h3 : DifferentiableAt ℝ
          (fun p : ℝ × ℝ => Work.Cyl.pdR (fun r' z' => Ψ r' z' t) p.1 p.2) (r, z) :=
        Work.Cyl.differentiableAt_pdR (fun r' z' => Ψ r' z' t) r z h2
      have hfst : DifferentiableAt ℝ (fun p : ℝ × ℝ => p.1) (r, z) := differentiableAt_fst
      have hquot : DifferentiableAt ℝ (fun p : ℝ × ℝ => Ψ p.1 p.2 t * (p.1)⁻¹) (r, z) :=
        h1.mul (hfst.inv (by simpa using (ne_of_gt hr : r ≠ 0)))
      exact hquot.neg.sub h3
  · intro r z t hr
    have h := hme r z t hr
    simp only [Work.CoreResiduals.meridianResid] at h
    linarith

end Work.FTS.Physical
