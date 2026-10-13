/-
# `EllPkgAux/uopPointwiseId` — the pointwise identity for `Uop α (EllResid α g Ψ)`

`Uop α Ξ = -3Ξ - α z ∂_z Ξ` is the coefficient of `∂_θΩ` in the self-similar vorticity
equation (paper (Relations), tex 1320).  For the *residual* `Ξ = EllResid α g Ψ` of
Theorem `RemovingL12` the paper replaces `Ξ` by the straightened unknown
`V = ellShift α g Ψ = Ψ + Gsing α g · sin 2θ` (they differ by the rank-one singular term
`Ḡ α g · sin 2θ`), and the two coefficients are related by the first integral of the ODE for
`Ḡ`:

  `α z ∂_z(Ḡ α g) = -5 Ḡ α g - (3/4) F_*(g)`   (`Ḡ = Gbar α g`).

Since `Ξ = V - Ḡ·sin 2θ` and `sin 2θ` is independent of `z`, this gives the *pointwise
identity* of the file

  `Uop α Ξ / sin 2θ = -3·(V / sin 2θ) - α·(D_z V / sin 2θ) - (2 Ḡ α g + (3/4) F_*(g))`.

Proof, in three steps.

* `∂_z Ξ = ∂_z V - sin 2θ · ∂_z Ḡ` (needs the `z`-slices of `Ψ` to be differentiable; this is
  the hypothesis `SmoothOpen Ψ` — with the *totalised* `deriv` the identity fails when the
  slices are not differentiable, see `PkgK5/uopPointwiseIdentityRefute.lean`);
* `∂_z Ḡ = ∂_z Gsing + (1/4α) ∂_z L₁₂` (`Gsing = Gstar + Ḡ`, `Gstar = -(1/4α) L₁₂`);
* `Ξ = V - Ḡ sin 2θ`, so multiplying out and inserting the first integral for `Ḡ` collapses
  everything to the displayed identity.

The analytic inputs (`F_* ∈ C^∞(0,∞)`, `r ↦ F_*(r)/r ∈ L¹(0,∞)`, the derivative of `L₁₂`, the
derivative of the primitive `∫_0^z s^{(5-α)/α} F_*(s) ds`) are supplied by `ClassC α g`
through `FstarDivOpen.fstar_div_integrable_of_smoothOpen`,
`HasDerivAt_L12_of_Fstar_facts` and `Cert.Jfun_hasDerivAt_of_Fstar`; the hypothesis
`α ≤ 1` is an artefact of the last of these.
-/
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Submission.Work.FTS.EllSol.ClassC
import Submission.Work.FTS.EllSol.Defs
import Submission.Work.FTS.EllipticEst.Gsing_deriv_rel
import Submission.Work.FTS.EllipticEst.FstarDivOpen.fstar_div_integrable_of_smoothOpen
import Submission.Work.FTS.EllipticEst.HasDerivAt_L12_of_Fstar_facts
import Submission.Work.FTS.EllipticEst.Cert.Jfun_hasDerivAt_of_Fstar
import Submission.Work.FTS.EllSol.PkgK5.CexK5

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllSol.EllPkgAux

set_option autoImplicit false

/-- **The pointwise identity for `Uop` on the elliptic residual.**  On the open quadrant,

  `Uop α (EllResid α g Ψ) z θ / sin 2θ
     = -3·(ellShift α g Ψ z θ / sin 2θ) - α·(D_z(ellShift α g Ψ) z θ / sin 2θ)
       - (2 Ḡ α g z + (3/4) F_*(g)(z))`,

i.e. the quotient `Uop α Ξ / sin 2θ` of the residual is obtained from the quotient of the
straightened unknown `ellShift α g Ψ` by subtracting the pure radial profile
`2 Gbar α g + (3/4) Fstar g`.  The identity uses the first integral
`α z ∂_z(Gbar α g) = -5 Gbar α g - (3/4) Fstar g` of the `Ḡ`-ODE and the differentiability of
the `z`-slices of `Ψ` (hypothesis `SmoothOpen Ψ`). -/
theorem uopPointwiseId (α : ℝ) (g Ψ : Work.FTS.Galerkin.Fn) (hα : 0 < α) (hα1 : α ≤ 1)
    (hC : Work.FTS.EllSol.ClassC α g) (hΨ : Work.FTS.EllipticEst.SmoothOpen Ψ) :
    ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      Work.FTS.EllipticEst.Uop α (Work.Elliptic.EllResid α g Ψ) z θ / Real.sin (2 * θ)
        = -3 * (Work.FTS.EllSol.ellShift α g Ψ z θ / Real.sin (2 * θ))
          - α * (Work.Spaces.Dz (Work.FTS.EllSol.ellShift α g Ψ) z θ / Real.sin (2 * θ))
          - (2 * Work.Elliptic.Gbar α g z + (3 / 4) * Work.Elliptic.Fstar g z) := by
  intro z θ hz hθ hθ2
  have hσ : Real.sin (2 * θ) ≠ 0 :=
    ne_of_gt (Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [hθ2, Real.pi_pos]))
  -- ## The analytic inputs supplied by `ClassC α g`
  have hFsm : ∀ m : ℕ, ContDiffOn ℝ m (Work.Elliptic.Fstar g) (Set.Ioi 0) := hC.fsm
  have hFint : MeasureTheory.IntegrableOn (fun r : ℝ => Work.Elliptic.Fstar g r / r)
      (Set.Ioi 0) :=
    Work.FTS.EllipticEst.FstarDivOpen.fstar_div_integrable_of_smoothOpen α 7 g hC.reg hC.mem
  have hL12 : ∀ z ∈ Set.Ioi (0 : ℝ),
      HasDerivAt (Work.Elliptic.L12 g) (-(3 * Work.Elliptic.Fstar g z / z)) z :=
    Work.FTS.EllipticEst.HasDerivAt_L12_of_Fstar_facts g hFsm hFint
  have hJ : ∀ z ∈ Set.Ioi (0 : ℝ),
      HasDerivAt (fun z' => ∫ s in (0 : ℝ)..z', s ^ ((5 - α) / α) * Work.Elliptic.Fstar g s)
        (z ^ ((5 - α) / α) * Work.Elliptic.Fstar g z) z :=
    Work.FTS.EllipticEst.Cert.Jfun_hasDerivAt_of_Fstar α g hFsm hFint hα hα1
  have hJz : HasDerivAt (Work.Elliptic.Jfun α g)
      (z ^ ((5 - α) / α) * Work.Elliptic.Fstar g z) z := by
    have h := hJ z hz
    have hfun : (fun z' => ∫ s in (0 : ℝ)..z',
        s ^ ((5 - α) / α) * Work.Elliptic.Fstar g s) = Work.Elliptic.Jfun α g := rfl
    rw [hfun] at h
    exact h
  have hGbarDeriv : HasDerivAt (Work.Elliptic.Gbar α g) (Work.Elliptic.DGbar α g z) z :=
    Work.FTS.EllSol.PkgK5.CexK5.hasDerivAt_Gbar_DGbar α g hz hJz
  have hGbar_diff : DifferentiableAt ℝ (Work.Elliptic.Gbar α g) z := hGbarDeriv.differentiableAt
  have hGstar_diff : DifferentiableAt ℝ (Work.Elliptic.Gstar α g) z := by
    have h1 : Work.Elliptic.Gstar α g
        = fun z' : ℝ => (-(1 / (4 * α))) * Work.Elliptic.L12 g z' := rfl
    rw [h1]
    exact (differentiableAt_const _).mul (hL12 z hz).differentiableAt
  have hGsing_diff : DifferentiableAt ℝ (Work.Elliptic.Gsing α g) z := by
    have h1 : Work.Elliptic.Gsing α g
        = Work.Elliptic.Gstar α g + Work.Elliptic.Gbar α g := rfl
    rw [h1]
    exact hGstar_diff.add hGbar_diff
  have hL12diff : DifferentiableAt ℝ (Work.Elliptic.L12 g) z := (hL12 z hz).differentiableAt
  -- ## The derivatives of the two `z`-slices (this is where `SmoothOpen Ψ` enters)
  have hΨslice : HasDerivAt (fun z' : ℝ => Ψ z' θ) (Work.Spaces.pz Ψ z θ) z :=
    hΨ.hasDerivAt_slice ⟨hθ, hθ2⟩ hz
  have hGsingd : HasDerivAt (fun z' : ℝ => Work.Elliptic.Gsing α g z')
      (deriv (Work.Elliptic.Gsing α g) z) z := hGsing_diff.hasDerivAt
  have hXslice : HasDerivAt (fun z' : ℝ => Work.FTS.EllSol.ellShift α g Ψ z' θ)
      (Work.Spaces.pz Ψ z θ + deriv (Work.Elliptic.Gsing α g) z * Real.sin (2 * θ)) z := by
    have h := hΨslice.add (hGsingd.mul_const (Real.sin (2 * θ)))
    have hfun : ((fun z' : ℝ => Ψ z' θ)
        + fun y : ℝ => Work.Elliptic.Gsing α g y * Real.sin (2 * θ))
        = fun z' : ℝ => Work.FTS.EllSol.ellShift α g Ψ z' θ := by
      funext z'
      simp only [Pi.add_apply, Work.FTS.EllSol.ellShift]
    rwa [hfun] at h
  have hΞslice : HasDerivAt (fun z' : ℝ => Work.Elliptic.EllResid α g Ψ z' θ)
      (Work.Spaces.pz Ψ z θ
        - (1 / (4 * α)) * Real.sin (2 * θ) * deriv (Work.Elliptic.L12 g) z) z := by
    have h := hΨslice.sub (hL12diff.hasDerivAt.const_mul ((1 / (4 * α)) * Real.sin (2 * θ)))
    have hfun : ((fun z' : ℝ => Ψ z' θ)
        - fun y : ℝ => (1 / (4 * α)) * Real.sin (2 * θ) * Work.Elliptic.L12 g y)
        = fun z' : ℝ => Work.Elliptic.EllResid α g Ψ z' θ := by
      funext z'
      simp only [Pi.sub_apply, Work.Elliptic.EllResid]
    rwa [hfun] at h
  have hpzX : Work.Spaces.pz (Work.FTS.EllSol.ellShift α g Ψ) z θ
      = Work.Spaces.pz Ψ z θ + deriv (Work.Elliptic.Gsing α g) z * Real.sin (2 * θ) := by
    simpa only [Work.Spaces.pz] using hXslice.deriv
  have hpzΞ : Work.Spaces.pz (Work.Elliptic.EllResid α g Ψ) z θ
      = Work.Spaces.pz Ψ z θ
        - (1 / (4 * α)) * Real.sin (2 * θ) * deriv (Work.Elliptic.L12 g) z := by
    simpa only [Work.Spaces.pz] using hΞslice.deriv
  -- ## `∂_z Ḡ = ∂_z Gsing + (1/4α) ∂_z L₁₂` (`Gsing = Gstar + Ḡ`, `Gstar = -(1/4α) L₁₂`)
  have hGbar_deriv : deriv (Work.Elliptic.Gbar α g) z
      = deriv (Work.Elliptic.Gsing α g) z
        + (1 / (4 * α)) * deriv (Work.Elliptic.L12 g) z := by
    have h := hGsingd.add (hL12diff.hasDerivAt.const_mul (1 / (4 * α)))
    have hfun : (Work.Elliptic.Gsing α g
        + fun y : ℝ => (1 / (4 * α)) * Work.Elliptic.L12 g y) = Work.Elliptic.Gbar α g := by
      funext y
      simp only [Pi.add_apply, Work.Elliptic.Gsing, Work.Elliptic.Gstar]
      ring
    rw [hfun] at h
    exact h.deriv
  -- ## `∂_z(ellShift) = ∂_z(EllResid) + sin 2θ · ∂_z Ḡ`
  have hpz_rel : Work.Spaces.pz (Work.FTS.EllSol.ellShift α g Ψ) z θ
      = Work.Spaces.pz (Work.Elliptic.EllResid α g Ψ) z θ
        + Real.sin (2 * θ) * deriv (Work.Elliptic.Gbar α g) z := by
    rw [hpzX, hpzΞ, hGbar_deriv]
    ring
  -- ## the first integral of the `Ḡ`-ODE: `α z ∂_z Ḡ = -5 Ḡ - (3/4) F_*`
  have hrel := Work.FTS.EllSol.PkgK5.CexK5.Gbar_deriv_rel α g hα hL12
      (fun z hz => (((hFsm 1).differentiableOn (by norm_num)).differentiableAt
        (isOpen_Ioi.mem_nhds hz)).hasDerivAt) hJ z hz
  rw [← hGbarDeriv.deriv] at hrel
  -- ## the unscaled identity
  have hscaled : Work.FTS.EllipticEst.Uop α (Work.Elliptic.EllResid α g Ψ) z θ
      = -3 * Work.FTS.EllSol.ellShift α g Ψ z θ
        - α * Work.Spaces.Dz (Work.FTS.EllSol.ellShift α g Ψ) z θ
        - Real.sin (2 * θ) * (2 * Work.Elliptic.Gbar α g z
            + (3 / 4) * Work.Elliptic.Fstar g z) := by
    have hU : Work.FTS.EllipticEst.Uop α (Work.Elliptic.EllResid α g Ψ) z θ
        = -3 * Work.Elliptic.EllResid α g Ψ z θ
          - α * Work.Spaces.Dz (Work.Elliptic.EllResid α g Ψ) z θ := by
      simp only [Work.FTS.EllipticEst.Uop, Work.Spaces.Dz]
      ring
    have hXeq : Work.FTS.EllSol.ellShift α g Ψ z θ
        = Work.Elliptic.EllResid α g Ψ z θ
          + Work.Elliptic.Gbar α g z * Real.sin (2 * θ) := by
      simp only [Work.FTS.EllSol.ellShift, Work.Elliptic.EllResid, Work.Elliptic.Gsing,
        Work.Elliptic.Gstar]
      ring
    have hDzX : Work.Spaces.Dz (Work.FTS.EllSol.ellShift α g Ψ) z θ
        = Work.Spaces.Dz (Work.Elliptic.EllResid α g Ψ) z θ
          + Real.sin (2 * θ) * z * deriv (Work.Elliptic.Gbar α g) z := by
      simp only [Work.Spaces.Dz, hpz_rel]
      ring
    rw [hU, hDzX, hXeq]
    have hσrel : Real.sin (2 * θ) * (α * (z * deriv (Work.Elliptic.Gbar α g) z))
        = Real.sin (2 * θ) * (-5 * Work.Elliptic.Gbar α g z
            - (3 / 4) * Work.Elliptic.Fstar g z) := by rw [hrel]
    linear_combination hσrel
  -- ## divide by `sin 2θ`
  rw [hscaled]
  field_simp

end Work.FTS.EllSol.EllPkgAux
