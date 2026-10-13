/-
# `Work.FTS.Physical.SignConvention` — the sign convention of the elliptic law

This module answers, with proofs, the design question raised by the lead (trap 8 of
`N45_DESIGN_LEAD.md` §5): *does the vorticity/stream-function dictionary used by the reconstructed
solution match the sign of the elliptic law `bslOp`?*  A mismatch makes the reconstructed velocity
the negative of the true one, and the pair `(u,ω)` then satisfies the vorticity equation with the
sign of `∂ₜ` reversed — the reconstructed solution runs **backward in time**.

## The two facts, both proved here

**(1) The curl identity of the workspace has a minus sign.**
`Work.Cyl.vorticity_psiField` together with the polar reduction `Work.Elliptic.cylOp_polar` gives,
for the no-swirl stream function `ψ = ρ²Φ(ρ^α,θ)`,

  `vorticity (psiField ψ) x = -(bslOp α Φ (ρ(x)^α, θ(x))) • e_θ(x)`,

i.e. the `e_θ`-coefficient `Ω` of the vorticity and the elliptic source are related by
`Ω = -(bslOp α Φ)`.  Hence the elliptic law that is *consistent* with
`ω = Ω e_θ = vorticity (psiField ψ)` is `bslOp α Φ = -Ω`; with the opposite law `bslOp α Φ = Ω`
the field `psiField ψ` has vorticity `-Ω e_θ`, so the field whose vorticity is `+Ω e_θ` is
`-psiField ψ` and the reconstruction must use the *negated* stream-function field.

**(2) A sign flip in the identification reverses time.**
`VorticityEquation` is *not* invariant under `(u,ω) ↦ (-u,-ω)`: the flipped pair satisfies
`-∂ₜω + (u·∇)ω = (ω·∇)u`, the vorticity equation with `∂ₜ` reversed.  So a wrong sign in the
dictionary `BS ω = ± psiField ψ` turns the reconstructed solution into the time-reversed one.

## Status of `Uop`, `Vop`, `Rop`

The operators `Work.Construction.Uop`, `Vop`, `Rop` are transcribed **verbatim** from the paper's
(Relations) (LaTeX line 1320; the displayed axisymmetric vorticity equation at tex line 268)

  `∂_tΩ + (-3Ψ - αR∂_RΨ)∂_θΩ + (∂_θΨ - tanθ·Ψ) αR∂_RΩ = (1/cosθ)(2sinθ·Ψ + αsinθ·R∂_RΨ
   + cosθ·∂_θΨ) Ω`,

which is the vorticity equation for the *true* vorticity `Ω` (`ω(r,x₃) = Ω(R,θ)`, tex line 255) of
the paper's velocity `u` (tex line 240--241, `u_r = ∂_3ψ`, `u_3 = -ψ/r - ∂_rψ`).  So
`Uop`/`Vop`/`Rop` carry the paper's *positive* stream-function convention, whereas the workspace's
`Work.Cyl.psiField` carries the opposite one ((1) above).  The two are only ever related in the
workspace through the *identification* of the Biot–Savart velocity with the stream-function field
(audit §4 N8 item 4, `Physical/Liouville.lean`); that identification must therefore be performed
with `-psiField` (equivalently with the law `bslOp α Φ = -Ω`), and `EllLaw` — which is
`bslOp α Φ = F` — is the law that gives the *negated* velocity.
-/
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.InnerProductSpace.PiL2
import Submission.Work.FTS.Physical.Defs
import Submission.Work.FTS.EllipticEst.vorticity_psiField_bslOp_fts

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open FiniteTimeSingularity Set
open scoped Topology

set_option autoImplicit false

namespace Work.FTS.Physical

/-! ## Time reversal of the vorticity equation -/

/-- Negating a spacetime field negates its time derivative. -/
theorem timeDeriv_neg (f : R3 → ℝ → R3) (x : R3) (t : ℝ) :
    timeDeriv (fun y s => -f y s) x t = -timeDeriv f x t := by
  simp only [FiniteTimeSingularity.timeDeriv]
  exact deriv.neg

/-- Negating the *value* field negates the directional derivative in the second slot. -/
theorem directionalDeriv_neg_snd (v u : R3 → ℝ → R3) (x : R3) (t : ℝ) :
    directionalDeriv v (fun y s => -u y s) x t = -directionalDeriv v u x t := by
  simp only [FiniteTimeSingularity.directionalDeriv, Pi.neg_apply]
  exact map_neg (fderiv ℝ (v · t) x) (u x t)

/-- Negating the *direction* field negates the directional derivative in the first slot. -/
theorem directionalDeriv_neg_fst (v u : R3 → ℝ → R3) (x : R3) (t : ℝ) :
    directionalDeriv (fun y s => -v y s) u x t = -directionalDeriv v u x t := by
  simp only [FiniteTimeSingularity.directionalDeriv]
  have hfun : (fun y : R3 => -v y t) = -(fun y : R3 => v y t) := rfl
  rw [hfun, fderiv_neg]
  rfl

/-- **The vorticity equation is not invariant under `(u,ω) ↦ (-u,-ω)`.**  The negated pair
satisfies `-∂ₜω + (u·∇)ω = (ω·∇)u`, which is the vorticity equation with `∂ₜ` reversed — the
time-reversed (backward-in-time) equation for `(u,ω)`.

This is why the sign of the elliptic law matters: if the identification `BS ω = ± psiField Φ`
carries the wrong sign, the reconstructed pair is `(-u,-ω)` for the true solution and therefore
runs backward in time. -/
theorem vorticityEquation_neg_iff (u ω : R3 → ℝ → R3) :
    Work.LWP.VorticityEquation (fun x t => -u x t) (fun x t => -ω x t) ↔
      ∀ x t, -timeDeriv ω x t + directionalDeriv ω u x t = directionalDeriv u ω x t := by
  constructor
  · intro h x t
    simpa [timeDeriv_neg, directionalDeriv_neg_fst, directionalDeriv_neg_snd] using h x t
  · intro h x t
    simpa [timeDeriv_neg, directionalDeriv_neg_fst, directionalDeriv_neg_snd] using h x t

/-! ## The curl identity and the sign of the elliptic law -/

/-- **The workspace's curl identity for the stream-function field.**  For the no-swirl stream
function `ψ = ρ²Φ(ρ^α,θ)`, the vorticity off the axis is `-(bslOp α Φ (ρ^α,θ)) • e_θ`.  The `−`
sign is the one pinned by `Work.Cyl.vorticity_psiField` and `Work.Elliptic.cylOp_polar`. -/
theorem vorticity_psiField_eq_neg_smul {α : ℝ} {Φ : ℝ → ℝ → ℝ} (x : Work.Cyl.R3)
    (hx : 0 < Work.Cyl.radial x)
    (hΦ : ContDiffAt ℝ 2 (fun q : ℝ × ℝ => Φ q.1 q.2) (Work.Cyl.rho x ^ α, Work.Cyl.theta x)) :
    vorticity (Work.Cyl.psiField (fun r z => Work.Cyl.rhoP r z ^ 2
        * Φ (Work.Cyl.rhoP r z ^ α) (Work.Cyl.thetaP r z))) x
      = -(Work.Elliptic.bslOp α Φ (Work.Cyl.rho x ^ α) (Work.Cyl.theta x)) • Work.Cyl.eTheta x :=
  Work.FTS.EllipticEst.vorticity_psiField_bslOp_fts α Φ x hx hΦ

/-- **The consistent elliptic law.**  If `bslOp α Φ = -Ω` then the stream-function field `psiField ψ`
*is* the no-swirl field of vorticity `Ω e_θ`: the identification of the reconstruction may use the
stream-function field itself. -/
theorem vorticity_psiField_eq_smul_of_bslOp_neg {α : ℝ} {Φ Ω : ℝ → ℝ → ℝ}
    (h : ∀ z θ, Work.Elliptic.bslOp α Φ z θ = -Ω z θ) (x : Work.Cyl.R3)
    (hx : 0 < Work.Cyl.radial x)
    (hΦ : ContDiffAt ℝ 2 (fun q : ℝ × ℝ => Φ q.1 q.2) (Work.Cyl.rho x ^ α, Work.Cyl.theta x)) :
    vorticity (Work.Cyl.psiField (fun r z => Work.Cyl.rhoP r z ^ 2
        * Φ (Work.Cyl.rhoP r z ^ α) (Work.Cyl.thetaP r z))) x
      = Ω (Work.Cyl.rho x ^ α) (Work.Cyl.theta x) • Work.Cyl.eTheta x := by
  rw [vorticity_psiField_eq_neg_smul (Φ := Φ) x hx hΦ, h]
  simp

/-- **THE SIGN TRAP.**  If the elliptic law is `bslOp α Φ = Ω` — which is the law
`Work.FTS.Galerkin.EllLaw α` of the dynamic-rescaling area, and the paper's (PolarBSL1) read
with the source equal to the vorticity coefficient — then the stream-function field has vorticity
`-Ω e_θ`, **not** `+Ω e_θ`.  Hence:

* the field whose vorticity is `+Ω e_θ` (the physical vorticity of the reconstruction,
  `physVort = A⁻¹ Ω e_θ`) is `-psiField (ρ²Φ(ρ^α,θ))`, not `psiField (ρ²Φ(ρ^α,θ))`;
* by `vorticityEquation_neg_iff`, identifying `BS ω` with `+psiField ψ` instead of `-psiField ψ`
  makes the reconstructed pair satisfy the vorticity equation with `∂ₜ` reversed, i.e. the
  reconstructed solution runs backward in time. -/
theorem vorticity_psiField_eq_neg_smul_of_bslOp_pos {α : ℝ} {Φ Ω : ℝ → ℝ → ℝ}
    (h : ∀ z θ, Work.Elliptic.bslOp α Φ z θ = Ω z θ) (x : Work.Cyl.R3)
    (hx : 0 < Work.Cyl.radial x)
    (hΦ : ContDiffAt ℝ 2 (fun q : ℝ × ℝ => Φ q.1 q.2) (Work.Cyl.rho x ^ α, Work.Cyl.theta x)) :
    vorticity (Work.Cyl.psiField (fun r z => Work.Cyl.rhoP r z ^ 2
        * Φ (Work.Cyl.rhoP r z ^ α) (Work.Cyl.thetaP r z))) x
      = -(Ω (Work.Cyl.rho x ^ α) (Work.Cyl.theta x)) • Work.Cyl.eTheta x := by
  rw [vorticity_psiField_eq_neg_smul (Φ := Φ) x hx hΦ, h]

/-- **The pinned convention, in the form the identification step consumes.**  Under the elliptic
law `bslOp α Φ = Ω` — the workspace's `Work.FTS.Galerkin.EllLaw α`, i.e. the paper's (PolarBSL1)
read with the source equal to the vorticity coefficient — the field whose vorticity is exactly the
physical one `Ω(ρ^α,θ) e_θ` is the stream-function field of the **negated** stream function:

  `vorticity (psiField (ρ²·(-Φ)(ρ^α,θ))) = Ω(ρ^α,θ) • e_θ`.

So the identification `BS ω = c · psiField ψ` of the reconstruction has no sign freedom: with the
law `bslOp α Φ = Ω` the stream function that must be used is `-Φ` (equivalently, the field
`-psiField ψ`), because `bslOp α (-Φ) = -Ω` (`Work.Elliptic.bslOp_neg`) and
`vorticity_psiField_eq_smul_of_bslOp_neg` then applies.  Using `+Φ` instead gives the vorticity
`-Ω e_θ`, and by `vorticityEquation_neg_iff` that is the time-reversed solution. -/
theorem vorticity_psiField_neg_of_bslOp_pos {α : ℝ} {Φ Ω : ℝ → ℝ → ℝ}
    (h : ∀ z θ, Work.Elliptic.bslOp α Φ z θ = Ω z θ) (x : Work.Cyl.R3)
    (hx : 0 < Work.Cyl.radial x)
    (hΦ : ContDiffAt ℝ 2 (fun q : ℝ × ℝ => Φ q.1 q.2) (Work.Cyl.rho x ^ α, Work.Cyl.theta x)) :
    vorticity (Work.Cyl.psiField (fun r z => Work.Cyl.rhoP r z ^ 2
        * (-Φ) (Work.Cyl.rhoP r z ^ α) (Work.Cyl.thetaP r z))) x
      = Ω (Work.Cyl.rho x ^ α) (Work.Cyl.theta x) • Work.Cyl.eTheta x := by
  have hneg : ∀ z θ, Work.Elliptic.bslOp α (-Φ) z θ = -Ω z θ := by
    intro z θ
    rw [Work.FTS.EllipticEst.bslOp_neg]
    simp only [Pi.neg_apply, h z θ]
  exact vorticity_psiField_eq_smul_of_bslOp_neg hneg x hx hΦ.neg

end Work.FTS.Physical
