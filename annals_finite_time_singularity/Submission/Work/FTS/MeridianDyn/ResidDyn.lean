/-
# `Work.FTS.MeridianDyn.ResidDyn` — the meridian residual of the dynamical ansatz

The pointwise identity that is the *content* of the dynamic meridian bridge: for the dynamical
self-similar ansatz

  `W(r,z,t) = a(t)·F(ρ(r,z)^p/b(t), Θ(r,z), σ(t))`,   `ψ(r,z,t) = ρ(r,z)²·a(t)·Φ(…, σ(t))`

whose amplitude, scale and clock satisfy

  `a'(t) = (1+μ)·σ'(t)·a(t)`,   `b'(t) = -(1-μ)·σ'(t)·b(t)`,   `2·σ'(t) = a(t)`

(the last being the *clock normalisation* `C.A = 2·A_v` of design correction 1, written in the
form in which it enters the algebra), the meridian residual of `(W,ψ)` is `a(t)·σ'(t)` times the
left-hand side of the dynamic profile equation `(E)`:

  `meridianResid W ψ r z t = a(t)·σ'(t)·( ∂_τF + (1+μ)F + (1-μ)D_zF + UVR p F Φ )(Z,Θ,σ(t))`.

This is the exact generalisation of `Work.CoreResiduals.meridianResid_algebra` (the constant-rate
case `a = λ⁻¹`, `b = λ`, `F` and `Φ` independent of `σ`), and it is the step that turns the
fake-time equation `(E)` (`Work.FTS.MeridianDyn.DynEqF`) into the meridian scalar equation.

The proof is the composition of the five chain rules (`Chain/timeDeriv_dynVort`,
`Chain/pdR_dynVort`, `Chain/pdZ_dynVort`, `Chain/pdR_dynPsi`, `Chain/pdZ_dynPsi`) with the
*algebraic core* `Algebra.meridianResid_algebra_dyn` and the polar expansion of `UVR`
(`Work.CoreResiduals.UVR_polar_expand`).
-/
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS.MeridianDyn.Defs
import Submission.Work.FTS.MeridianDyn.Algebra.meridianResid_algebra_dyn
import Submission.Work.FTS.MeridianDyn.Chain.timeDeriv_dynVort
import Submission.Work.FTS.MeridianDyn.Chain.pdR_dynVort
import Submission.Work.FTS.MeridianDyn.Chain.pdZ_dynVort
import Submission.Work.FTS.MeridianDyn.Chain.pdR_dynPsi
import Submission.Work.FTS.MeridianDyn.Chain.pdZ_dynPsi
import Submission.Work.CoreResiduals.meridianEq_of_dynEqConst

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open FiniteTimeSingularity Set
open scoped Topology

namespace Work.FTS.MeridianDyn

set_option autoImplicit false

/-- **The meridian residual of the dynamical ansatz.**  With `Z = ρ(r,z)^p/b(t)`,
`Θ = Θ(r,z)`, amplitude `a`, scale `b` and clock `σ`, and the rates `(1+μ)`, `(1-μ)` of
amplitude and scale together with the clock normalisation `2σ' = a(t)`, the meridian residual is
`a(t)·σ'(t)` times the dynamic profile operator `dynEqLHS` at `(Z,Θ)` with fake-time derivative
`Fτ`:

  `meridianResid (dynVort p a b σ F) (dynPsi p a b σ Φ) r z t
     = a(t)·σ'·(Fτ + (1+μ)F + (1-μ)D_zF + UVR p F Φ)(Z,Θ)`.

The differentiability hypotheses are exactly the joint `C¹` of the two profiles at the point
`(Z,Θ,σ(t))` (`hFc`, `hΦc`) together with the fake-time derivative of `F` along `(Z,Θ)`
(`hFt`). -/
theorem meridianResid_dyn {p : ℝ} {a b σ : ℝ → ℝ} {F Φ : Fam}
    {r z t A' B' sp μa fτ : ℝ}
    (hr : 0 < r) (hbne : b t ≠ 0)
    (ha : HasDerivAt a A' t) (hb : HasDerivAt b B' t) (hσ : HasDerivAt σ sp t)
    (ha' : A' = (1 + μa) * sp * a t) (hb' : B' = -((1 - μa) * sp) * b t)
    (h2s : 2 * sp = a t)
    (hFc : ContDiffAt ℝ 1 (fun q : ℝ × ℝ × ℝ => F q.1 q.2.1 q.2.2)
      (Work.Cyl.rhoP r z ^ p / b t, Work.Cyl.thetaP r z, σ t))
    (hΦc : ContDiffAt ℝ 1 (fun q : ℝ × ℝ => Φ q.1 q.2 (σ t))
      (Work.Cyl.rhoP r z ^ p / b t, Work.Cyl.thetaP r z))
    (hFt : HasDerivAt (fun s => F (Work.Cyl.rhoP r z ^ p / b t) (Work.Cyl.thetaP r z) s)
      fτ (σ t)) :
    Work.CoreResiduals.meridianResid (dynVort p a b σ F) (dynPsi p a b σ Φ) r z t
      = a t * sp * dynEqLHS p μa (fun Z Θ => F Z Θ (σ t)) (fun Z Θ => Φ Z Θ (σ t))
          (Work.Cyl.rhoP r z ^ p / b t) (Work.Cyl.thetaP r z) fτ := by
  have hρne : Work.Cyl.rhoP r z ≠ 0 := Work.Cyl.rhoP_ne_zero hr z
  have htan : Real.tan (Work.Cyl.thetaP r z) = z / r := by
    rw [Work.Cyl.thetaP, Real.tan_arctan]
  -- joint differentiability of the two profiles at the point
  have hFd : DifferentiableAt ℝ (fun q : ℝ × ℝ × ℝ => F q.1 q.2.1 q.2.2)
      (Work.Cyl.rhoP r z ^ p / b t, Work.Cyl.thetaP r z, σ t) :=
    hFc.differentiableAt (by norm_num)
  -- the `(Z,Θ)`-slices, for the meridian chain rules
  have hF2 : Work.Cyl.DiffAt2 (fun Z Θ => F Z Θ (σ t))
      (Work.Cyl.rhoP r z ^ p / b t) (Work.Cyl.thetaP r z) := by
    show DifferentiableAt ℝ
      ((fun q : ℝ × ℝ × ℝ => F q.1 q.2.1 q.2.2)
        ∘ fun p : ℝ × ℝ => (p.1, p.2, σ t))
      (Work.Cyl.rhoP r z ^ p / b t, Work.Cyl.thetaP r z)
    exact hFd.comp (Work.Cyl.rhoP r z ^ p / b t, Work.Cyl.thetaP r z) (by fun_prop)
  have hΦ2 : Work.Cyl.DiffAt2 (fun Z Θ => Φ Z Θ (σ t))
      (Work.Cyl.rhoP r z ^ p / b t) (Work.Cyl.thetaP r z) :=
    hΦc.differentiableAt (by norm_num)
  -- the `(Z,σ)`-slice, for the fake-time chain rule
  have hFs2 : Work.Cyl.DiffAt2 (fun Z s => F Z (Work.Cyl.thetaP r z) s)
      (Work.Cyl.rhoP r z ^ p / b t) (σ t) := by
    show DifferentiableAt ℝ
      ((fun q : ℝ × ℝ × ℝ => F q.1 q.2.1 q.2.2)
        ∘ fun p : ℝ × ℝ => (p.1, Work.Cyl.thetaP r z, p.2))
      (Work.Cyl.rhoP r z ^ p / b t, σ t)
    exact hFd.comp (Work.Cyl.rhoP r z ^ p / b t, σ t) (by fun_prop)
  -- the five chain rules
  have htd := Chain.timeDeriv_dynVort (p := p) (a := a) (b := b) (σ := σ) (F := F)
    (r := r) (z := z) (t := t) (A' := A') (B' := B') (sp := sp) (fτ := fτ)
    ha hb hσ hbne hFs2 hFt
  have hrd := Chain.pdR_dynVort (p := p) (a := a) (b := b) (σ := σ) (F := F)
    (r := r) (z := z) (t := t) hr hbne hF2
  have hzd := Chain.pdZ_dynVort (p := p) (a := a) (b := b) (σ := σ) (F := F)
    (r := r) (z := z) (t := t) hr hbne hF2
  have hrdψ := Chain.pdR_dynPsi (p := p) (a := a) (b := b) (σ := σ) (Φ := Φ)
    (r := r) (z := z) (t := t) hr hbne hΦ2
  have hzdψ := Chain.pdZ_dynPsi (p := p) (a := a) (b := b) (σ := σ) (Φ := Φ)
    (r := r) (z := z) (t := t) hr hbne hΦ2
  -- the algebraic core
  have halg := Algebra.meridianResid_algebra_dyn (p := p) (z := z) (r := r)
    (ρsq := Work.Cyl.rhoP r z ^ 2) (Z := Work.Cyl.rhoP r z ^ p / b t) (a := a t) (sp := sp)
    (κ₁ := 1 + μa) (κ₂ := 1 - μa)
    (f := F (Work.Cyl.rhoP r z ^ p / b t) (Work.Cyl.thetaP r z) (σ t)) (fτ := fτ)
    (f1 := Work.Cyl.pdR (fun Z Θ => F Z Θ (σ t))
      (Work.Cyl.rhoP r z ^ p / b t) (Work.Cyl.thetaP r z))
    (f2 := Work.Cyl.pdZ (fun Z Θ => F Z Θ (σ t))
      (Work.Cyl.rhoP r z ^ p / b t) (Work.Cyl.thetaP r z))
    (g := Φ (Work.Cyl.rhoP r z ^ p / b t) (Work.Cyl.thetaP r z) (σ t))
    (g1 := Work.Cyl.pdR (fun Z Θ => Φ Z Θ (σ t))
      (Work.Cyl.rhoP r z ^ p / b t) (Work.Cyl.thetaP r z))
    (g2 := Work.Cyl.pdZ (fun Z Θ => Φ Z Θ (σ t))
      (Work.Cyl.rhoP r z ^ p / b t) (Work.Cyl.thetaP r z))
    (ne_of_gt hr) (Work.Cyl.rhoP_sq r z)
  -- the polar expansion of `UVR`
  have hUVR := Work.CoreResiduals.UVR_polar_expand p r z (Work.Cyl.rhoP r z)
    (fun Z Θ => F Z Θ (σ t)) (fun Z Θ => Φ Z Θ (σ t))
    (Work.Cyl.rhoP r z ^ p / b t) (Work.Cyl.thetaP r z)
    (ne_of_gt hr) hρne (Work.Cyl.sin_thetaP hr z) (Work.Cyl.cos_thetaP hr z) htan
  -- the final assembly: substitute the chain rules, the polar expansion of `UVR` and the
  -- normalisations `ρ² = r²+z²` and `2σ' = a(t)`, then clear denominators and compare.
  unfold Work.CoreResiduals.meridianResid
  rw [htd, hrd, hzd, hrdψ, hzdψ]
  rw [dynVort_apply, dynPsi_apply]
  rw [ha', hb']
  rw [dynEqLHS_apply, hUVR]
  simp only [Work.Spaces.Dz, Work.Spaces.pz, Work.Cyl.pdR]
  rw [Work.Cyl.rhoP_sq r z]
  rw [← h2s]
  have hrne : r ≠ 0 := ne_of_gt hr
  have hρne : r ^ 2 + z ^ 2 ≠ 0 := by positivity
  field_simp
  ring

end Work.FTS.MeridianDyn
