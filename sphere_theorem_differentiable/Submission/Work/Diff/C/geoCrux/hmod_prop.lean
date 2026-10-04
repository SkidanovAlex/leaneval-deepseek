import Mathlib
import Submission.Work.Diff.C.geoCrux.CoreStmts
import Submission.Work.Diff.C.geoCrux.inj_radius_core
import Submission.Work.Diff.C.geoCrux.variation_modulus
import Submission.RayJacobi
import Submission.ConjEnergy
import Submission.Work.OddBound.longHomotopy.gauss_pairing_fibre
import Submission.Work.OddBound.longHomotopy.covAlong_variation_zero

set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

open LeanEval.Geometry.SphereTheorem
open scoped Manifold ContDiff Bundle Topology
open Bundle Set VectorField CovariantDerivative Metric Filter

namespace Work.Diff.C.geoCrux

universe u v w

noncomputable section

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
  [I.Boundaryless] [Nontrivial E] [CompactSpace M]
  {cov : CovariantDerivative I E (TangentSpace I (M := M))}
  [ContMDiffCovariantDerivative cov ∞]

/-! ## Transport lemmas for the tangent-space type synonym

`TangentSpace I x` is a non-reducible type synonym for the model space `E`, so the fibre metric and
the fibre norm at two propositionally equal points are only *propositionally* equal.  The three
lemmas below (private copies of the ones used in
`Submission/Work/Diff/C/RadialBound/GExp_radius_mfderiv_bound`) move a norm, an inner product and the
covariant derivative `covAlong` across a propositional equality of base points. -/

private theorem hmod_norm_congr {X Y : M} (h : X = Y) (a : E) :
    ‖(show TangentSpace I X from a)‖ = ‖(show TangentSpace I Y from a)‖ := by
  subst h; rfl

private theorem hmod_inner_congr {X Y : M} (h : X = Y) (a b : E) :
    Inner.inner ℝ (show TangentSpace I X from a) (show TangentSpace I X from b)
      = Inner.inner ℝ (show TangentSpace I Y from a) (show TangentSpace I Y from b) := by
  subst h; rfl

private theorem hmod_covAlong_congr {γ₁ γ₂ : ℝ → M} (h : γ₁ = γ₂)
    {V₁ : (t : ℝ) → TangentSpace I (γ₁ t)} {V₂ : (t : ℝ) → TangentSpace I (γ₂ t)}
    (hV : ∀ t : ℝ, (show E from V₁ t) = (show E from V₂ t)) (d : ℝ) :
    Submission.JacobiGlobal.covAlong cov V₁ d
      = Submission.JacobiGlobal.covAlong cov V₂ d := by
  subst h
  rw [show V₁ = V₂ from funext hV]

/-- The ray `t ↦ GExp q (t • v)` has non-vanishing velocity when `‖v‖ = 1`. -/
theorem curveVelocity_GExp_ray_ne (hmet : IsMetricCompatible cov) {q : M} {v : TangentSpace I q}
    (hv : ‖v‖ = 1) (t : ℝ) :
    Submission.Geodesic.curveVelocity (I := I)
      (fun s : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet q (s • v)) t ≠ 0 := by
  have hvne : v ≠ 0 := by intro hz; rw [hz, norm_zero] at hv; norm_num at hv
  rcases eq_or_ne t 0 with h | h
  · subst h
    rw [Submission.GExpVelocity.curveVelocity_GExp_smul_zero (cov := cov) hmet q hvne]
    exact hvne
  · intro hz
    have h1 := Submission.LensLoop.norm_curveVelocity_GExp_smul_ne (cov := cov) hmet q hvne h
    rw [hz, norm_zero] at h1
    rw [← h1] at hv
    norm_num at hv

/-- **The `hmod` input of `Work.Diff.C.RadialBound.GExp_radius_mfderiv_bound`, reduced to the
modulus bound for the radial variation fields.**

An arbitrary Jacobi field `Z` along the ray `t ↦ GExp q (t • v)` with `Z 0 = 0` and
`∇Z(0) ⟂ v` is identified, by Jacobi uniqueness (`Work.Diff.C.geoCrux.jacobi_uniq`) together with
`Work.OddBound.longHomotopy.covAlong_variation_zero`, with the radial variation field
`Z_ξ(t) = ∂_r|₀ GExp q (t • (v + r • ξ))` of the family of rays out of `q` with `ξ := ∇Z(0)`; the
modulus bound for the latter is the hypothesis `hvar`.  The injectivity-radius input needed to
*state* the variation bound is supplied by `Work.Diff.C.geoCrux.inj_radius_core`. -/
theorem hmod_of_variation (hvar : Work.Diff.C.geoCrux.VariationModulusProp.{u, v, w}) :
    Work.Diff.C.geoCrux.HmodProp.{u, v, w} := by
  intro E iE1 iE2 iE3 iE4 H iH I M iM1 iM2 iM3 iM4 iRB iCM iBL iNE iCS iPC cov iCD
    hmet htor c ε₁ hc hc1 hε₁ hnum2 hsmC hHess hcont hgrad q v hv ρ hρ0 hρπ hρe Z hJ hZ0 horth
  have hvne : v ≠ 0 := by intro hz; rw [hz, norm_zero] at hv; norm_num at hv
  -- the injectivity-radius input, from the C-area hypotheses
  have hcut : ∀ x : M, Submission.InjRadius.InjAtLeast (I := I) (M := M) hmet x
      (Real.pi - Real.arccos (1 - c)) := fun x =>
    Work.Diff.C.geoCrux.inj_radius_core (E := E) (H := H) (I := I) (M := M) (cov := cov)
      hmet htor hc hc1 hε₁ hnum2 hsmC hHess hcont hgrad x
  -- the initial covariant derivative of `Z`
  set ξ : TangentSpace I q :=
    (show TangentSpace I q from (show E from Submission.JacobiGlobal.covAlong cov Z 0)) with hξdef
  -- the radial variation field of the family of rays out of `q`
  set W : (t : ℝ) → TangentSpace I (Submission.GlobalExp.GExp (cov := cov) hmet q (t • v)) :=
    fun t : ℝ => Submission.Geodesic.curveVelocity (I := I)
      (fun r : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet q (t • (v + r • ξ))) 0 with hWdef
  -- `W` is a Jacobi field along the ray
  have hWJ : ∀ t : ℝ, Submission.RauchGlobal.IsJacobiAt cov
      (fun t : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet q (t • v)) W t := by
    intro t
    rw [hWdef]
    exact Submission.RayJacobi.isJacobiAt_GExp_variation (cov := cov) hmet htor (p := q) (u := v)
      (η := ξ) hvne hv t
  -- `W 0 = 0`
  have hW0 : W 0 = 0 := by
    rw [hWdef]
    exact Work.OddBound.longHomotopy.variation_zero_at_zero (cov := cov) hmet (p := q) (u := v)
      (η := ξ)
  -- the covariant derivative of `W` at `0` is `ξ`
  have hWcov : Submission.JacobiGlobal.covAlong cov W 0 = ξ := by
    have hA0 : Submission.JacobiGlobal.covAlong cov (γ := fun t : ℝ =>
        Submission.GlobalExp.GExp (cov := cov) hmet q (t • (v + (0 : ℝ) • ξ)))
        (fun t : ℝ => Submission.Geodesic.curveVelocity (I := I)
          (fun r : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet q (t • (v + r • ξ))) 0) 0
        = ξ :=
      Work.OddBound.longHomotopy.covAlong_variation_zero (cov := cov) hmet htor (u := v) hvne
    have hgam : (fun t : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet q (t • v))
        = (fun t : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet q
            (t • (v + (0 : ℝ) • ξ))) := by
      funext t
      congr 1
      rw [zero_smul, add_zero]
    have hVl : ∀ t : ℝ, (show E from W t)
        = (show E from Submission.Geodesic.curveVelocity (I := I)
            (fun r : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet q (t • (v + r • ξ))) 0) := by
      intro t
      rw [hWdef]
    exact (hmod_covAlong_congr (cov := cov)
      (γ₁ := fun t : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet q (t • v))
      (γ₂ := fun t : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet q (t • (v + (0 : ℝ) • ξ)))
      hgam (V₁ := W) (V₂ := fun t : ℝ => Submission.Geodesic.curveVelocity (I := I)
        (fun r : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet q (t • (v + r • ξ))) 0)
      hVl 0).trans hA0
  -- hence `Z = W` by Jacobi uniqueness
  have hZW : ∀ t : ℝ, W t = Z t :=
    Work.Diff.C.geoCrux.jacobiUniqSmooth (E := E) (H := H) (I := I) (M := M) (cov := cov) htor
      (γ := fun t : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet q (t • v))
      (Submission.ConjEnergy.contMDiff_GExp_smul (cov := cov) hmet q hvne)
      (curveVelocity_GExp_ray_ne (cov := cov) hmet hv) (J := W) (Z := Z) hWJ hJ (t₀ := 0)
      (by rw [hW0, hZ0]) (by rw [hWcov, hξdef])
  -- the two pairings at the base point `q`
  have hpt : (fun t : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet q (t • v)) 0 = q := by
    show Submission.GlobalExp.GExp (cov := cov) hmet q ((0 : ℝ) • v) = q
    rw [zero_smul, Submission.GlobalExp.GExp_zero]
  have hξort : Inner.inner ℝ v ξ = 0 := by
    have horth_q : Inner.inner ℝ (show TangentSpace I q from
        (show E from Submission.JacobiGlobal.covAlong cov Z 0)) v = 0 := by
      rw [← hmod_inner_congr (I := I) hpt
        (show E from Submission.JacobiGlobal.covAlong cov Z 0) (show E from v)]
      exact horth
    rw [hξdef, real_inner_comm]
    exact horth_q
  have hnormξ : ‖ξ‖ = ‖Submission.JacobiGlobal.covAlong cov Z 0‖ := by
    rw [hξdef]
    exact (hmod_norm_congr (I := I) hpt
      (show E from Submission.JacobiGlobal.covAlong cov Z 0)).symm
  -- the modulus bound for the variation field
  -- the normalisation hypothesis in the form used by `VariationModulusProp`
  have hvin : Inner.inner ℝ v v = 1 := by
    rw [real_inner_self_eq_norm_sq, hv, one_pow]
  have hbound : ‖W ρ‖ ≤ (Real.sin ρ + 25 * ε₁) * ‖ξ‖ := by
    rw [hWdef]
    have hptρ : Submission.GlobalExp.GExp (cov := cov) hmet q (ρ • v)
        = Submission.GlobalExp.GExp (cov := cov) hmet q (ρ • (v + (0 : ℝ) • ξ)) := by
      congr 1
      rw [zero_smul, add_zero]
    exact le_of_eq_of_le (hmod_norm_congr (I := I) hptρ
      (show E from Submission.Geodesic.curveVelocity (I := I)
        (fun r : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet q (ρ • (v + r • ξ))) 0))
      (hvar (E := E) (H := H) (I := I) (M := M) (cov := cov) (c := c) (ε₁ := ε₁)
        hmet htor hc hc1 hε₁ hnum2 hsmC hHess hcont hgrad hcut q v hvin ρ hρ0 hρπ ξ hξort)
  calc ‖Z ρ‖ = ‖W ρ‖ := by rw [hZW ρ]
    _ ≤ (Real.sin ρ + 25 * ε₁) * ‖ξ‖ := hbound
    _ = (Real.sin ρ + 25 * ε₁) * ‖Submission.JacobiGlobal.covAlong cov Z 0‖ := by rw [hnormξ]

theorem hmod_prop : Work.Diff.C.geoCrux.HmodProp :=
  hmod_of_variation Work.Diff.C.geoCrux.variation_modulus

end

end Work.Diff.C.geoCrux
