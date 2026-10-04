import Submission.ChartCurv

set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The Ricci identity for a straight-line variation, and the second variation of the energy

This file continues `Submission/ChartCurv.lean`.  We consider the **straight-line variation** of a
chart curve `u` in the direction of a coordinate field `η`,

`Ψ(s,t) = u t + s • η t`,

and the coordinate fields `P = ∂_t Ψ = w + s • e` and `Q = ∂_s Ψ = η` (where `w = u'`, `e = η'`).
Writing `Γ` for the chart Christoffel symbol `chrB` and `B` for its derivative in the base point
(`dB`), the covariant derivatives along the two parameters are

`D_t y = ∂_t y + Γ(y, P)`,   `D_s y = ∂_s y + Γ(y, Q)`.

The main theorem `ricci_chart_affine` is the **Ricci identity** for this family at `s = 0`:

`D_s D_t P - D_t D_s P = R(η, w)w`   (as tangent vectors at `γ t₀`),

where the right-hand side is `curvVec` applied to the frame vectors of the coordinate vectors
`e(t₀) = η'`, `w(t₀) = u'`.  This is the technical heart of the second-variation formula for the
energy (Bonnet–Myers).

The proof is: compute the two derivatives with the chain rule
`Submission.ChartCurv.hasDerivAt_chrB_curve`, and identify the resulting expression with
`Submission.ChartCurv.curvVec_eq_chart` (using the symmetry of the Christoffel symbol
`christoffelEval_comm`, which is torsion-freeness).

## Status and plan for the second variation (NEXT STEP)

`ricci_chart_affine` is the technical heart; what remains for **Bonnet–Myers** is:

1. the **energy** `E(s) = ∫ chartGram (γ_s t) (P(s,t)) (P(s,t)) dt` of the straight-line variation of
   a chart geodesic (`[0,L]`, unit speed, `η 0 = η L = 0`), with
   `E'(s) = 2 ∫ chartGram (D_s P) P` and (differentiating under the integral sign)
   `E''(0) = -2 ∫ chartGram (η, D_s D_t P)|_{s=0}` (the boundary terms at `t = 0, L` vanish because
   `η` vanishes there);
2. `D_t P|_{s=0} = 0` is the chart geodesic equation (`HasChartGeodesic`), and `D_s P = D_t η` for
   all `s` (Clairaut `∂_s P = ∂_t Q` plus the symmetry of `Γ`);
3. so, by `ricci_chart_affine`, `D_s D_t P|_{s=0} = D_t D_t η + R(η, w)w`, and integrating by parts
   (`D_t D_t η` against `η`, boundary terms vanish) gives the **index form**
   `E''(0) = 2 ∫ (chartGram (D_t η) (D_t η) - chartGram η (R(η,w)w)) dt`;
4. the pinching hypothesis `QuarterPinched` (`Submission/Curvature.quarterPinched_curvForm_bounds`,
   bridged to the chart by `curvVec_eq_chart` + `inner_curvVec_self`) bounds the curvature term
   from below by the Gram determinant; for `γ` a unit geodesic and `η = sin (π t / L) • E(t)` with
   `E` a **unit parallel field orthogonal to the velocity** (`exists_parallel_field_Icc`,
   `chartGram_parallel_const`) one gets `E''(0) ≤ 2 ∫ ((π/L)^2 - 1) sin^2 < 0` for `L > π`;
5. finally `E(s) < E(0) = L^2` for small `s > 0`, while `E(s) ≥ (length Φ_s)^2 / L ≥ L` by Cauchy–
   Schwarz (`Commons.Analysis.Calculus.sq_intervalIntegral_le_length_mul_intervalIntegral_sq`) and
   the minimality of the geodesic — contradiction, hence `diam M ≤ π`.
-/

set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false

open LeanEval.Geometry.SphereTheorem
open scoped Manifold ContDiff Bundle Topology
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter
open Submission.Geodesic
open Submission.ChartConnection
open Submission.ChartCurv
open Submission.CurvatureVec

namespace Submission.SecondVariation

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M]
    [IsManifold I ∞ M]
  [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun (x : M) ↦ TangentSpace I x)]

noncomputable section

variable {cov : CovariantDerivative I E (TangentSpace I (M := M))}

/-! ## The straight-line variation and its two covariant derivatives -/

/-- The straight-line family `Ψ(s,t) = u t + s • η t` in the chart at `x₀`. -/
def fam (u η : ℝ → E) (s t : ℝ) : E := u t + s • η t

/-- The `t`-velocity of the straight-line family, written with the explicit derivative functions
`w = u'` and `e = η'`: `∂_t Ψ (s,t) = w t + s • e t`. -/
def famP (w e : ℝ → E) (s t : ℝ) : E := w t + s • e t

/-- The covariant derivative along `t` of the velocity field `P` of the straight-line family:
`D_t P = ∂_t P + Γ(P, P)`, where `∂_t P (s,t) = w' t + s • e' t`. -/
def covDtP (cov : CovariantDerivative I E (TangentSpace I (M := M))) (x₀ : M)
    (u η w e w' e' : ℝ → E) (s t : ℝ) : E :=
  (w' t + s • e' t)
    + chrB cov x₀ ((extChartAt I x₀).symm (fam u η s t)) (famP w e s t) (famP w e s t)

/-- The covariant derivative along `s` of the velocity field `P` of the straight-line family:
`D_s P = ∂_s P + Γ(P, η)`, where `∂_s P (s,t) = e t`. -/
def covDsP (cov : CovariantDerivative I E (TangentSpace I (M := M))) (x₀ : M)
    (u η w e : ℝ → E) (s t : ℝ) : E :=
  e t + chrB cov x₀ ((extChartAt I x₀).symm (fam u η s t)) (famP w e s t) (η t)


/-! ## The chain rule for the Christoffel term of the variation -/

/-- Auxiliary: the derivative of the straight-line family in `s` at `0`. -/
lemma hasDerivAt_fam (u η : ℝ → E) (t₀ : ℝ) :
    HasDerivAt (fun s : ℝ => fam u η s t₀) (η t₀) 0 := by
  show HasDerivAt (fun s : ℝ => u t₀ + s • η t₀) (η t₀) 0
  have h1 : HasDerivAt (fun s : ℝ => s • η t₀) ((1 : ℝ) • η t₀) 0 :=
    (hasDerivAt_id (0 : ℝ)).smul_const (η t₀)
  rw [one_smul] at h1
  have h := (hasDerivAt_const (x := (0 : ℝ)) (c := u t₀)).add h1
  rw [zero_add] at h
  exact h

/-- Auxiliary: the derivative of the velocity field of the straight-line family in `s` at `0`. -/
lemma hasDerivAt_famP (w e : ℝ → E) (t₀ : ℝ) :
    HasDerivAt (fun s : ℝ => famP w e s t₀) (e t₀) 0 := by
  show HasDerivAt (fun s : ℝ => w t₀ + s • e t₀) (e t₀) 0
  have h1 : HasDerivAt (fun s : ℝ => s • e t₀) ((1 : ℝ) • e t₀) 0 :=
    (hasDerivAt_id (0 : ℝ)).smul_const (e t₀)
  rw [one_smul] at h1
  have h := (hasDerivAt_const (x := (0 : ℝ)) (c := w t₀)).add h1
  rw [zero_add] at h
  exact h

/-- **The chain rule in `s`** for the Christoffel term of the straight-line variation. -/
lemma hasDerivAt_chrB_fam_s [ContMDiffCovariantDerivative cov ∞]
    {x₀ : M} {u η w e : ℝ → E} {t₀ : ℝ}
    (htgt : u t₀ ∈ (extChartAt I x₀).target)
    (hstay : ∀ᶠ s in 𝓝 (0 : ℝ), fam u η s t₀ ∈ (extChartAt I x₀).target) :
    HasDerivAt (fun s : ℝ => chrB cov x₀ ((extChartAt I x₀).symm (fam u η s t₀))
        (famP w e s t₀) (famP w e s t₀))
      (dB cov x₀ ((extChartAt I x₀).symm (u t₀)) (η t₀) (w t₀) (w t₀)
        + chrB cov x₀ ((extChartAt I x₀).symm (u t₀)) (e t₀) (w t₀)
        + chrB cov x₀ ((extChartAt I x₀).symm (u t₀)) (w t₀) (e t₀)) 0 := by
  have hbase : HasDerivAt (fun s : ℝ => fam u η s t₀) (η t₀) 0 := hasDerivAt_fam u η t₀
  have hfield : HasDerivAt (fun s : ℝ => famP w e s t₀) (e t₀) 0 := hasDerivAt_famP w e t₀
  have h := hasDerivAt_chrB_curve (cov := cov) (x₀ := x₀) (v := η t₀) hbase hfield hfield
    (by simpa [fam] using htgt) hstay
  simpa [fam, famP] using h


/-- **The chain rule in `t`** for the Christoffel term `Γ(w(t))(η(t))` along the chart curve. -/
lemma hasDerivAt_chrB_fam_t [ContMDiffCovariantDerivative cov ∞]
    {x₀ : M} {u η w e w' : ℝ → E} {t₀ : ℝ}
    (hu : HasDerivAt u (w t₀) t₀) (hw : HasDerivAt w (w' t₀) t₀)
    (hη : HasDerivAt η (e t₀) t₀)
    (htgt : u t₀ ∈ (extChartAt I x₀).target)
    (hstay : ∀ᶠ t in 𝓝 t₀, u t ∈ (extChartAt I x₀).target) :
    HasDerivAt (fun t : ℝ => chrB cov x₀ ((extChartAt I x₀).symm (u t)) (w t) (η t))
      (dB cov x₀ ((extChartAt I x₀).symm (u t₀)) (w t₀) (w t₀) (η t₀)
        + chrB cov x₀ ((extChartAt I x₀).symm (u t₀)) (w' t₀) (η t₀)
        + chrB cov x₀ ((extChartAt I x₀).symm (u t₀)) (w t₀) (e t₀)) t₀ := by
  have h := hasDerivAt_chrB_curve (cov := cov) (x₀ := x₀) (v := w t₀) hu hw hη htgt hstay
  simpa using h


/-! ## The Ricci identity for the straight-line variation -/

/-- **The Ricci identity in coordinates for the straight-line variation.**  For the straight-line
variation `Ψ(s,t) = u t + s • η t` of a chart curve, with `P = ∂_tΨ = w + s • e` (`w = u'`,
`e = η'`), the commutator of the two covariant derivatives of `P` at `s = 0` is the curvature:

`[D_s, D_t] P = R(η, w) w`

where the left-hand side is computed in coordinates and the right-hand side is the intrinsic
curvature tensor `curvVec`. -/
theorem ricci_chart_affine [ContMDiffCovariantDerivative cov ∞] (htor : cov.torsion = 0)
    {x₀ : M} {u η w e w' e' : ℝ → E} {t₀ : ℝ}
    (hu : HasDerivAt u (w t₀) t₀) (hw : HasDerivAt w (w' t₀) t₀)
    (hη : HasDerivAt η (e t₀) t₀) (he : HasDerivAt e (e' t₀) t₀)
    (htgt : u t₀ ∈ (extChartAt I x₀).target)
    (hstay : ∀ᶠ s in 𝓝 (0 : ℝ), fam u η s t₀ ∈ (extChartAt I x₀).target)
    (hstayt : ∀ᶠ t in 𝓝 t₀, u t ∈ (extChartAt I x₀).target) :
    frameVector (I := I) x₀ ((extChartAt I x₀).symm (u t₀))
      (deriv (fun s : ℝ => covDtP cov x₀ u η w e w' e' s t₀) 0
        + chrB cov x₀ ((extChartAt I x₀).symm (u t₀))
            (covDtP cov x₀ u η w e w' e' 0 t₀) (η t₀)
        - (deriv (fun t : ℝ => covDsP cov x₀ u η w e 0 t) t₀
          + chrB cov x₀ ((extChartAt I x₀).symm (u t₀))
              (covDsP cov x₀ u η w e 0 t₀) (w t₀)))
      = curvVec cov ((extChartAt I x₀).symm (u t₀))
          (frameVector (I := I) x₀ ((extChartAt I x₀).symm (u t₀)) (η t₀))
          (frameVector (I := I) x₀ ((extChartAt I x₀).symm (u t₀)) (w t₀))
          (frameVector (I := I) x₀ ((extChartAt I x₀).symm (u t₀)) (w t₀)) := by
  have hp₀ : (extChartAt I x₀).symm (u t₀) ∈ (chartAt H x₀).source :=
    mem_source_chartCurve (I := I) (x₀ := x₀) htgt
  -- the two derivatives
  have hA : HasDerivAt (fun s : ℝ => w' t₀ + s • e' t₀) (e' t₀) 0 := by
    have h1' : HasDerivAt (fun s : ℝ => s • e' t₀) ((1 : ℝ) • e' t₀) 0 :=
      (hasDerivAt_id (0 : ℝ)).smul_const (e' t₀)
    rw [one_smul] at h1'
    have h := (hasDerivAt_const (x := (0 : ℝ)) (c := w' t₀)).add h1'
    rw [zero_add] at h
    exact h
  have h1 : HasDerivAt (fun s : ℝ => covDtP cov x₀ u η w e w' e' s t₀)
      (e' t₀ + (dB cov x₀ ((extChartAt I x₀).symm (u t₀)) (η t₀) (w t₀) (w t₀)
        + chrB cov x₀ ((extChartAt I x₀).symm (u t₀)) (e t₀) (w t₀)
        + chrB cov x₀ ((extChartAt I x₀).symm (u t₀)) (w t₀) (e t₀))) 0 := by
    have hB := hasDerivAt_chrB_fam_s (cov := cov) (x₀ := x₀) (u := u) (η := η) (w := w)
      (e := e) (t₀ := t₀) htgt hstay
    have h := hA.add hB
    have hfun : (fun s : ℝ => covDtP cov x₀ u η w e w' e' s t₀)
        = ((fun s : ℝ => w' t₀ + s • e' t₀) + fun s =>
            chrB cov x₀ ((extChartAt I x₀).symm (fam u η s t₀)) (famP w e s t₀)
              (famP w e s t₀)) := by
      funext s
      rfl
    rw [hfun]
    exact h
  have h2 : HasDerivAt (fun t : ℝ => covDsP cov x₀ u η w e 0 t)
      (e' t₀ + (dB cov x₀ ((extChartAt I x₀).symm (u t₀)) (w t₀) (w t₀) (η t₀)
        + chrB cov x₀ ((extChartAt I x₀).symm (u t₀)) (w' t₀) (η t₀)
        + chrB cov x₀ ((extChartAt I x₀).symm (u t₀)) (w t₀) (e t₀))) t₀ := by
    have hC : HasDerivAt (fun t : ℝ => e t + chrB cov x₀ ((extChartAt I x₀).symm (u t))
        (w t) (η t))
        (e' t₀ + (dB cov x₀ ((extChartAt I x₀).symm (u t₀)) (w t₀) (w t₀) (η t₀)
          + chrB cov x₀ ((extChartAt I x₀).symm (u t₀)) (w' t₀) (η t₀)
          + chrB cov x₀ ((extChartAt I x₀).symm (u t₀)) (w t₀) (e t₀))) t₀ :=
      he.add (hasDerivAt_chrB_fam_t (cov := cov) (x₀ := x₀) (u := u) (η := η) (w := w)
        (e := e) (w' := w') (t₀ := t₀) hu hw hη htgt hstayt)
    have hfun : (fun t : ℝ => covDsP cov x₀ u η w e 0 t)
        = (fun t : ℝ => e t + chrB cov x₀ ((extChartAt I x₀).symm (u t)) (w t) (η t)) := by
      funext t
      simp only [covDsP, fam, famP, zero_smul, add_zero, zero_add, smul_zero]
    rw [hfun]
    exact hC
  rw [h1.deriv, h2.deriv]
  -- simplify the values of the covariant derivatives at `s = 0`
  simp only [covDtP, covDsP, fam, famP, zero_smul, add_zero, zero_add, smul_zero]
  -- expand the Christoffel symbols by bilinearity
  rw [chrB_add_fst (cov := cov) x₀ ((extChartAt I x₀).symm (u t₀)) (w' t₀)
      (chrB cov x₀ ((extChartAt I x₀).symm (u t₀)) (w t₀) (w t₀)) (η t₀) hp₀,
    chrB_add_fst (cov := cov) x₀ ((extChartAt I x₀).symm (u t₀)) (e t₀)
      (chrB cov x₀ ((extChartAt I x₀).symm (u t₀)) (w t₀) (η t₀)) (w t₀) hp₀]
  -- identify the right-hand side with the curvature in coordinates
  rw [curvVec_eq_chart (cov := cov) (I := I) htor x₀ ((extChartAt I x₀).symm (u t₀))
    (w t₀) (w t₀) (η t₀) hp₀]
  congr 1
  abel


/-! ## Symmetry of the Christoffel symbol and the geodesic equation -/

/-- **Torsion-freeness makes the chart Christoffel symbol symmetric.** -/
lemma chrB_comm (htor : cov.torsion = 0) {x₀ p : M} (hp : p ∈ (chartAt H x₀).source) (a b : E) :
    chrB cov x₀ p a b = chrB cov x₀ p b a := by
  rw [chrB_apply, chrB_apply]
  exact christoffelEval_comm htor x₀ p hp a b

/-- The covariant derivative of the velocity field `P` of the straight-line variation along the
`t`-direction vanishes at `s = 0` when the underlying chart curve is a chart geodesic. -/
lemma covDtP_eq_zero_of_geodesic {x₀ : M} {u η w e w' e' : ℝ → E} {t : ℝ}
    (hgeo : w' t + chrB cov x₀ ((extChartAt I x₀).symm (u t)) (w t) (w t) = 0) :
    covDtP cov x₀ u η w e w' e' 0 t = 0 := by
  rw [covDtP]
  simp only [fam, famP, zero_smul, add_zero, zero_add, smul_zero]
  exact hgeo

/-- The covariant derivative of `P` in the `s`-direction is the covariant derivative of `Q = η` in
the `t`-direction (which is the coordinate form of `[∂_s, ∂_t] = 0` together with the symmetry of
the Christoffel symbol). -/
lemma covDsP_eq_covDtQ (htor : cov.torsion = 0) {x₀ : M} {u η w e : ℝ → E} {s t : ℝ}
    (hp : (extChartAt I x₀).symm (fam u η s t) ∈ (chartAt H x₀).source) :
    covDsP cov x₀ u η w e s t
      = e t + chrB cov x₀ ((extChartAt I x₀).symm (fam u η s t)) (η t) (famP w e s t) := by
  rw [covDsP, chrB_comm (cov := cov) htor hp]

end

end Submission.SecondVariation
