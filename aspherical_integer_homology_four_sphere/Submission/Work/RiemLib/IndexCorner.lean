import Submission.Work.RiemLib.BonnetMyers
import Submission.Work.RiemLib.IndexForm2
import Submission.Work.RiemLib.CurvatureSym
import Submission.Work.RiemLib.SecondVar2

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# The second variation at a corner: the broken Jacobi field

This file develops the **index form with a corner**, the classical tool behind

* `σ ≤ κ` (the cut time is at most the first conjugate time, i.e. a minimising geodesic has no
  interior conjugate point),
* the Morse index theorem,
* the second variation of *closed* geodesics (Klingenberg's `ℓ ≥ 2π/√K`).

## Setting and content

Throughout, `(u,w)` is a unit-speed **chart geodesic** in the chart at `x₀` (a curve
`t ↦ γ t = (extChartAt I x₀).symm (u t)` with `γ' = w` and `∇_t w = 0`), `J` is a **Jacobi field**
along it, and `W` is a perturbation field.  The second variation of the energy of the
straight-line family is the integral of `indexIntegrand` (`Submission/BonnetMyers.lean`).

The new content is

* `Rq`, `Gq`: the two halves of the index integrand as bilinear forms on coordinate fields, with
  full bilinearity and the symmetry `Rq X Y = Rq Y X` (self-adjointness of `R(·,v)v`);
* `indexBilin`: the **polarisation** of `indexIntegrand` (the bilinear index form integrand),
  and `indexIntegrand_add`: its defining property
  `ℓ(V+εW) = ℓ(V) + 2ε·B(V,W) + ε²ℓ(W)`;
* `integral_indexBilin_of_jacobi`: **integration by parts along a Jacobi field**,
  `∫₀^{t₀} B(J,W) = -⟪∇J(t₀), W(t₀)⟫` for `J` a Jacobi field with `J 0 = J t₀ = 0`;
* `integral_indexIntegrand_of_jacobi`: the special case `W = J`,
  `∫₀^{t₀} ℓ(J) = 0` — the *broken Jacobi field* has vanishing index form, which is why a conjugate
  point forces a shortening.

-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

open LeanEval.Geometry.SphereTheorem
open scoped Manifold ContDiff Bundle Topology ENNReal
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter
open MeasureTheory
open scoped MeasureTheory
open Submission.Geodesic
open Submission.Jacobi
open Submission.ChartConnection
open Submission.ChartCurv
open Submission.CurvatureVec
open Submission.CurvatureSym
open Submission.Rauch
open Submission.Gauss
open Submission.Curvature
open Submission.SecondVariation
open Submission.ChartBounds
open Submission.BonnetMyers
open Submission.IndexForm
open Submission.IndexForm2
open Submission.SecondVar2

namespace Submission.IndexCorner

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M]
    [IsManifold I ∞ M]
  [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun (x : M) ↦ TangentSpace I x)]

noncomputable section

variable [I.Boundaryless]
variable {cov : CovariantDerivative I E (TangentSpace I (M := M))}

/-! ## The two halves of the index integrand, as bilinear forms -/

/-- The curvature half of the index integrand, as a bilinear form on the coordinate fields at a
point: `Rq p v X Y = ⟪X, R(Y,v)v⟫`. -/
noncomputable def Rq (cov : CovariantDerivative I E (TangentSpace I (M := M))) (x₀ : M) (p : M)
    (v X Y : E) : ℝ :=
  inner ℝ (frameVector (I := I) x₀ p X)
    (curvVec cov p (frameVector (I := I) x₀ p Y) (frameVector (I := I) x₀ p v)
      (frameVector (I := I) x₀ p v))

/-- The metric half of the index integrand, as a bilinear form on the coordinate fields at a
point: `Gq p X Y = ⟪X,Y⟫`. -/
noncomputable def Gq (x₀ : M) (p : M) (X Y : E) : ℝ :=
  chartGram (I := I) x₀ p X Y

/-- Symmetry of `Rq` (self-adjointness of `R(·,v)v`). -/
lemma Rq_symm [ContMDiffCovariantDerivative cov ∞] (hmet : IsMetricCompatible cov)
    (htor : cov.torsion = 0) (x₀ : M) (p : M) (v X Y : E) :
    Rq (cov := cov) x₀ p v X Y = Rq (cov := cov) x₀ p v Y X := by
  rw [Rq, Rq, real_inner_comm, inner_curvVec_self_adjoint (cov := cov) ‹_› htor hmet]

lemma Rq_add_left [ContMDiffCovariantDerivative cov ∞] (x₀ : M) (p : M) (v X₁ X₂ Y : E) :
    Rq (cov := cov) x₀ p v (X₁ + X₂) Y = Rq (cov := cov) x₀ p v X₁ Y
      + Rq (cov := cov) x₀ p v X₂ Y := by
  rw [Rq, Rq, Rq, frameVector_add, inner_add_left]

lemma Rq_add_right [ContMDiffCovariantDerivative cov ∞] (x₀ : M) (p : M) (v X Y₁ Y₂ : E) :
    Rq (cov := cov) x₀ p v X (Y₁ + Y₂) = Rq (cov := cov) x₀ p v X Y₁
      + Rq (cov := cov) x₀ p v X Y₂ := by
  rw [Rq, Rq, Rq, frameVector_add, curvVec_add_left (cov := cov) ‹_›, inner_add_right]

lemma Rq_smul_left [ContMDiffCovariantDerivative cov ∞] (x₀ : M) (p : M) (v : E) (c : ℝ)
    (X Y : E) :
    Rq (cov := cov) x₀ p v (c • X) Y = c * Rq (cov := cov) x₀ p v X Y := by
  rw [Rq, Rq, frameVector_smul, inner_smul_left, starRingEnd_apply, star_trivial]

lemma Rq_smul_right [ContMDiffCovariantDerivative cov ∞] (x₀ : M) (p : M) (v : E) (c : ℝ)
    (X Y : E) :
    Rq (cov := cov) x₀ p v X (c • Y) = c * Rq (cov := cov) x₀ p v X Y := by
  rw [Rq, Rq, frameVector_smul, curvVec_smul_left (cov := cov) ‹_›, inner_smul_right]

lemma Gq_add_left (x₀ : M) (p : M) (X₁ X₂ Y : E) :
    Gq (I := I) x₀ p (X₁ + X₂) Y = Gq (I := I) x₀ p X₁ Y + Gq (I := I) x₀ p X₂ Y :=
  chartGram_add_fst x₀ p X₁ X₂ Y

lemma Gq_add_right (x₀ : M) (p : M) (X Y₁ Y₂ : E) :
    Gq (I := I) x₀ p X (Y₁ + Y₂) = Gq (I := I) x₀ p X Y₁ + Gq (I := I) x₀ p X Y₂ :=
  chartGram_add_snd x₀ p X Y₁ Y₂

lemma Gq_smul_left (x₀ : M) (p : M) (c : ℝ) (X Y : E) :
    Gq (I := I) x₀ p (c • X) Y = c * Gq (I := I) x₀ p X Y :=
  chartGram_smul_fst x₀ p c X Y

lemma Gq_smul_right (x₀ : M) (p : M) (c : ℝ) (X Y : E) :
    Gq (I := I) x₀ p X (c • Y) = c * Gq (I := I) x₀ p X Y :=
  chartGram_smul_snd x₀ p c X Y

lemma Gq_symm (x₀ : M) (p : M) (X Y : E) :
    Gq (I := I) x₀ p X Y = Gq (I := I) x₀ p Y X :=
  chartGram_comm x₀ p X Y

/-- The curvature half of the index integrand is `Rq` applied to the field and the velocity. -/
lemma Rt_eq_Rq (x₀ : M) (u w η : ℝ → E) (t : ℝ) :
    Rt cov x₀ u η w t = Rq (cov := cov) x₀ ((extChartAt I x₀).symm (u t)) (w t) (η t) (η t) :=
  rfl

/-- The metric half of the index integrand is `Gq` applied to the covariant derivative. -/
lemma Gt_eq_Gq (x₀ : M) (u η w e : ℝ → E) (t : ℝ) :
    Gt cov x₀ u η w e t
      = Gq (I := I) x₀ ((extChartAt I x₀).symm (u t)) (DtQ cov x₀ u η w e t)
          (DtQ cov x₀ u η w e t) := rfl

/-- The index integrand is `Rq - Gq`. -/
lemma indexIntegrand_eq (x₀ : M) (u η w e : ℝ → E) (t : ℝ) :
    indexIntegrand cov x₀ u η w e t
      = Rq (cov := cov) x₀ ((extChartAt I x₀).symm (u t)) (w t) (η t) (η t)
        - Gq (I := I) x₀ ((extChartAt I x₀).symm (u t)) (DtQ cov x₀ u η w e t)
            (DtQ cov x₀ u η w e t) := rfl

/-! ## The polarised index integrand -/

/-- **The polarisation of the index integrand**: the bilinear form
`B(V,W) = ⟪V, R(W,γ')γ'⟫ - ⟪∇_tV, ∇_tW⟫` whose associated quadratic form is `indexIntegrand`. -/
noncomputable def indexBilin (cov : CovariantDerivative I E (TangentSpace I (M := M))) (x₀ : M)
    (u w V e W W' : ℝ → E) (t : ℝ) : ℝ :=
  Rq (cov := cov) x₀ ((extChartAt I x₀).symm (u t)) (w t) (V t) (W t)
    - Gq (I := I) x₀ ((extChartAt I x₀).symm (u t))
        (DtQ cov x₀ u V w e t) (DtQ cov x₀ u W w W' t)

/-- `indexBilin` in terms of `Rq` and `Gq`. -/
lemma indexBilin_eq (x₀ : M) (u w V e W W' : ℝ → E) (t : ℝ) :
    indexBilin cov x₀ u w V e W W' t
      = Rq (cov := cov) x₀ ((extChartAt I x₀).symm (u t)) (w t) (V t) (W t)
        - Gq (I := I) x₀ ((extChartAt I x₀).symm (u t))
            (DtQ cov x₀ u V w e t) (DtQ cov x₀ u W w W' t) := rfl

/-! ## Linearity of the covariant derivative in the field -/

/-- `DtQ` is linear in `(field, derivative)`. -/
lemma DtQ_add_smul (x₀ : M) (u w η e W W' : ℝ → E) (ε : ℝ) (t : ℝ) :
    DtQ cov x₀ u (fun s => η s + ε • W s) w (fun s => e s + ε • W' s) t
      = DtQ cov x₀ u η w e t + ε • DtQ cov x₀ u W w W' t := by
  simp only [DtQ, covDsP, fam, famP, zero_smul, add_zero, smul_add, chrB_add_snd,
    chrB_smul_snd]
  abel

/-! ## The expansion of the index integrand -/

/-- **The defining property of the polarised index integrand**: expanding the index integrand of the
sum of two fields produces the polarised form in the cross terms. -/
lemma indexIntegrand_add [ContMDiffCovariantDerivative cov ∞] (hmet : IsMetricCompatible cov)
    (htor : cov.torsion = 0) (x₀ : M) (u w η e W W' : ℝ → E) (ε : ℝ) (t : ℝ) :
    indexIntegrand cov x₀ u (fun s => η s + ε • W s) w (fun s => e s + ε • W' s) t
      = indexIntegrand cov x₀ u η w e t
        + 2 * ε * indexBilin cov x₀ u w η e W W' t
        + ε ^ 2 * indexIntegrand cov x₀ u W w W' t := by
  simp only [indexIntegrand_eq, indexBilin_eq,
    DtQ_add_smul (cov := cov) (x₀ := x₀) (u := u) (w := w) (η := η) (e := e) (W := W)
      (W' := W') (ε := ε) (t := t)]
  simp only [Rq_add_left, Rq_add_right, Gq_add_left, Gq_add_right, Rq_smul_left, Rq_smul_right,
    Gq_smul_left, Gq_smul_right]
  rw [Rq_symm (cov := cov) hmet htor (x₀ := x₀) ((extChartAt I x₀).symm (u t)) (w t)
    (W t) (η t),
    Gq_symm (x₀ := x₀) ((extChartAt I x₀).symm (u t))
      (DtQ cov x₀ u W w W' t) (DtQ cov x₀ u η w e t)]
  ring

/-! ## The chart form of the curvature half -/

/-- The curvature half of the index integrand, in terms of `chartCurv`. -/
lemma Rq_eq_chartGram_chartCurv [ContMDiffCovariantDerivative cov ∞] (htor : cov.torsion = 0)
    (x₀ : M) {p : M} (hp : p ∈ (chartAt H x₀).source) (v X Y : E) :
    Rq (cov := cov) x₀ p v X Y = chartGram (I := I) x₀ p X (chartCurv cov x₀ p Y v) := by
  rw [Rq, chartGram_apply, curvVec_frameVector_eq (cov := cov) htor x₀ hp Y v]

/-- `chartCovDeriv` agrees with `DtQ` when the derivative function is the actual derivative. -/
lemma chartCovDeriv_eq_DtQ (htor : cov.torsion = 0) (x₀ : M) {u w F F' : ℝ → E} {t : ℝ}
    (hsrc : (extChartAt I x₀).symm (u t) ∈ (chartAt H x₀).source)
    (hF : HasDerivAt F (F' t) t) :
    chartCovDeriv cov x₀ u w F t = DtQ cov x₀ u F w F' t := by
  have h1 : chartCovDeriv cov x₀ u w F t
      = deriv F t + christoffelLM cov x₀ ((extChartAt I x₀).symm (u t))
          (frameVector (I := I) x₀ ((extChartAt I x₀).symm (u t)) (w t)) (F t) := rfl
  have h2 : DtQ cov x₀ u F w F' t
      = F' t + chrB cov x₀ ((extChartAt I x₀).symm (u t)) (w t) (F t) := by
    simp only [DtQ, covDsP, fam, famP, zero_smul, add_zero]
  rw [h1, h2, hF.deriv]
  simp only [christoffelLM_apply (cov := cov) hsrc, chrB_apply,
    christoffelEval_comm htor x₀ ((extChartAt I x₀).symm (u t)) hsrc (w t) (F t)]

/-! ## The pointwise identity -/

/-- **The index integrand of a Jacobi field is minus the derivative of `⟪∇J, W⟫`.** -/
lemma indexBilin_eq_neg [ContMDiffCovariantDerivative cov ∞] (hmet : IsMetricCompatible cov)
    (htor : cov.torsion = 0) (x₀ : M)
    {u w J J' W W' : ℝ → E} {t : ℝ}
    (hsrc : (extChartAt I x₀).symm (u t) ∈ (chartAt H x₀).source)
    (hjac : DtDsP cov x₀ u J w J' t
      + chartCurv cov x₀ ((extChartAt I x₀).symm (u t)) (J t) (w t) = 0) :
    indexBilin cov x₀ u w J J' W W' t
      = - (chartGram (I := I) x₀ ((extChartAt I x₀).symm (u t))
            (DtDsP cov x₀ u J w J' t) (W t)
          + chartGram (I := I) x₀ ((extChartAt I x₀).symm (u t))
            (DtQ cov x₀ u J w J' t) (DtQ cov x₀ u W w W' t)) := by
  have hDj : DtDsP cov x₀ u J w J' t
      = - chartCurv cov x₀ ((extChartAt I x₀).symm (u t)) (J t) (w t) := by
    exact eq_neg_of_add_eq_zero_left hjac
  rw [indexBilin_eq, hDj]
  simp only [Gq, chartGram_neg_fst]
  rw [Rq_eq_chartGram_chartCurv (cov := cov) htor x₀ hsrc (w t) (J t) (W t),
    chartCurv_self_adjoint (cov := cov) ‹ContMDiffCovariantDerivative cov ∞› htor hmet x₀ hsrc
      (J t) (w t) (W t),
    chartGram_comm (I := I) x₀ ((extChartAt I x₀).symm (u t))]
  ring

/-! ## Integration by parts along a Jacobi field -/

/-- **Integration by parts along a Jacobi field.**  For `J` a Jacobi field along the chart geodesic
(with second covariant derivative `DtDsP`) and `W` a field with `W 0 = 0`, the integral of the
polarised index form is the negative of the boundary term `⟪∇J(t₀), W(t₀)⟫`. -/
theorem integral_indexBilin_of_jacobi [ContMDiffCovariantDerivative cov ∞]
    (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0) (x₀ : M)
    {u w w' J J' J'' W W' : ℝ → E} {t₀ : ℝ} (ht₀ : 0 < t₀)
    (hu : ∀ t ∈ Icc 0 t₀, HasDerivAt u (w t) t)
    (hw : ∀ t ∈ Icc 0 t₀, HasDerivAt w (w' t) t) (hwc : ContinuousOn w' (Icc 0 t₀))
    (htgt : ∀ t ∈ Icc 0 t₀, u t ∈ (extChartAt I x₀).target)
    (hJ : ∀ t ∈ Icc 0 t₀, HasDerivAt J (J' t) t) (hJc : ContinuousOn J' (Icc 0 t₀))
    (hJ' : ∀ t ∈ Icc 0 t₀, HasDerivAt J' (J'' t) t) (hJ''c : ContinuousOn J'' (Icc 0 t₀))
    (hjac : ∀ t ∈ Icc 0 t₀, DtDsP cov x₀ u J w J' t
      + chartCurv cov x₀ ((extChartAt I x₀).symm (u t)) (J t) (w t) = 0)
    (hW : ∀ t ∈ Icc 0 t₀, HasDerivAt W (W' t) t) (hWc : ContinuousOn W' (Icc 0 t₀))
    (hW0 : W 0 = 0) :
    ∫ t in (0 : ℝ)..t₀, indexBilin cov x₀ u w J J' W W' t
      = - chartGram (I := I) x₀ ((extChartAt I x₀).symm (u t₀))
          (DtQ cov x₀ u J w J' t₀) (W t₀) := by
  have huc : ContinuousOn u (Icc 0 t₀) := HasDerivAt.continuousOn hu
  have hwc0 : ContinuousOn w (Icc 0 t₀) := HasDerivAt.continuousOn hw
  have hJcont : ContinuousOn J (Icc 0 t₀) := HasDerivAt.continuousOn hJ
  have hWcont : ContinuousOn W (Icc 0 t₀) := HasDerivAt.continuousOn hW
  have hγc : ContinuousOn (fun t : ℝ => (extChartAt I x₀).symm (u t)) (Icc 0 t₀) :=
    continuousOn_chartCurve huc htgt
  have hsrc : ∀ t ∈ Icc 0 t₀, (extChartAt I x₀).symm (u t) ∈ (chartAt H x₀).source :=
    fun t ht => mem_source_chartCurve (I := I) (htgt t ht)
  have hQcont : ContinuousOn (DtQ cov x₀ u J w J') (Icc 0 t₀) :=
    continuousOn_covDsP_along (cov := cov) huc hJcont hwc0 hJc htgt
  have hRcont : ContinuousOn (DtQ cov x₀ u W w W') (Icc 0 t₀) :=
    continuousOn_covDsP_along (cov := cov) huc hWcont hwc0 hWc htgt
  have hQQcont : ContinuousOn (fun t : ℝ => DtDsP cov x₀ u J w J' t) (Icc 0 t₀) :=
    continuousOn_DtDsP (cov := cov) hu hw hJ hJ' hwc hJ''c htgt
  -- the product rule
  have hder : ∀ t ∈ Icc 0 t₀,
      HasDerivAt
        (fun s : ℝ => chartGram (I := I) x₀ ((extChartAt I x₀).symm (u s))
          (DtQ cov x₀ u J w J' s) (W s))
        (chartGram (I := I) x₀ ((extChartAt I x₀).symm (u t))
            (DtDsP cov x₀ u J w J' t) (W t)
          + chartGram (I := I) x₀ ((extChartAt I x₀).symm (u t))
            (DtQ cov x₀ u J w J' t) (DtQ cov x₀ u W w W' t)) t := by
    intro t ht
    have hstay : ∀ᶠ s in 𝓝 t, u s ∈ (extChartAt I x₀).target :=
      (hu t ht).continuousAt.preimage_mem_nhds
        ((isOpen_extChartAt_target x₀).mem_nhds (htgt t ht))
    have hdQ := hasDerivAt_covDsP_zero (cov := cov) (u := u) (η := J) (w := w) (e := J')
      (w' := w') (e' := J'') (hu t ht) (hw t ht) (hJ t ht) (hJ' t ht) (htgt t ht) hstay
    have hdW : HasDerivAt W (deriv W t) t :=
      (hW t ht).congr_deriv (hW t ht).deriv.symm
    have hpush := hasDerivAt_chartGram_curve (cov := cov) hmet x₀ (hu t ht) (htgt t ht) hstay
      (hdQ.congr_deriv hdQ.deriv.symm) hdW
    refine hpush.congr_deriv ?_
    have hQeq : deriv (fun r : ℝ => covDsP cov x₀ u J w J' 0 r) t
        + christoffelEval cov x₀ ((extChartAt I x₀).symm (u t))
            (covDsP cov x₀ u J w J' 0 t)
            (frameVector (I := I) x₀ ((extChartAt I x₀).symm (u t)) (w t))
        = DtDsP cov x₀ u J w J' t := by
      simp only [DtDsP, hdQ.deriv, chrB_apply]
    have hReq : deriv W t
        + christoffelEval cov x₀ ((extChartAt I x₀).symm (u t)) (W t)
            (frameVector (I := I) x₀ ((extChartAt I x₀).symm (u t)) (w t))
        = DtQ cov x₀ u W w W' t := by
      simp only [DtQ, covDsP, fam, famP, zero_smul, add_zero, chrB_apply, (hW t ht).deriv]
      rw [christoffelEval_comm htor x₀ ((extChartAt I x₀).symm (u t)) (hsrc t ht) (W t) (w t)]
    rw [hQeq, hReq]
    rfl
  have hF'cont : ContinuousOn (fun t : ℝ =>
      chartGram (I := I) x₀ ((extChartAt I x₀).symm (u t)) (DtDsP cov x₀ u J w J' t) (W t)
        + chartGram (I := I) x₀ ((extChartAt I x₀).symm (u t))
            (DtQ cov x₀ u J w J' t) (DtQ cov x₀ u W w W' t)) (Icc 0 t₀) :=
    (continuousOn_chartGram_curve (I := I) hγc hQQcont hWcont hsrc).add
      (continuousOn_chartGram_curve (I := I) hγc hQcont hRcont hsrc)
  have hint : IntervalIntegrable (fun t : ℝ =>
      chartGram (I := I) x₀ ((extChartAt I x₀).symm (u t)) (DtDsP cov x₀ u J w J' t) (W t)
        + chartGram (I := I) x₀ ((extChartAt I x₀).symm (u t))
            (DtQ cov x₀ u J w J' t) (DtQ cov x₀ u W w W' t)) volume 0 t₀ :=
    hF'cont.intervalIntegrable_of_Icc ht₀.le
  have hFTC : ∫ t in (0 : ℝ)..t₀,
      (chartGram (I := I) x₀ ((extChartAt I x₀).symm (u t)) (DtDsP cov x₀ u J w J' t) (W t)
        + chartGram (I := I) x₀ ((extChartAt I x₀).symm (u t))
            (DtQ cov x₀ u J w J' t) (DtQ cov x₀ u W w W' t))
      = chartGram (I := I) x₀ ((extChartAt I x₀).symm (u t₀))
          (DtQ cov x₀ u J w J' t₀) (W t₀)
        - chartGram (I := I) x₀ ((extChartAt I x₀).symm (u 0))
            (DtQ cov x₀ u J w J' 0) (W 0) :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt (by rwa [uIcc_of_le ht₀.le]) hint
  have hpoint : ∀ t ∈ uIcc (0 : ℝ) t₀, indexBilin cov x₀ u w J J' W W' t
      = - (chartGram (I := I) x₀ ((extChartAt I x₀).symm (u t))
              (DtDsP cov x₀ u J w J' t) (W t)
            + chartGram (I := I) x₀ ((extChartAt I x₀).symm (u t))
              (DtQ cov x₀ u J w J' t) (DtQ cov x₀ u W w W' t)) := by
    intro t ht
    rw [uIcc_of_le ht₀.le] at ht
    exact indexBilin_eq_neg (cov := cov) hmet htor x₀ (hsrc t ht) (hjac t ht)
  rw [intervalIntegral.integral_congr hpoint, intervalIntegral.integral_neg, hFTC, hW0,
    chartGram_zero_snd, sub_zero]

/-- **The index form of a broken Jacobi field vanishes.**  For a Jacobi field `J` along the chart
geodesic with `J 0 = J t₀ = 0`, the integral of the index integrand over `[0,t₀]` is zero.  This is
the reason a conjugate point forces a shortening: the *broken* field (`J` up to `t₀`, zero after)
has vanishing index form, so the linear term in the perturbation dominates. -/
theorem integral_indexIntegrand_of_jacobi [ContMDiffCovariantDerivative cov ∞]
    (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0) (x₀ : M)
    {u w w' J J' J'' : ℝ → E} {t₀ : ℝ} (ht₀ : 0 < t₀)
    (hu : ∀ t ∈ Icc 0 t₀, HasDerivAt u (w t) t)
    (hw : ∀ t ∈ Icc 0 t₀, HasDerivAt w (w' t) t) (hwc : ContinuousOn w' (Icc 0 t₀))
    (htgt : ∀ t ∈ Icc 0 t₀, u t ∈ (extChartAt I x₀).target)
    (hJ : ∀ t ∈ Icc 0 t₀, HasDerivAt J (J' t) t) (hJc : ContinuousOn J' (Icc 0 t₀))
    (hJ' : ∀ t ∈ Icc 0 t₀, HasDerivAt J' (J'' t) t) (hJ''c : ContinuousOn J'' (Icc 0 t₀))
    (hjac : ∀ t ∈ Icc 0 t₀, DtDsP cov x₀ u J w J' t
      + chartCurv cov x₀ ((extChartAt I x₀).symm (u t)) (J t) (w t) = 0)
    (hJ0 : J 0 = 0) (hJt : J t₀ = 0) :
    ∫ t in (0 : ℝ)..t₀, indexIntegrand cov x₀ u J w J' t = 0 := by
  have h := integral_indexBilin_of_jacobi (cov := cov) hmet htor x₀ ht₀ hu hw hwc htgt hJ hJc hJ'
    hJ''c hjac hJ hJc hJ0
  have h2 : chartGram (I := I) x₀ ((extChartAt I x₀).symm (u t₀))
      (DtQ cov x₀ u J w J' t₀) (J t₀) = 0 := by
    rw [hJt]
    simp
  rw [h2, neg_zero] at h
  have hgoal : ∫ t in (0 : ℝ)..t₀, indexIntegrand cov x₀ u J w J' t
      = ∫ t in (0 : ℝ)..t₀, indexBilin cov x₀ u w J J' J J' t :=
    intervalIntegral.integral_congr fun t ht => by rw [indexIntegrand_eq, indexBilin_eq]
  rw [hgoal, h]
/-! ## The second variation of the energy of a family with a corner -/

/-- **The second variation of the energy of a family with a corner.**  `(u,w)` is a chart geodesic on
`[0,L]`, `η` is a field which is `C¹` on `[0,t₀]` (derivative `e₁`) and on `[t₀,L]` (derivative
`e₂`), continuous at `t₀`, and vanishes at `0` and `L`.  Then the energy

`E(s) = ∫₀^{t₀} ⟪∂_tΨ,∂_tΨ⟫ + ∫_{t₀}^{L} ⟪∂_tΨ,∂_tΨ⟫`

of the straight-line family `Ψ(s,t) = u t + s·η t` has second derivative at `0`

`E''(0) = -2 ( ∫₀^{t₀} indexIntegrand(η,e₁) + ∫₀^{L-t₀} indexIntegrand(η(·+t₀),e₂(·+t₀)) )`.

The two pieces' boundary terms (`christoffel`-type, from the moving foot point) **cancel at `t₀`**
because `η` is continuous, and vanish at `0` and `L` because `η` does. -/
theorem fam2Energy_second_deriv_piecewise [ContMDiffCovariantDerivative cov ∞]
    (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0) (x₀ : M)
    {u w w' η e₁ e₂ : ℝ → E} {t₀ L : ℝ} (ht₀ : 0 < t₀) (hLt : t₀ < L)
    {a₁ a₂ : ℝ} (ha₁ : a₁ < 0) (ha₂ : 0 < a₂)
    (hu : ∀ t ∈ Icc 0 L, HasDerivAt u (w t) t) (hw : ∀ t ∈ Icc 0 L, HasDerivAt w (w' t) t)
    (hwc : ContinuousOn w' (Icc 0 L))
    (hη₁ : ∀ t ∈ Icc 0 t₀, HasDerivAt η (e₁ t) t) (he₁c : ContinuousOn e₁ (Icc 0 t₀))
    (hη₂ : ∀ t ∈ Icc t₀ L, HasDerivAt η (e₂ t) t) (he₂c : ContinuousOn e₂ (Icc t₀ L))
    (hgeo : ∀ t ∈ Icc 0 L, w' t + chrB cov x₀ ((extChartAt I x₀).symm (u t)) (w t) (w t) = 0)
    (hη0 : η 0 = 0) (hηL : η L = 0)
    (hstay : ∀ s ∈ Icc a₁ a₂, ∀ t ∈ Icc (-1) (L+2), fam u η s t ∈ (extChartAt I x₀).target)
    (htgt : ∀ t ∈ Icc 0 L, u t ∈ (extChartAt I x₀).target) :
    HasDerivAt
      (deriv (fun s =>
        fam2Energy (I := I) x₀ u η (fun _ => (0:E)) w e₁ (fun _ => (0:E)) t₀ s
        + fam2Energy (I := I) x₀ (fun τ : ℝ => u (t₀ + τ)) (fun τ : ℝ => η (t₀ + τ)) (fun _ => (0:E))
            (fun τ : ℝ => w (t₀ + τ)) (fun τ : ℝ => e₂ (t₀ + τ)) (fun _ => (0:E)) (L - t₀) s))
      (-2 * ((∫ t in (0 : ℝ)..t₀, indexIntegrand cov x₀ u η w e₁ t)
        + (∫ τ in (0 : ℝ)..(L - t₀), indexIntegrand cov x₀ (fun τ' : ℝ => u (t₀ + τ'))
            (fun τ' : ℝ => η (t₀ + τ')) (fun τ' : ℝ => w (t₀ + τ'))
            (fun τ' : ℝ => e₂ (t₀ + τ')) τ))) 0 := by
  classical
  -- ### The hypotheses of the two applications
  have ht₀L : t₀ ≤ L := hLt.le
  have hmem₀ : ∀ τ ∈ Icc (0:ℝ) (L - t₀), t₀ + τ ∈ Icc (0:ℝ) L := fun τ hτ =>
    ⟨by linarith [ht₀, hτ.1], by linarith [hτ.2]⟩
  have hmem₂ : ∀ τ ∈ Icc (0:ℝ) (L - t₀), t₀ + τ ∈ Icc t₀ L := fun τ hτ =>
    ⟨by linarith [hτ.1], by linarith [hτ.2]⟩
  have hshift₂ (f : ℝ → E) (hf : ContinuousOn f (Icc t₀ L)) :
      ContinuousOn (fun τ : ℝ => f (t₀ + τ)) (Icc 0 (L - t₀)) :=
    ContinuousOn.comp' hf
      ((continuousOn_const : ContinuousOn (fun _ : ℝ => t₀) (Icc 0 (L - t₀))).add
        continuousOn_id) (fun τ hτ => hmem₂ τ hτ)
  have hshiftc (f : ℝ → E) (hf : ContinuousOn f (Icc 0 L)) :
      ContinuousOn (fun τ : ℝ => f (t₀ + τ)) (Icc 0 (L - t₀)) := by
    exact ContinuousOn.comp' hf
      ((continuousOn_const : ContinuousOn (fun _ : ℝ => t₀) (Icc 0 (L - t₀))).add
        continuousOn_id) (fun τ hτ => hmem₀ τ hτ)
  have huc : ContinuousOn u (Icc 0 L) := HasDerivAt.continuousOn hu
  have hwc0 : ContinuousOn w (Icc 0 L) := HasDerivAt.continuousOn hw
  -- ### The two applications
  have hstay₁ : ∀ s ∈ Icc a₁ a₂, ∀ t ∈ Icc (-1) (t₀ + 2),
      fam2 u η (fun _ => (0 : E)) s t ∈ (extChartAt I x₀).target := by
    intro s hs t ht
    have hmem := hstay s hs t ⟨by linarith [ht.1], by linarith [ht.2, hLt.le, ht₀]⟩
    simpa only [fam2, fam, zero_smul, pow_two, zero_mul, zero_div, add_zero, smul_zero]
      using hmem
  have hstay₂ : ∀ s ∈ Icc a₁ a₂, ∀ t ∈ Icc (-1) ((L - t₀) + 2),
      fam2 (fun τ : ℝ => u (t₀ + τ)) (fun τ : ℝ => η (t₀ + τ)) (fun _ => (0 : E)) s t
        ∈ (extChartAt I x₀).target := by
    intro s hs t ht
    have hmem : fam u η s (t₀ + t) ∈ (extChartAt I x₀).target :=
      hstay s hs (t₀ + t) ⟨by linarith [ht.1, ht₀], by linarith [ht.2]⟩
    simpa only [fam2, fam, zero_smul, pow_two, zero_mul, zero_div, add_zero, smul_zero]
      using hmem
  have h1 := fam2Energy_second_deriv (I := I) (cov := cov) hmet htor x₀
    (ζ := fun _ => (0 : E)) (ζ' := fun _ => (0 : E)) (w := w) (e := e₁) (w' := w')
    (u := u) (η := η) (L := t₀) ht₀ ha₁ ha₂
    (fun t ht => hu t ⟨ht.1, ht.2.trans hLt.le⟩)
    (fun t ht => hw t ⟨ht.1, ht.2.trans hLt.le⟩)
    hη₁
    (fun _ _ => hasDerivAt_const _ (0 : E)) he₁c continuousOn_const
    (fun t ht => hgeo t ⟨ht.1, ht.2.trans hLt.le⟩)
    (A₀ := -1) (B₀ := t₀ + 2) (by norm_num) (by linarith) hstay₁
    (fun t ht => htgt t ⟨ht.1, ht.2.trans hLt.le⟩)
  have h2 := fam2Energy_second_deriv (I := I) (cov := cov) hmet htor x₀
    (ζ := fun _ => (0 : E)) (ζ' := fun _ => (0 : E))
    (u := fun τ : ℝ => u (t₀ + τ)) (η := fun τ : ℝ => η (t₀ + τ))
    (w := fun τ : ℝ => w (t₀ + τ)) (e := fun τ : ℝ => e₂ (t₀ + τ))
    (w' := fun τ : ℝ => w' (t₀ + τ)) (L := L - t₀) (by linarith)
    ha₁ ha₂
    (fun t ht => (hu (t₀ + t) (hmem₀ t ht)).comp_const_add t₀ t)
    (fun t ht => (hw (t₀ + t) (hmem₀ t ht)).comp_const_add t₀ t)
    (fun t ht => (hη₂ (t₀ + t) (hmem₂ t ht)).comp_const_add t₀ t)
    (fun _ _ => hasDerivAt_const _ (0 : E))
    (hshift₂ e₂ he₂c) continuousOn_const
    (fun t ht => by simpa only using hgeo (t₀ + t) (hmem₀ t ht))
    (A₀ := -1) (B₀ := (L - t₀) + 2) (by norm_num) (by linarith) hstay₂
    (fun t ht => htgt (t₀ + t) (hmem₀ t ht))
  -- ### The boundary terms cancel
  have hbdy1 : fam2A (cov := cov) x₀ u η (fun _ => (0 : E)) t₀
      = chrB cov x₀ ((extChartAt I x₀).symm (u t₀)) (η t₀) (η t₀) := by
    simp only [fam2A, zero_add]
  have hbdy10 : fam2A (cov := cov) x₀ u η (fun _ => (0 : E)) 0 = 0 := by
    simp only [fam2A, zero_add, hη0, chrB_zero_fst]
  have hbdy2 : fam2A (cov := cov) x₀ (fun τ : ℝ => u (t₀ + τ)) (fun τ : ℝ => η (t₀ + τ))
      (fun _ => (0 : E)) 0
      = chrB cov x₀ ((extChartAt I x₀).symm (u t₀)) (η t₀) (η t₀) := by
    simp only [fam2A, zero_add, add_zero]
  have hbdy2L : fam2A (cov := cov) x₀ (fun τ : ℝ => u (t₀ + τ)) (fun τ : ℝ => η (t₀ + τ))
      (fun _ => (0 : E)) (L - t₀) = 0 := by
    simp only [fam2A, zero_add, show t₀ + (L - t₀) = L from by ring, hηL, chrB_zero_fst]
  rw [hbdy1, hbdy10] at h1
  rw [hbdy2, hbdy2L] at h2
  simp only [chartGram_zero_fst, sub_zero, add_zero] at h1 h2
  -- ### Combine
  have hsum := h1.add h2
  have hev : (fun s : ℝ =>
        deriv (fun σ : ℝ => fam2Energy (I := I) x₀ u η (fun _ => (0:E)) w e₁ (fun _ => (0:E)) t₀ σ) s
        + deriv (fun σ : ℝ => fam2Energy (I := I) x₀ (fun τ : ℝ => u (t₀ + τ))
            (fun τ : ℝ => η (t₀ + τ)) (fun _ => (0:E)) (fun τ : ℝ => w (t₀ + τ))
            (fun τ : ℝ => e₂ (t₀ + τ)) (fun _ => (0:E)) (L - t₀) σ) s)
      =ᶠ[𝓝 (0:ℝ)]
      deriv (fun s : ℝ =>
        fam2Energy (I := I) x₀ u η (fun _ => (0:E)) w e₁ (fun _ => (0:E)) t₀ s
        + fam2Energy (I := I) x₀ (fun τ : ℝ => u (t₀ + τ)) (fun τ : ℝ => η (t₀ + τ)) (fun _ => (0:E))
            (fun τ : ℝ => w (t₀ + τ)) (fun τ : ℝ => e₂ (t₀ + τ)) (fun _ => (0:E)) (L - t₀) s) := by
    filter_upwards [isOpen_Ioo.mem_nhds (show (0:ℝ) ∈ Ioo a₁ a₂ from ⟨ha₁, ha₂⟩)] with s hs
    have hd1 : DifferentiableAt ℝ
        (fun σ : ℝ => fam2Energy (I := I) x₀ u η (fun _ => (0:E)) w e₁ (fun _ => (0:E)) t₀ σ) s :=
      (fam2Energy_hasDerivAt (I := I) (cov := cov) hmet x₀
        (ζ := fun _ => (0 : E)) (ζ' := fun _ => (0 : E)) (u := u) (η := η) (w := w) (e := e₁)
        (w' := w') (L := t₀) ht₀.le (a₁ := a₁) (a₂ := a₂) (δ₁ := (a₁ + s) / 2)
        (δ₂ := (s + a₂) / 2) (s₀ := s) (A₀ := -1) (B₀ := t₀ + 2)
        (by linarith [hs.1]) (by linarith [hs.2]) (by linarith [hs.1]) (by linarith [hs.2])
        (fun (t : ℝ) (ht : t ∈ Icc 0 t₀) => hu t ⟨ht.1, ht.2.trans hLt.le⟩)
        (fun (t : ℝ) (ht : t ∈ Icc 0 t₀) => hw t ⟨ht.1, ht.2.trans hLt.le⟩) hη₁
        (fun _ _ => hasDerivAt_const _ (0:E)) he₁c continuousOn_const
        (by norm_num) (by linarith) hstay₁).differentiableAt
    have hd2 : DifferentiableAt ℝ
        (fun σ : ℝ => fam2Energy (I := I) x₀ (fun τ : ℝ => u (t₀ + τ))
            (fun τ : ℝ => η (t₀ + τ)) (fun _ => (0:E)) (fun τ : ℝ => w (t₀ + τ))
            (fun τ : ℝ => e₂ (t₀ + τ)) (fun _ => (0:E)) (L - t₀) σ) s :=
      (fam2Energy_hasDerivAt (I := I) (cov := cov) hmet x₀
        (ζ := fun _ => (0 : E)) (ζ' := fun _ => (0 : E))
        (u := fun τ : ℝ => u (t₀ + τ)) (η := fun τ : ℝ => η (t₀ + τ))
        (w := fun τ : ℝ => w (t₀ + τ)) (e := fun τ : ℝ => e₂ (t₀ + τ))
        (w' := fun τ : ℝ => w' (t₀ + τ)) (L := L - t₀) (by linarith)
        (a₁ := a₁) (a₂ := a₂) (δ₁ := (a₁ + s) / 2) (δ₂ := (s + a₂) / 2) (s₀ := s)
        (A₀ := -1) (B₀ := (L - t₀) + 2)
        (by linarith [hs.1]) (by linarith [hs.2]) (by linarith [hs.1]) (by linarith [hs.2])
        (fun (t : ℝ) (ht : t ∈ Icc 0 (L - t₀)) => (hu (t₀ + t) (hmem₀ t ht)).comp_const_add t₀ t)
        (fun (t : ℝ) (ht : t ∈ Icc 0 (L - t₀)) => (hw (t₀ + t) (hmem₀ t ht)).comp_const_add t₀ t)
        (fun (t : ℝ) (ht : t ∈ Icc 0 (L - t₀)) => (hη₂ (t₀ + t) (hmem₂ t ht)).comp_const_add t₀ t)
        (fun _ _ => hasDerivAt_const _ (0:E)) (hshift₂ e₂ he₂c) continuousOn_const
        (by norm_num) (by linarith) hstay₂).differentiableAt
    have hd := deriv_add (f := fun σ : ℝ => fam2Energy (I := I) x₀ u η (fun _ => (0:E)) w e₁ (fun _ => (0:E)) t₀ σ)
      (g := fun σ : ℝ => fam2Energy (I := I) x₀ (fun τ : ℝ => u (t₀ + τ))
          (fun τ : ℝ => η (t₀ + τ)) 0 (fun τ : ℝ => w (t₀ + τ))
          (fun τ : ℝ => e₂ (t₀ + τ)) 0 (L - t₀) σ) hd1 hd2
    rw [show (fun σ : ℝ => fam2Energy (I := I) x₀ u η (fun _ => (0:E)) w e₁ (fun _ => (0:E)) t₀ σ
        + fam2Energy (I := I) x₀ (fun τ : ℝ => u (t₀ + τ)) (fun τ : ℝ => η (t₀ + τ)) (fun _ => (0:E))
            (fun τ : ℝ => w (t₀ + τ)) (fun τ : ℝ => e₂ (t₀ + τ)) (fun _ => (0:E)) (L - t₀) σ)
        = ((fun σ : ℝ => fam2Energy (I := I) x₀ u η (fun _ => (0:E)) w e₁ (fun _ => (0:E)) t₀ σ)
          + fun σ : ℝ => fam2Energy (I := I) x₀ (fun τ : ℝ => u (t₀ + τ))
              (fun τ : ℝ => η (t₀ + τ)) 0 (fun τ : ℝ => w (t₀ + τ))
              (fun τ : ℝ => e₂ (t₀ + τ)) 0 (L - t₀) σ) from rfl]
    exact hd.symm
  refine (hsum.congr_of_eventuallyEq hev.symm).congr_deriv ?_
  ring

end

end Submission.IndexCorner
