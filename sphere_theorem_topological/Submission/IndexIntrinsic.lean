import Submission.IndexCorner2
import Submission.ChartIndep

/-!
# The intrinsic index integrand

The chart index integrand `IndexCorner.indexIntegrand cov x₀ u η w e t` is only defined in a chart,
which is why `IndexCorner2`'s `σ ≤ κ` theorem needs the whole minimising segment to lie in **one**
chart: its energy comparison `L ≤ E(s)` uses the distance between the two endpoints of the chart
piece, and the perturbation fields are built in chart coordinates.

To globalise, one needs the index integrand as a **chart-free** object.  This file provides it:

* `idxAlong cov γ V Z t = ⟪Z t, Z t⟫ - ⟪R(V t, γ̇ t)γ̇ t, V t⟫` — a real number attached to a curve `γ`,
  a field `V` along `γ` and a field `Z` along `γ` playing the role of `∇V`.  It mentions no chart (it
  uses only the fibre inner product, `curvVec` and `curveVelocity`) and depends only on the *values*
  `V t`, `Z t` — never on derivatives of the chosen fields, so no extension of `V` to the ambient
  manifold is needed;
* `idxAlong_eq_neg_indexIntegrand` — **the chart identity**: `idxAlong` is the negative of
  `indexIntegrand` when read in a chart (`V` the frame field of `η`, `Z` the frame field of the
  covariant derivative `DtQ`), the two differing by the convention that the chart integrand is
  `Rq - Gq` while `idxAlong` is `Gq - Rq` with the curvature factor transposed;
* `integral_idxAlong_of_jacobiChart` — the corollary that the integral of `idxAlong` of a Jacobi
  field with `J 0 = J L = 0` vanishes, which is `IndexCorner.integral_indexIntegrand_of_jacobi` read
  through the chart identity.  Because `idxAlong` is now chart-free, *this integral is additive over
  any decomposition of `[0,L]`*, which is exactly what the global `σ ≤ κ` needs (see Roadmap §96.4
  and §96.5).

The hypotheses of `integral_idxAlong_of_jacobiChart` are on the closed interval `Icc (-1) (L+1)` for
the same reason as in `Submission/IndexMin.lean`: the chart data producer gives closed intervals,
while all the "eventually near `t`" statements follow because `t ∈ Icc 0 L` is interior.
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
open Submission.IndexCorner
open Submission.IndexCorner2
open Submission.ChartIndep

namespace Submission.IndexIntrinsic

noncomputable section

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M]
    [IsManifold I ∞ M]
  [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun (x : M) ↦ TangentSpace I x)]

variable [I.Boundaryless]
variable {cov : CovariantDerivative I E (TangentSpace I (M := M))}
variable [ContMDiffCovariantDerivative cov ∞]

/-- **The intrinsic index integrand.**  Along a curve `γ`, for a field `V` and a field `Z` playing the
role of its covariant derivative, the integrand of the index form is
`⟪Z,Z⟫ - ⟪R(V,γ̇)γ̇, V⟫`.
It mentions no chart: it uses only the fibre inner product, `curvVec` and `curveVelocity`, and it
depends only on the *values* `V t`, `Z t` (never on derivatives of the chosen fields), so it is
well-defined for a field along `γ` with no extension to the ambient manifold. -/
noncomputable def idxAlong (cov : CovariantDerivative I E (TangentSpace I (M := M))) (γ : ℝ → M)
    (V Z : (t : ℝ) → TangentSpace I (γ t)) (t : ℝ) : ℝ :=
  inner ℝ (Z t) (Z t)
    - inner ℝ (curvVec cov (γ t) (V t) (curveVelocity (I := I) γ t)
        (curveVelocity (I := I) γ t)) (V t)

/-- **The intrinsic index integrand is the negative of the chart index integrand.**  If near `t` the
curve `γ` is the chart curve of `u`, the velocity of `γ` is the chart velocity `w`, the field `V` is
the frame field of `η` and the field `Z` is the frame field of the *covariant* derivative
`DtQ cov x₀ u η w e`, then `idxAlong = - indexIntegrand`. -/
theorem idxAlong_eq_neg_indexIntegrand (htor : cov.torsion = 0) (x₀ : M)
    {γ : ℝ → M} {u w η e : ℝ → E} {V Z : (t : ℝ) → TangentSpace I (γ t)} {t : ℝ}
    (hsrc : γ t ∈ (chartAt H x₀).source)
    (hstay : ∀ᶠ s in 𝓝 t, u s ∈ (extChartAt I x₀).target)
    (hγeq : γ =ᶠ[𝓝 t] fun s => (extChartAt I x₀).symm (u s))
    (hu : ∀ᶠ s in 𝓝 t, HasDerivAt u (w s) s)
    (hγmd : MDifferentiableAt 𝓘(ℝ) I γ t)
    (hV : V t = frameVector (I := I) x₀ (γ t) (η t))
    (hZ : Z t = frameVector (I := I) x₀ (γ t) (DtQ cov x₀ u η w e t)) :
    idxAlong (cov := cov) γ V Z t = - indexIntegrand cov x₀ u η w e t := by
  have hvel : curveVelocity (I := I) γ t = frameVector (I := I) x₀ (γ t) (w t) :=
    (frameVector_chartVel_eq_curveVelocity (I := I) hsrc hstay hγeq hu hγmd).symm
  have hpt : γ t = (extChartAt I x₀).symm (u t) := hγeq.self_of_nhds
  have hcurv : curvVec cov (γ t) (frameVector (I := I) x₀ (γ t) (η t))
      (frameVector (I := I) x₀ (γ t) (w t)) (frameVector (I := I) x₀ (γ t) (w t))
      = frameVector (I := I) x₀ (γ t) (chartCurv cov x₀ (γ t) (η t) (w t)) :=
    curvVec_frameVector_eq (cov := cov) htor x₀ hsrc (η t) (w t)
  rw [idxAlong, hV, hZ, hvel]
  rw [indexIntegrand_eq, ← hpt]
  rw [Rq, Gq, chartGram_apply, hcurv,
    real_inner_comm (frameVector (I := I) x₀ (γ t) (η t))
      (frameVector (I := I) x₀ (γ t) (chartCurv cov x₀ (γ t) (η t) (w t)))]
  ring_nf

/-- **The index integral of a broken Jacobi field vanishes, in intrinsic form.**  For a Jacobi field
along a chart geodesic with `J 0 = J L = 0`, the integral of the *intrinsic* index integrand is
zero.  This is `IndexCorner.integral_indexIntegrand_of_jacobi` re-read through
`idxAlong_eq_neg_indexIntegrand`; its point is that the integrand is now a chart-free object, so the
statement can be glued across charts. -/
theorem integral_idxAlong_of_jacobiChart (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0)
    (x₀ : M) {u w w' J J' J'' : ℝ → E} {L : ℝ} (hL : 0 < L)
    (hu : ∀ t ∈ Icc (-1 : ℝ) (L + 1), HasDerivAt u (w t) t)
    (hw : ∀ t ∈ Icc (-1 : ℝ) (L + 1), HasDerivAt w (w' t) t)
    (hwc : ContinuousOn w' (Icc (-1 : ℝ) (L + 1)))
    (htgt : ∀ t ∈ Icc (-1 : ℝ) (L + 1), u t ∈ (extChartAt I x₀).target)
    (hJ : ∀ t ∈ Icc (-1 : ℝ) (L + 1), HasDerivAt J (J' t) t)
    (hJc : ContinuousOn J' (Icc (-1 : ℝ) (L + 1)))
    (hJ' : ∀ t ∈ Icc (-1 : ℝ) (L + 1), HasDerivAt J' (J'' t) t)
    (hJ''c : ContinuousOn J'' (Icc (-1 : ℝ) (L + 1)))
    (hjac : ∀ t ∈ Icc (-1 : ℝ) (L + 1), DtDsP cov x₀ u J w J' t
      + chartCurv cov x₀ ((extChartAt I x₀).symm (u t)) (J t) (w t) = 0)
    (hJ0 : J 0 = 0) (hJt : J L = 0) :
    ∫ t in (0 : ℝ)..L, idxAlong (cov := cov) (fun s : ℝ => (extChartAt I x₀).symm (u s))
        (fun t : ℝ => frameVector (I := I) x₀ ((extChartAt I x₀).symm (u t)) (J t))
        (fun t : ℝ => frameVector (I := I) x₀ ((extChartAt I x₀).symm (u t))
          (DtQ cov x₀ u J w J' t)) t = 0 := by
  have hsub : Icc (0:ℝ) L ⊆ Icc (-1 : ℝ) (L + 1) := fun t ht => ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have hkey : ∀ t ∈ uIcc (0:ℝ) L,
      idxAlong (cov := cov) (fun s : ℝ => (extChartAt I x₀).symm (u s))
        (fun t : ℝ => frameVector (I := I) x₀ ((extChartAt I x₀).symm (u t)) (J t))
        (fun t : ℝ => frameVector (I := I) x₀ ((extChartAt I x₀).symm (u t))
          (DtQ cov x₀ u J w J' t)) t = - indexIntegrand cov x₀ u J w J' t := by
    intro t ht
    rw [uIcc_of_le hL.le] at ht
    have ht' : t ∈ Icc (-1 : ℝ) (L + 1) := hsub ht
    have hsrc : (extChartAt I x₀).symm (u t) ∈ (chartAt H x₀).source :=
      mem_source_chartCurve (I := I) (htgt t ht')
    have hstay : ∀ᶠ s in 𝓝 t, u s ∈ (extChartAt I x₀).target :=
      (hu t ht').continuousAt.preimage_mem_nhds
        ((isOpen_extChartAt_target x₀).mem_nhds (htgt t ht'))
    have hγmd : MDifferentiableAt 𝓘(ℝ) I (fun s : ℝ => (extChartAt I x₀).symm (u s)) t :=
      mdifferentiableAt_chartCurve (I := I) (hu t ht') (htgt t ht') hstay
    exact idxAlong_eq_neg_indexIntegrand (cov := cov) htor x₀ hsrc hstay
      (Filter.EventuallyEq.refl _ _)
      (Filter.mem_of_superset (Icc_mem_nhds (by linarith [ht.1]) (by linarith [ht.2]))
        (fun s hs => hu s hs)) hγmd rfl rfl
  rw [intervalIntegral.integral_congr hkey, intervalIntegral.integral_neg,
    integral_indexIntegrand_of_jacobi (cov := cov) hmet htor x₀ hL
      (fun t ht => hu t (hsub ht)) (fun t ht => hw t (hsub ht)) (hwc.mono hsub)
      (fun t ht => htgt t (hsub ht)) (fun t ht => hJ t (hsub ht)) (hJc.mono hsub)
      (fun t ht => hJ' t (hsub ht)) (hJ''c.mono hsub) (fun t ht => hjac t (hsub ht)) hJ0 hJt,
    neg_zero]

end

end Submission.IndexIntrinsic
