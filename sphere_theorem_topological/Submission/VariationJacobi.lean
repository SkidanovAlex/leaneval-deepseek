import Submission.FlowJacobi

/-!
# The variation field of *any* smooth family of chart geodesics is Jacobi

`Submission/FlowJacobi.lean` proves that the `t`-variation field of the *geodesic-flow* family
`Φ (s,t) = sol (v + t • x) s` solves the chart Jacobi system, and identifies it with the column
`D.Y · x` of the Jacobi tensor.  Reading the proof closely (§83.3 of the roadmap), the three
lemmas that perform the V1/V2 computation —

* `hasDerivAt_variation` (`Yp Φ` differentiates to `Zp Φ`, by Clairaut's theorem),
* `hasDerivAt_variation_vel` (`Zp Φ` differentiates to the `t`-derivative of the geodesic vector
  field), and
* `deriv_chartGeodesicVectorField` (the value of that derivative, by the linearisation identity),

— use only `hδ`, `hTGT`, `hODE`, `hSM`, i.e. **only** that `Φ` is, near the relevant times, a
jointly smooth family of *chart geodesics* whose positions stay in the chart target.  The initial
conditions `(Φ (0,t)).1 = (extChartAt I x₀) x₀` and `(Φ (0,t)).2 = v + t • x` are used only
afterwards, in the uniqueness step that identifies the solution of the linear system with the
Jacobi-tensor column.

This file extracts that computation as a **standalone lemma** about an arbitrary such family — which
is exactly what the globalisation of the variation argument along a geodesic ray needs: a chart
taken at a point *along* the ray hosts a family of chart geodesics that does **not** emanate from
the chart centre, and its variation field must still be recognised as a Jacobi field.

## Contents

* `Ufun` — the second component of the solution pair attached to `Φ`: `Zp Φ` plus the
  Christoffel correction `chrB` (this was a local `set` inside `FlowJacobi`);
* `variationField_satisfies_jacobiSys` — the extracted computation.
-/

set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

open LeanEval.Geometry.SphereTheorem
open scoped Manifold ContDiff Bundle Topology ENNReal
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter
open Submission.Geodesic
open Submission.ChartConnection
open Submission.ChartCurv
open Submission.JacobiTensor
open Submission.Rauch
open Submission.RauchUpper
open Submission.SecondVariation
open Submission.SecondVar2
open Submission.FlowJacobi

namespace Submission.VariationJacobi

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

/-- The second component of the solution pair attached to the family `Φ`: the `t`-derivative of
the velocity plus the Christoffel correction comparing the velocity of the family with the tangent
vector `Yp Φ`. -/
def Ufun (x₀ : M) (Φ : ℝ × ℝ → E × E) : ℝ → E :=
  fun r => Zp Φ r + chrB cov x₀ ((extChartAt I x₀).symm ((Φ (r, 0)).1)) (Yp Φ r) (gv Φ r)

@[simp] lemma Ufun_apply (x₀ : M) (Φ : ℝ × ℝ → E × E) (r : ℝ) :
    Ufun (cov := cov) x₀ Φ r
      = Zp Φ r + chrB cov x₀ ((extChartAt I x₀).symm ((Φ (r, 0)).1)) (Yp Φ r) (gv Φ r) := rfl

/-- **The variation field of a smooth family of chart geodesics solves the chart Jacobi system.**
Let `Φ : ℝ × ℝ → E × E` be a family such that, for every `t` near `0`, the curve `s ↦ Φ (s,t)` is a
chart geodesic (with velocity `(Φ (s,t)).2`) staying inside the chart target, and suppose `Φ` is
jointly `C^∞` near `(s,0)` for `s ∈ (-2,2)`.  Then the pair
`(Yp Φ, Ufun x₀ Φ)` — the `t`-variation field and the corresponding velocity — satisfies the linear
Jacobi system on `[-1,1]`.

No hypothesis relates the family to the centre of the chart: this is the form needed when the chart
is taken at a point along a long geodesic. -/
theorem variationField_satisfies_jacobiSys (htor : cov.torsion = 0) {x₀ : M} {δ : ℝ}
    {Φ : ℝ × ℝ → E × E} (hδ : 0 < δ)
    (hTGT : ∀ t ∈ Ioo (-δ) δ, ∀ s ∈ Ioo (-2 : ℝ) 2,
      (Φ (s, t)).1 ∈ (extChartAt I x₀).target)
    (hODE : ∀ t ∈ Ioo (-δ) δ, ∀ s ∈ Ioo (-2 : ℝ) 2,
      HasDerivAt (fun s' : ℝ => Φ (s', t))
        ((Φ (s, t)).2, chartGeodesicVectorField cov x₀ (Φ (s, t))) s)
    (hSM : ∀ s ∈ Ioo (-2 : ℝ) 2, ContDiffAt ℝ ∞ (fun p : ℝ × ℝ => Φ p) (s, 0)) :
    ∀ t ∈ Icc (-1 : ℝ) 1,
      HasDerivAt (fun r : ℝ => (Yp Φ r, Ufun (cov := cov) x₀ Φ r))
        (jacobiSysVec (cov := cov) x₀ (gc Φ) (gv Φ) t (Yp Φ t, Ufun (cov := cov) x₀ Φ t)) t := by
  have h0 : (0 : ℝ) ∈ Ioo (-δ) δ := ⟨by linarith, hδ⟩
  have hsub : Icc (-1 : ℝ) 1 ⊆ Ioo (-2 : ℝ) 2 :=
    fun t ht => ⟨by linarith [ht.1], by linarith [ht.2]⟩
  intro t ht
  have ht2 : t ∈ Ioo (-2 : ℝ) 2 := hsub ht
  have hsrc : (extChartAt I x₀).symm ((Φ (t, 0)).1) ∈ (chartAt H x₀).source :=
    mem_source_chartCurve (I := I) (x₀ := x₀) (u := fun _ => (Φ (t, 0)).1) (t := 0)
      (hTGT 0 h0 t ht2)
  have hu : HasDerivAt (gc Φ) (gv Φ t) t := Submission.Gauss.hasDerivAt_fst (hODE 0 h0 t ht2)
  have hw : HasDerivAt (gv Φ) (chartGeodesicVectorField cov x₀ (Φ (t, 0))) t :=
    Submission.Gauss.hasDerivAt_snd (hODE 0 h0 t ht2)
  have hGCtarget : gc Φ t ∈ (extChartAt I x₀).target := hTGT 0 h0 t ht2
  have hGCtarget_ev : ∀ᶠ r in 𝓝 t, gc Φ r ∈ (extChartAt I x₀).target := by
    filter_upwards [isOpen_Ioo.mem_nhds ht2] with r hr
    exact hTGT 0 h0 r hr
  have hy : HasDerivAt (Yp Φ) (Zp Φ t) t :=
    hasDerivAt_variation (cov := cov) hδ hTGT hODE hSM ht2
  have hz := hasDerivAt_variation_vel (cov := cov) hδ hTGT hODE hSM ht2
  have hzval := deriv_chartGeodesicVectorField (cov := cov) hδ hTGT hODE hSM ht2
  have hchr : HasDerivAt
      (fun r : ℝ => chrB cov x₀ ((extChartAt I x₀).symm ((Φ (r, 0)).1)) (Yp Φ r) (gv Φ r))
      (dB cov x₀ ((extChartAt I x₀).symm ((Φ (t, 0)).1)) (gv Φ t) (Yp Φ t) (gv Φ t)
        + chrB cov x₀ ((extChartAt I x₀).symm ((Φ (t, 0)).1)) (Zp Φ t) (gv Φ t)
        + chrB cov x₀ ((extChartAt I x₀).symm ((Φ (t, 0)).1)) (Yp Φ t)
            (chartGeodesicVectorField cov x₀ (Φ (t, 0)))) t :=
    hasDerivAt_chrB_curve (cov := cov) (x₀ := x₀) (u := gc Φ) (a := Yp Φ) (b := gv Φ)
      (v := gv Φ t) (a' := Zp Φ t) (b' := chartGeodesicVectorField cov x₀ (Φ (t, 0)))
      hu hy hw hGCtarget hGCtarget_ev
  have hUderiv : HasDerivAt (Ufun (cov := cov) x₀ Φ)
      (deriv (fun r : ℝ => chartGeodesicVectorField cov x₀ (Φ (t, r))) 0
        + (dB cov x₀ ((extChartAt I x₀).symm ((Φ (t, 0)).1)) (gv Φ t) (Yp Φ t) (gv Φ t)
          + chrB cov x₀ ((extChartAt I x₀).symm ((Φ (t, 0)).1)) (Zp Φ t) (gv Φ t)
          + chrB cov x₀ ((extChartAt I x₀).symm ((Φ (t, 0)).1)) (Yp Φ t)
              (chartGeodesicVectorField cov x₀ (Φ (t, 0))))) t := by
    have h := hz.add hchr
    exact h
  have hgam : gammaOp (cov := cov) x₀ (gc Φ) (gv Φ) t (Yp Φ t)
      = chrB cov x₀ ((extChartAt I x₀).symm ((Φ (t, 0)).1)) (Yp Φ t) (gv Φ t) :=
    gammaOp_apply (cov := cov) (x₀ := x₀) (u := gc Φ) (w := gv Φ) (t := t) hsrc (Yp Φ t)
  have hgamU : gammaOp (cov := cov) x₀ (gc Φ) (gv Φ) t (Ufun (cov := cov) x₀ Φ t)
      = chrB cov x₀ ((extChartAt I x₀).symm ((Φ (t, 0)).1))
          (Ufun (cov := cov) x₀ Φ t) (gv Φ t) :=
    gammaOp_apply (cov := cov) (x₀ := x₀) (u := gc Φ) (w := gv Φ) (t := t) hsrc
      (Ufun (cov := cov) x₀ Φ t)
  have hcurv : curvOp (cov := cov) x₀ (gc Φ) (gv Φ) t (Yp Φ t)
      = chartCurv cov x₀ ((extChartAt I x₀).symm ((Φ (t, 0)).1)) (Yp Φ t) (gv Φ t) :=
    curvOp_apply (cov := cov) (x₀ := x₀) (u := gc Φ) (w := gv Φ) (t := t) hsrc (Yp Φ t)
  have hbase := hy.prodMk hUderiv
  rw [jacobiSysVec_apply]
  refine hbase.congr_deriv ?_
  refine Prod.ext ?_ ?_
  · simp only [hgam, Ufun_apply]
    abel
  · have hgv : chartGeodesicVectorField cov x₀ (Φ (t, 0))
        = - chrB cov x₀ ((extChartAt I x₀).symm ((Φ (t, 0)).1)) (gv Φ t) (gv Φ t) := rfl
    have hid := linearization_identity (cov := cov) htor x₀ hsrc (Yp Φ t) (Zp Φ t) (gv Φ t)
    rw [hzval, hgamU, hcurv, hgv, Ufun_apply, hid]

end

end Submission.VariationJacobi
