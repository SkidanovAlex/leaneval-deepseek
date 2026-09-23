import Mathlib
import Submission.Work.OddBound.PiExtChart

namespace Work.OddBound

open LeanEval.Geometry.SphereTheorem
open scoped Manifold ContDiff Bundle Topology ENNReal
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter
open MeasureTheory
open scoped MeasureTheory Interval
open Submission.Geodesic Submission.JacobiGlobal Submission.GlobalExp Submission.Length
open Submission.InjRadius Submission.IndexIntrinsic Submission.CurvatureVec

/-- **Chart-critical points of the polygon energy are intrinsically critical.**

If `w` lies in the source of the product extended chart `piExtChart x` and the chart expression
`u ↦ gonEnergy p ((piExtChart x).symm u)` of the polygon energy is differentiable at `(piExtChart x) w`
with vanishing derivative there, then `w` is a critical point of the polygon energy in the intrinsic
sense `GonCritical`: the energy has vanishing first variation along every smooth curve that moves a
single interior vertex.

The proof is the chain rule.  For a fixed vertex `i` and a smooth curve `γ` with `γ 0 = w i`, the
polygon `t ↦ Function.update w i (γ t)` writes in the chart as the curve
`t ↦ Function.update ((piExtChart x) w) i (extChartAt I (x i) (γ t))`, which is differentiable at
`0` because `Function.update` is an affine map and the extended chart is `C^∞` on its source along
the smooth curve `γ`.  Composing with the (differentiable, critical) chart expression and using
`(piExtChart x).symm ∘ (piExtChart x) = id` near `w` gives the result. -/
theorem gonCritical_of_piExtChart_critical
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ∞ M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
    [I.Boundaryless] [Nontrivial E]
    {N : ℕ} {p : M} {x w : Fin (N - 1) → M}
    (hwsrc : w ∈ (Work.OddBound.piExtChart (I := I) x).source)
    (hdiff : DifferentiableAt ℝ
      (fun u : (Fin (N - 1)) → E =>
        Work.OddBound.gonEnergy (I := I) p ((Work.OddBound.piExtChart (I := I) x).symm u))
      ((Work.OddBound.piExtChart (I := I) x) w))
    (hcrit : fderiv ℝ
      (fun u : (Fin (N - 1)) → E =>
        Work.OddBound.gonEnergy (I := I) p ((Work.OddBound.piExtChart (I := I) x).symm u))
      ((Work.OddBound.piExtChart (I := I) x) w) = 0) :
    Work.OddBound.GonCritical (I := I) p w := by
  intro i γ hγ hγ0
  -- Each vertex of the polygon `w` lies in the source of its extended chart.
  have hsrc : ∀ j : Fin (N - 1), w j ∈ (Work.OddBound.extChartHomeo (I := I) (x j)).source := by
    have h := hwsrc
    simp only [Work.OddBound.piExtChart, OpenPartialHomeomorph.pi, PartialEquiv.pi_source,
      Set.mem_pi, Set.mem_univ, true_implies] at h
    exact h
  -- The chart coordinates of the moved polygon: `Function.update` commutes with the product chart.
  have hupd : ∀ t : ℝ,
      Function.update ((Work.OddBound.piExtChart (I := I) x) w) i (extChartAt I (x i) (γ t)) =
        (Work.OddBound.piExtChart (I := I) x) (Function.update w i (γ t)) := by
    intro t
    funext j
    simp only [Work.OddBound.piExtChart, OpenPartialHomeomorph.pi_apply, Function.update_apply,
      Work.OddBound.extChartHomeo_coe, extChartAt_coe]
    by_cases h : j = i <;> simp_all
  -- Near `t = 0` the moved polygon stays in the source of the product chart.
  have hγsrc : γ 0 ∈ (Work.OddBound.extChartHomeo (I := I) (x i)).source := by
    rw [hγ0]; exact hsrc i
  have hmem : ∀ᶠ t in 𝓝 0, γ t ∈ (Work.OddBound.extChartHomeo (I := I) (x i)).source :=
    hγ.continuous.continuousAt.preimage_mem_nhds
      ((Work.OddBound.extChartHomeo (I := I) (x i)).open_source.mem_nhds hγsrc)
  have hev : ∀ᶠ t in 𝓝 0,
      Function.update w i (γ t) ∈ (Work.OddBound.piExtChart (I := I) x).source := by
    refine Filter.mem_of_superset hmem (fun t ht => ?_)
    simp only [Work.OddBound.piExtChart, OpenPartialHomeomorph.pi, PartialEquiv.pi_source,
      Set.mem_pi, Set.mem_univ, true_implies]
    intro j
    by_cases h : j = i
    · subst h; simpa using ht
    · simp only [Function.update_apply, if_neg h]; exact hsrc j
  -- The extended chart is smooth along `γ`, so the chart curve of the moved vertex is
  -- differentiable at `0`.
  have hchart : ContMDiffAt 𝓘(ℝ) 𝓘(ℝ, E) ∞ (fun t : ℝ => extChartAt I (x i) (γ t)) 0 :=
    (contMDiffAt_extChartAt' (I := I) (x := x i) (n := ∞) hγsrc).comp 0 hγ.contMDiffAt
  have hηdiff : DifferentiableAt ℝ (fun t : ℝ => extChartAt I (x i) (γ t)) 0 :=
    (hchart.contDiffAt).differentiableAt (by simp)
  have hη0 : extChartAt I (x i) (γ 0) = (Work.OddBound.piExtChart (I := I) x) w i := by
    rw [hγ0, Work.OddBound.piExtChart, OpenPartialHomeomorph.pi_apply,
      Work.OddBound.extChartHomeo_coe, extChartAt_coe]
    rfl
  have hcdiff : DifferentiableAt ℝ
      (fun t : ℝ => Function.update ((Work.OddBound.piExtChart (I := I) x) w) i
        (extChartAt I (x i) (γ t))) 0 :=
    (HasFDerivAt.comp (x := (0 : ℝ))
      (f := fun t : ℝ => extChartAt I (x i) (γ t))
      (f' := fderiv ℝ (fun t : ℝ => extChartAt I (x i) (γ t)) 0)
      (g := Function.update ((Work.OddBound.piExtChart (I := I) x) w) i)
      (g' := ContinuousLinearMap.pi (Pi.single i (ContinuousLinearMap.id ℝ E)))
      (hg := hasFDerivAt_update (i := i) ((Work.OddBound.piExtChart (I := I) x) w)
        (extChartAt I (x i) (γ 0)))
      (hf := hηdiff.hasFDerivAt)).differentiableAt
  -- The chart expression of the energy is differentiable and critical at the chart image of `w`.
  have hG' : HasFDerivAt
      (fun u : (Fin (N - 1)) → E =>
        Work.OddBound.gonEnergy (I := I) p ((Work.OddBound.piExtChart (I := I) x).symm u))
      (fderiv ℝ (fun u : (Fin (N - 1)) → E =>
        Work.OddBound.gonEnergy (I := I) p ((Work.OddBound.piExtChart (I := I) x).symm u))
        ((Work.OddBound.piExtChart (I := I) x) w))
      (Function.update ((Work.OddBound.piExtChart (I := I) x) w) i (extChartAt I (x i) (γ 0))) := by
    rw [hη0, Function.update_eq_self]
    exact hdiff.hasFDerivAt
  -- Chain rule: the composition has vanishing derivative at `0`.
  have hchain : HasFDerivAt
      ((fun u : (Fin (N - 1)) → E =>
        Work.OddBound.gonEnergy (I := I) p ((Work.OddBound.piExtChart (I := I) x).symm u)) ∘
       (fun t : ℝ => Function.update ((Work.OddBound.piExtChart (I := I) x) w) i
        (extChartAt I (x i) (γ t)))) (0 : ℝ →L[ℝ] ℝ) (0 : ℝ) := by
    have h := HasFDerivAt.comp (x := (0 : ℝ))
      (f := fun t : ℝ => Function.update ((Work.OddBound.piExtChart (I := I) x) w) i
        (extChartAt I (x i) (γ t)))
      (f' := fderiv ℝ (fun t : ℝ => Function.update ((Work.OddBound.piExtChart (I := I) x) w) i
        (extChartAt I (x i) (γ t))) 0)
      (g := fun u : (Fin (N - 1)) → E =>
        Work.OddBound.gonEnergy (I := I) p ((Work.OddBound.piExtChart (I := I) x).symm u))
      (g' := fderiv ℝ (fun u : (Fin (N - 1)) → E =>
        Work.OddBound.gonEnergy (I := I) p ((Work.OddBound.piExtChart (I := I) x).symm u))
        ((Work.OddBound.piExtChart (I := I) x) w))
      (hg := hG') (hf := hcdiff.hasFDerivAt)
    simpa only [hcrit, ContinuousLinearMap.zero_comp] using h
  -- The genuine energy along the moving vertex agrees with the composed chart expression.
  have hcongr : (fun t : ℝ => Work.OddBound.gonEnergy (I := I) p (Function.update w i (γ t)))
      =ᶠ[𝓝 0]
      ((fun u : (Fin (N - 1)) → E =>
        Work.OddBound.gonEnergy (I := I) p ((Work.OddBound.piExtChart (I := I) x).symm u)) ∘
       (fun t : ℝ => Function.update ((Work.OddBound.piExtChart (I := I) x) w) i
        (extChartAt I (x i) (γ t)))) := by
    filter_upwards [hev] with t ht
    simp only [Function.comp_apply]
    rw [hupd t, OpenPartialHomeomorph.left_inv (Work.OddBound.piExtChart (I := I) x) ht]
  simpa using (hchain.congr_of_eventuallyEq hcongr).hasDerivAt

end Work.OddBound
