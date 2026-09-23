import Submission.RauchGlobal
import Submission.CoeffSmooth2
import Submission.JacobiTensor

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

open LeanEval.Geometry.SphereTheorem
open scoped Manifold ContDiff Bundle Topology ENNReal
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter
open Submission.Geodesic
open Submission.ChartConnection
open Submission.Jacobi
open Submission.ChartCurv
open Submission.Rauch
open Submission.JacobiTensor
open Submission.RauchGlobal


/-!
# The local data of a Jacobi field in first-order system form, and `C^∞` regularity

`Submission.RauchGlobal.IsJacobiAt` packages a Jacobi field as `C¹`-level chart data plus the
*second-order* chart Jacobi equation `D(Dy) + R(y,w)w = 0`.  The variational theorems
(`Submission.SecondVarGlobal`, `Submission.IndexIntrinsic2`) need the data in the
**first-order system** form

  `y' = z - Γ(w)∘y`,  `z' = -Γ(w)∘z - R(y,w)w`   with `z = chartCovDeriv x₀ u w y`,

and, for the *smoothness* hypotheses of the second-variation theorems, they need the coordinate
function `y` to be `C^∞`.

* `isJacobiAt_system`: `IsJacobiAt` data, rewritten in the system form (Theorem 1);
* `contDiffOn_of_isJacobiSystem`: if the base curve's coordinates `u, w` are `C^∞` on an open
  interval and the system holds on it, then the field's coordinate function `y` is `C^∞` on every
  closed subinterval — this is `Submission.Coeff.contDiffOn_of_jacobiSolution` fed with the
  definitional identities `chartCovDeriv = deriv + Γ` and `curvOp = chartCurv (·)(w)`.

Together they turn the `IsJacobiAt` data of a conjugate field (which holds at *every* point of the
minimising segment) into the `C^∞` per-piece chart data consumed by
`Submission.SecondVarGlobal.energy_second_deriv_piece`.
-/

namespace Submission.JacobiAtSystem

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

/-- **The local data of a Jacobi field, in first-order system form.**  With
`z := chartCovDeriv x₀ u w y` the second-order Jacobi equation
`D(Dy) + R(y,w)w = 0` reads `y' = z - Γ(w)∘y`, `z' = -Γ(w)∘z - R(y,w)w`. -/
theorem isJacobiAt_system (htor : cov.torsion = 0)
    {γ : ℝ → M} {J : (t : ℝ) → TangentSpace I (γ t)} {t : ℝ} (hJ : IsJacobiAt cov γ J t) :
    ∃ (x₀ : M) (u w y : ℝ → E) (ρ : ℝ), 0 < ρ ∧
      (∀ s ∈ Ioo (t - ρ) (t + ρ), u s ∈ (extChartAt I x₀).target) ∧
      (∀ s ∈ Ioo (t - ρ) (t + ρ), HasDerivAt u (w s) s) ∧
      (∀ s ∈ Ioo (t - ρ) (t + ρ), γ s = (extChartAt I x₀).symm (u s)) ∧
      (∀ s ∈ Ioo (t - ρ) (t + ρ), frameVector (I := I) x₀ (γ s) (y s) = J s) ∧
      (∀ s ∈ Ioo (t - ρ) (t + ρ),
        HasDerivAt y (chartCovDeriv cov x₀ u w y s - gammaOp (cov := cov) x₀ u w s (y s)) s) ∧
      (∀ s ∈ Ioo (t - ρ) (t + ρ),
        HasDerivAt (chartCovDeriv cov x₀ u w y)
          (-(gammaOp (cov := cov) x₀ u w s (chartCovDeriv cov x₀ u w y s))
            - curvOp (cov := cov) x₀ u w s (y s)) s) ∧
      (ContinuousOn y (Ioo (t - ρ) (t + ρ))) ∧
      (ContinuousOn (chartCovDeriv cov x₀ u w y) (Ioo (t - ρ) (t + ρ))) := by
  obtain ⟨x₀, u, w, y, ρ, hρ, htgt, hu, hγeq, hJeq, hunit, hy, hyz, hjac⟩ :=
    exists_local_data (cov := cov) hJ
  have hzval : ∀ s ∈ Ioo (t - ρ) (t + ρ),
      chartCovDeriv cov x₀ u w y s - gammaOp (cov := cov) x₀ u w s (y s) = deriv y s := by
    intro s hs
    have hsrc : (extChartAt I x₀).symm (u s) ∈ (chartAt H x₀).source :=
      mem_source_chartCurve (I := I) (htgt s hs)
    rw [chartCovDeriv_apply (cov := cov) (htgt s hs), gammaOp_apply (cov := cov) hsrc]
    abel
  have hzderiv : ∀ s ∈ Ioo (t - ρ) (t + ρ),
      deriv (chartCovDeriv cov x₀ u w y) s
        = -(gammaOp (cov := cov) x₀ u w s (chartCovDeriv cov x₀ u w y s))
          - curvOp (cov := cov) x₀ u w s (y s) := by
    intro s hs
    have hsrc : (extChartAt I x₀).symm (u s) ∈ (chartAt H x₀).source :=
      mem_source_chartCurve (I := I) (htgt s hs)
    have h1 : chartCovDeriv cov x₀ u w (chartCovDeriv cov x₀ u w y) s
        = deriv (chartCovDeriv cov x₀ u w y) s
          + gammaOp (cov := cov) x₀ u w s (chartCovDeriv cov x₀ u w y s) := by
      rw [chartCovDeriv_apply (cov := cov) (htgt s hs), gammaOp_apply (cov := cov) hsrc]
    have h2 : chartCovDeriv cov x₀ u w (chartCovDeriv cov x₀ u w y) s
        = - curvOp (cov := cov) x₀ u w s (y s) := by
      have h := hjac s hs
      rw [← curvOp_apply (cov := cov) hsrc] at h
      exact eq_neg_of_add_eq_zero_left h
    rw [h2] at h1
    have h5 : deriv (chartCovDeriv cov x₀ u w y) s
        = -(curvOp (cov := cov) x₀ u w s (y s))
          - gammaOp (cov := cov) x₀ u w s (chartCovDeriv cov x₀ u w y s) :=
      (sub_eq_iff_eq_add.mpr h1).symm
    rw [h5]
    abel
  refine ⟨x₀, u, w, y, ρ, hρ, htgt, hu, hγeq, hJeq, ?_, ?_, ?_, ?_⟩
  · intro s hs
    rw [hzval s hs]
    exact hy s hs
  · intro s hs
    exact (hyz s hs).congr_deriv (hzderiv s hs)
  · exact isOpen_Ioo.continuousOn_iff.mpr (fun s hs => (hy s hs).continuousAt)
  · exact isOpen_Ioo.continuousOn_iff.mpr (fun s hs => (hyz s hs).continuousAt)

/-- **The coordinates of a local Jacobi field are `C^∞`.**  If the first-order Jacobi system holds on
an interval (in the form of `isJacobiAt_system`, i.e. with `z = chartCovDeriv cov x₀ u w y`) and the
base curve's chart coordinates `u`, `w` are `C^∞`, then `y` is `C^∞` on every closed subinterval.
This is what turns the `C¹`-level `IsJacobiAt` data into the `C^∞` data required by the
second-variation theorems. -/
theorem contDiffOn_of_isJacobiSystem (htor : cov.torsion = 0)
    {x₀ : M} {u w y : ℝ → E} {A₀ B₀ a b : ℝ} (hab : a < b) (habt : Icc a b ⊆ Ioo A₀ B₀)
    (hstay : ∀ t ∈ Ioo A₀ B₀, u t ∈ (extChartAt I x₀).target)
    (hu : ContDiffOn ℝ ∞ u (Ioo A₀ B₀)) (hw : ContDiffOn ℝ ∞ w (Ioo A₀ B₀))
    (hy : ∀ t ∈ Ioo A₀ B₀, HasDerivAt y (deriv y t) t)
    (hzd : ∀ t ∈ Ioo A₀ B₀, HasDerivAt (chartCovDeriv cov x₀ u w y)
      (deriv (chartCovDeriv cov x₀ u w y) t) t)
    (hjac : ∀ t ∈ Ioo A₀ B₀, chartCovDeriv cov x₀ u w (chartCovDeriv cov x₀ u w y) t
      + chartCurv cov x₀ ((extChartAt I x₀).symm (u t)) (y t) (w t) = 0)
    (hyc : ContinuousOn y (Icc a b)) :
    ContDiffOn ℝ ∞ y (Icc a b) := by
  refine (Submission.Coeff.contDiffOn_of_jacobiSolution (cov := cov)
    (z := chartCovDeriv cov x₀ u w y) htor hab habt hstay hu hw ?_ ?_ hyc ?_).1
  · intro t ht
    have hs := hstay t (habt ht)
    have hsrc : (extChartAt I x₀).symm (u t) ∈ (chartAt H x₀).source :=
      mem_source_chartCurve (I := I) hs
    have hval : chartCovDeriv cov x₀ u w y t - gammaOp (cov := cov) x₀ u w t (y t) = deriv y t := by
      rw [chartCovDeriv_apply (cov := cov) hs, gammaOp_apply (cov := cov) hsrc]
      abel
    exact (hy t (habt ht)).congr_deriv hval.symm
  · intro t ht
    have hs := hstay t (habt ht)
    have hsrc : (extChartAt I x₀).symm (u t) ∈ (chartAt H x₀).source :=
      mem_source_chartCurve (I := I) hs
    have h1 : chartCovDeriv cov x₀ u w (chartCovDeriv cov x₀ u w y) t
        = deriv (chartCovDeriv cov x₀ u w y) t
          + gammaOp (cov := cov) x₀ u w t (chartCovDeriv cov x₀ u w y t) := by
      rw [chartCovDeriv_apply (cov := cov) hs, gammaOp_apply (cov := cov) hsrc]
    have h2 : chartCovDeriv cov x₀ u w (chartCovDeriv cov x₀ u w y) t
        = - curvOp (cov := cov) x₀ u w t (y t) := by
      have h := hjac t (habt ht)
      rw [← curvOp_apply (cov := cov) hsrc] at h
      exact eq_neg_of_add_eq_zero_left h
    rw [h2] at h1
    have h5 : deriv (chartCovDeriv cov x₀ u w y) t
        = -(curvOp (cov := cov) x₀ u w t (y t))
          - gammaOp (cov := cov) x₀ u w t (chartCovDeriv cov x₀ u w y t) :=
      (sub_eq_iff_eq_add.mpr h1).symm
    refine (hzd t (habt ht)).congr_deriv ?_
    rw [h5]
    abel
  · exact (isOpen_Ioo.continuousOn_iff.mpr (fun t ht => (hzd t ht).continuousAt)).mono habt

end

end Submission.JacobiAtSystem
