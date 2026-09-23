import Submission.ChartGeoAt

/-!
# The Jacobi system with prescribed initial data at a prescribed base time

`Submission.ChartGeoAt.exists_jacobiSystemOn` produces the Jacobi *tensor* along a chart geodesic,
normalised by `Y 0 = 0`, `U 0 = 1` at the *global* time `0` — so it applies only to the pieces of a
chart cover that contain `0`.  This file removes that restriction: for any base time `t₀ ∈ Icc a b`
and any initial data `(Y₀, U₀)` there is a solution of the Jacobi system

`Y' = U - Γ̂ ∘ Y`,   `U' = -Γ̂ ∘ U - R̂ ∘ Y`

on `Icc a b` with `Y t₀ = Y₀`, `U t₀ = U₀`.  This is what makes it possible to **patch** Jacobi data
across the pieces of a chart cover of a geodesic: the initial data of each piece are the chart
coordinates (obtained through
`(trivializationAt E (TangentSpace I) x).continuousLinearMapAt ℝ (γ t₀)`) of the values produced on
the previous piece.  See `Submission/Roadmap.lean` §97.3.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 1000000

open LeanEval.Geometry.SphereTheorem
open scoped Manifold ContDiff Bundle Topology ENNReal InnerProductSpace
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter
open Submission.Geodesic
open Submission.ChartConnection
open Submission.ChartCurv
open Submission.Curvature
open Submission.Rauch
open Submission.JacobiTensor
open Submission.RauchGen
open Submission.JacobiGen
open Submission.FlowJacobi
open Submission.Minimal
open Submission.GlobalExp
open Commons.Analysis.ODE

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M]
    [IsManifold I ∞ M]
  [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun (x : M) ↦ TangentSpace I x)]

namespace Submission.JacobiSystemInit

noncomputable section

variable [I.Boundaryless]
variable {cov : CovariantDerivative I E (TangentSpace I (M := M))}
variable [ContMDiffCovariantDerivative cov ∞]

/-- **Existence of the Jacobi system with prescribed initial data at a prescribed base time.**  On
`Icc a b ⊆ Ioo A B`, for any base time `t₀ ∈ Icc a b` and any initial data `(Y₀, U₀)`, there are
`Y, U : ℝ → E →L[ℝ] E` with `Y t₀ = Y₀`, `U t₀ = U₀` and
`Y' = U - Γ̂ ∘ Y`,  `U' = -Γ̂ ∘ U - R̂ ∘ Y`.

This is `Submission.ChartGeoAt.exists_jacobiSystemOn` with the initial data moved from `(0,1)` at
time `0` to `(Y₀,U₀)` at time `t₀`; it is what makes it possible to *patch* Jacobi data across the
pieces of a chart cover of a geodesic (each piece carries the initial data transported from the
previous one). -/
theorem exists_jacobiSystemOn_init (htor : cov.torsion = 0)
    {x₀ q : M} {v : E} {u w : ℝ → E} {A B : ℝ}
    (h : HasChartGeodesicOn cov x₀ q v u w A B)
    {a b t₀ : ℝ} (hab : a < b) (habt : Icc a b ⊆ Ioo A B) (ht₀ : t₀ ∈ Icc a b)
    (Y₀ U₀ : E →L[ℝ] E) :
    ∃ Y U : ℝ → E →L[ℝ] E, Y t₀ = Y₀ ∧ U t₀ = U₀ ∧
      (∀ t ∈ Icc a b, HasDerivAt Y (U t - (gammaOp (cov := cov) x₀ u w t).comp (Y t)) t) ∧
      (∀ t ∈ Icc a b, HasDerivAt U (-((gammaOp (cov := cov) x₀ u w t).comp (U t))
        - (curvOp (cov := cov) x₀ u w t).comp (Y t)) t) := by
  have hc : ContinuousOn (jacobiSys (cov := cov) x₀ u w) (Icc a b) := by
    have hG : ContinuousOn (fun t : ℝ => gammaOp (cov := cov) x₀ u w t) (Icc a b) :=
      (Submission.JacobiGen.continuousOn_christoffelLM_along_Ioo (cov := cov) htor
        h.2.2.1 h.2.2.2.1 h.2.2.2.2).mono (fun _ hx => habt hx)
    have hw : ContinuousOn w (Icc a b) :=
      HasDerivAt.continuousOn fun t ht => h.2.2.2.2 t (habt ht)
    have hR : ContinuousOn (fun t : ℝ => curvOp (cov := cov) x₀ u w t) (Icc a b) :=
      (Submission.JacobiTensor.continuousOn_curvOp (cov := cov)
        (HasDerivAt.continuousOn fun t ht => h.2.2.2.1 t (habt ht)) hw
        (fun t ht => h.2.2.1 t (habt ht)))
    have hcomp := (continuous_jacobiSysAux (E := E)).comp_continuousOn (hG.prodMk hR)
    refine hcomp.congr fun t _ => ?_
    rfl
  obtain ⟨Z, hZ0, hZode, -⟩ :=
    Commons.Analysis.ODE.exists_linearODE_solution_Icc
      (E := (E →L[ℝ] E) × (E →L[ℝ] E)) hab hc ht₀ (Y₀, U₀)
  refine ⟨fun t => (Z t).1, fun t => (Z t).2, ?_, ?_, ?_, ?_⟩
  · simpa using congrArg Prod.fst hZ0
  · simpa using congrArg Prod.snd hZ0
  · intro t ht
    have h1 : HasDerivAt (fun s : ℝ => (Z s).1)
        ((jacobiSys (cov := cov) x₀ u w t (Z t)).1) t := (hZode t ht).fst
    rw [jacobiSys_apply] at h1
    exact h1
  · intro t ht
    have h1 : HasDerivAt (fun s : ℝ => (Z s).2)
        ((jacobiSys (cov := cov) x₀ u w t (Z t)).2) t := (hZode t ht).snd
    rw [jacobiSys_apply] at h1
    exact h1

end

end Submission.JacobiSystemInit
