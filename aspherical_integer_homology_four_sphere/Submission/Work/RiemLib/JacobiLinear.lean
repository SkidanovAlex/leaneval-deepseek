import Submission.Work.RiemLib.VariationJacobi

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# The Jacobi system: existence with arbitrary initial data, and linearity

`Submission.JacobiTensor.exists_jacobiSystem` produces the Jacobi tensor with the *fixed* initial
data `(Y 0, U 0) = (0, 1)` at the *fixed* base time `0`.  The globalisation of the variation
argument along a geodesic ray (§83 of the roadmap) instantiates the chart Jacobi system in charts
taken at points *along* the ray, where the data live at the left edge of the chart interval and are
**arbitrary**.  This file supplies the two pieces that are needed for that:

* `exists_jacobiSystem_init` — existence of a solution of the Jacobi system with arbitrary initial
  data `(A, B)` at an arbitrary base time `t₀` (a direct generalisation of `exists_jacobiSystem`);
* `eqOn_fundamental_of_jacobiSystem` — **the two-fundamental-solutions spanning statement**: a
  solution `(y, z)` of the Jacobi system is the linear combination
  `y s = (Y₂ s) (y t₀) + (Y s) (z t₀)`, `z s = (U₂ s) (y t₀) + (U s) (z t₀)`
  of the two fundamental solutions — the one with data `(0, 1)` and the one with data `(1, 0)` —
  evaluated on the initial data.  The proof is linearity of the (linear!) system plus ODE
  uniqueness (`Commons.Analysis.ODE.eqOn_of_hasDerivAt_linearODE`); the bound `M` on the
  coefficient is an explicit hypothesis here, since supplying it along a chart geodesic is routine
  plumbing (`continuousOn_gammaOp`, `continuousOn_curvOp`) that the caller does once.
-/

set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

open LeanEval.Geometry.SphereTheorem
open scoped Manifold ContDiff Bundle Topology ENNReal NNReal
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter
open Submission.Geodesic
open Submission.ChartConnection
open Submission.ChartCurv
open Submission.JacobiTensor
open Submission.FlowJacobi

namespace Submission.JacobiLinear

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

/-- **The Jacobi system with arbitrary initial data.**  Along a chart geodesic `(u,w)` there is a
solution of the Jacobi system with prescribed data `(A, B)` at any base time `t₀` of the interval. -/
theorem exists_jacobiSystem_init (htor : cov.torsion = 0) {x₀ : M} {v : E} {u w : ℝ → E}
    (h : HasChartGeodesic cov x₀ v u w) {a b t₀ : ℝ} (hab : a < b)
    (habt : Icc a b ⊆ Ioo (-2 : ℝ) 2) (h0 : t₀ ∈ Icc a b) (A B : E →L[ℝ] E) :
    ∃ Y U : ℝ → E →L[ℝ] E, Y t₀ = A ∧ U t₀ = B ∧
      (∀ t ∈ Icc a b, HasDerivAt Y (U t - (gammaOp (cov := cov) x₀ u w t).comp (Y t)) t) ∧
      (∀ t ∈ Icc a b, HasDerivAt U (-((gammaOp (cov := cov) x₀ u w t).comp (U t))
        - (curvOp (cov := cov) x₀ u w t).comp (Y t)) t) := by
  have hc : ContinuousOn (jacobiSys (cov := cov) x₀ u w) (Icc a b) :=
    (continuousOn_jacobiSys (cov := cov) htor h).mono habt
  obtain ⟨Z, hZ0, hZode, -⟩ :=
    Commons.Analysis.ODE.exists_linearODE_solution_Icc
      (E := (E →L[ℝ] E) × (E →L[ℝ] E)) hab hc h0 (A, B)
  refine ⟨fun t => (Z t).1, fun t => (Z t).2, ?_, ?_, ?_, ?_⟩
  · simpa using congrArg Prod.fst hZ0
  · simpa using congrArg Prod.snd hZ0
  · intro t ht
    have h1 : HasDerivAt (fun s : ℝ => (Z s).1) ((jacobiSys (cov := cov) x₀ u w t (Z t)).1) t :=
      (hZode t ht).fst
    rw [jacobiSys_apply] at h1
    exact h1
  · intro t ht
    have h1 : HasDerivAt (fun s : ℝ => (Z s).2) ((jacobiSys (cov := cov) x₀ u w t (Z t)).2) t :=
      (hZode t ht).snd
    rw [jacobiSys_apply] at h1
    exact h1


variable {x₀ : M} {Φ : ℝ × ℝ → E × E}

/-- **The two fundamental solutions span.**  Let `(Y, U)` be the solution of the Jacobi system with
data `(0, 1)` at `t₀` and `(Y₂, U₂)` the one with data `(1, 0)`.  Then any solution `(y, z)` of the
same system is the linear combination of the two columns evaluated on its own initial data:
`y s = (Y₂ s) (y t₀) + (Y s) (z t₀)` and `z s = (U₂ s) (y t₀) + (U s) (z t₀)`. -/
theorem eqOn_fundamental_of_jacobiSystem (htor : cov.torsion = 0)
    {a b t₀ : ℝ} (hab : a < b) (h0 : t₀ ∈ Icc a b) {M : ℝ≥0}
    (hM : ∀ t ∈ Icc a b, ‖jacobiSysVec (cov := cov) x₀ (gc Φ) (gv Φ) t‖ ≤ M)
    {Y U Y₂ U₂ : ℝ → E →L[ℝ] E}
    (hY0 : Y t₀ = 0) (hU0 : U t₀ = 1) (hY₂0 : Y₂ t₀ = 1) (hU₂0 : U₂ t₀ = 0)
    (hYode : ∀ t ∈ Icc a b,
      HasDerivAt Y (U t - (gammaOp (cov := cov) x₀ (gc Φ) (gv Φ) t).comp (Y t)) t)
    (hUode : ∀ t ∈ Icc a b, HasDerivAt U
      (-((gammaOp (cov := cov) x₀ (gc Φ) (gv Φ) t).comp (U t))
        - (curvOp (cov := cov) x₀ (gc Φ) (gv Φ) t).comp (Y t)) t)
    (hY₂ode : ∀ t ∈ Icc a b,
      HasDerivAt Y₂ (U₂ t - (gammaOp (cov := cov) x₀ (gc Φ) (gv Φ) t).comp (Y₂ t)) t)
    (hU₂ode : ∀ t ∈ Icc a b, HasDerivAt U₂
      (-((gammaOp (cov := cov) x₀ (gc Φ) (gv Φ) t).comp (U₂ t))
        - (curvOp (cov := cov) x₀ (gc Φ) (gv Φ) t).comp (Y₂ t)) t)
    {y z : ℝ → E}
    (hyode : ∀ t ∈ Icc a b, HasDerivAt y
      (z t - gammaOp (cov := cov) x₀ (gc Φ) (gv Φ) t (y t)) t)
    (hzode : ∀ t ∈ Icc a b, HasDerivAt z
      (-gammaOp (cov := cov) x₀ (gc Φ) (gv Φ) t (z t)
        - curvOp (cov := cov) x₀ (gc Φ) (gv Φ) t (y t)) t) :
    (∀ s ∈ Icc a b, y s = (Y₂ s) (y t₀) + (Y s) (z t₀)) ∧
      (∀ s ∈ Icc a b, z s = (U₂ s) (y t₀) + (U s) (z t₀)) := by
  classical
  set A : ℝ → (E × E) →L[ℝ] (E × E) := jacobiSysVec (cov := cov) x₀ (gc Φ) (gv Φ) with hA
  set w : ℝ → E × E := fun s => ((Y₂ s) (y t₀) + (Y s) (z t₀),
    (U₂ s) (y t₀) + (U s) (z t₀)) with hw
  have hwode : ∀ t ∈ Icc a b, HasDerivAt w (A t (w t)) t := by
    intro t ht
    have h1 : HasDerivAt (fun s : ℝ => (Y₂ s) (y t₀))
        ((U₂ t - (gammaOp (cov := cov) x₀ (gc Φ) (gv Φ) t).comp (Y₂ t)) (y t₀)) t := by
      simpa using (hY₂ode t ht).clm_apply (hasDerivAt_const t (y t₀))
    have h2 : HasDerivAt (fun s : ℝ => (Y s) (z t₀))
        ((U t - (gammaOp (cov := cov) x₀ (gc Φ) (gv Φ) t).comp (Y t)) (z t₀)) t := by
      simpa using (hYode t ht).clm_apply (hasDerivAt_const t (z t₀))
    have h3 : HasDerivAt (fun s : ℝ => (U₂ s) (y t₀))
        ((-((gammaOp (cov := cov) x₀ (gc Φ) (gv Φ) t).comp (U₂ t))
          - (curvOp (cov := cov) x₀ (gc Φ) (gv Φ) t).comp (Y₂ t)) (y t₀)) t := by
      simpa using (hU₂ode t ht).clm_apply (hasDerivAt_const t (y t₀))
    have h4 : HasDerivAt (fun s : ℝ => (U s) (z t₀))
        ((-((gammaOp (cov := cov) x₀ (gc Φ) (gv Φ) t).comp (U t))
          - (curvOp (cov := cov) x₀ (gc Φ) (gv Φ) t).comp (Y t)) (z t₀)) t := by
      simpa using (hUode t ht).clm_apply (hasDerivAt_const t (z t₀))
    have hfst : HasDerivAt (fun s : ℝ => (Y₂ s) (y t₀) + (Y s) (z t₀))
        (((U₂ t - (gammaOp (cov := cov) x₀ (gc Φ) (gv Φ) t).comp (Y₂ t)) (y t₀))
          + ((U t - (gammaOp (cov := cov) x₀ (gc Φ) (gv Φ) t).comp (Y t)) (z t₀))) t :=
      h1.add h2
    have hsnd : HasDerivAt (fun s : ℝ => (U₂ s) (y t₀) + (U s) (z t₀))
        (((-((gammaOp (cov := cov) x₀ (gc Φ) (gv Φ) t).comp (U₂ t))
            - (curvOp (cov := cov) x₀ (gc Φ) (gv Φ) t).comp (Y₂ t)) (y t₀))
          + ((-((gammaOp (cov := cov) x₀ (gc Φ) (gv Φ) t).comp (U t))
            - (curvOp (cov := cov) x₀ (gc Φ) (gv Φ) t).comp (Y t)) (z t₀))) t :=
      h3.add h4
    have hbase := hfst.prodMk hsnd
    refine hbase.congr_deriv ?_
    simp only [hw, hA, jacobiSysVec_apply]
    refine Prod.ext ?_ ?_
    · simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.comp_apply, map_add]
      abel
    · simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.comp_apply,
        ContinuousLinearMap.neg_apply, map_add]
      abel
  have hw0 : w t₀ = (y t₀, z t₀) := by
    refine Prod.ext ?_ ?_
    · simp only [hw]
      rw [hY₂0, hY0, ContinuousLinearMap.one_apply, ContinuousLinearMap.zero_apply, add_zero]
    · simp only [hw]
      rw [hU₂0, hU0, ContinuousLinearMap.zero_apply, ContinuousLinearMap.one_apply, zero_add]
  have hpair : ∀ t ∈ Icc a b, HasDerivAt (fun s : ℝ => (y s, z s)) (A t (y t, z t)) t := by
    intro t ht
    have hbase := (hyode t ht).prodMk (hzode t ht)
    refine hbase.congr_deriv ?_
    simp only [hA, jacobiSysVec_apply]
  have huniq := Commons.Analysis.ODE.eqOn_of_hasDerivAt_linearODE (A := A) (M := M) hM h0
    (y := fun s => (y s, z s)) (z := w) hpair hwode hw0.symm
  constructor
  · intro s hs
    exact (Prod.ext_iff.mp (huniq hs)).1
  · intro s hs
    exact (Prod.ext_iff.mp (huniq hs)).2

end

end Submission.JacobiLinear
