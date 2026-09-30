import Submission.Work.RiemLib.RauchGlobal

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# The space of Jacobi fields: linearity

A Jacobi field along a geodesic is determined by the chart Jacobi equation
`D(Dy) + R(y,w)w = 0`, which is *linear* in `y`.  This file records the linearity of the
coordinate curvature term `chartCurv` in its first argument and deduces that scalar multiples of a
Jacobi field (in the germ-level sense `Submission.RauchGlobal.IsJacobiAt`) are again Jacobi fields.

## Contents

* `dB_smul_fst`, `dB_smul_last`, `chartCurv_smul_fst`: linearity in the first (vector) argument;
* `isJacobiAt_const_smul`: `IsJacobiAt` is closed under scalar multiplication.
-/

set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false

open LeanEval.Geometry.SphereTheorem
open scoped Manifold ContDiff Bundle Topology
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter
open Submission.Geodesic
open Submission.ChartConnection
open Submission.Jacobi
open Submission.ChartCurv
open Submission.Curvature
open Submission.CurvatureVec
open Submission.Rauch
open Submission.RauchGlobal

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M]
    [IsManifold I ∞ M]
  [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun (x : M) ↦ TangentSpace I x)]

namespace Submission.JacobiVec

noncomputable section

variable [I.Boundaryless]
variable {cov : CovariantDerivative I E (TangentSpace I (M := M))}

/-- `dB` is linear in its first (direction) argument. -/
lemma dB_smul_fst (x₀ p : M) (c : ℝ) (v a b : E) :
    dB cov x₀ p (c • v) a b = c • dB cov x₀ p v a b := by
  rw [dB, dB, frameVector_smul]
  exact map_smul _ c _

/-- `dB` is linear in its last (vector) argument. -/
lemma dB_smul_last [ContMDiffCovariantDerivative cov ∞] (x₀ p : M)
    (hp : p ∈ (chartAt H x₀).source) (v a : E) (c : ℝ) (b : E) :
    dB cov x₀ p v a (c • b) = c • dB cov x₀ p v a b := by
  rw [dB, dB,
    mvfderiv_chrB_apply (cov := cov) x₀ p a (c • b) v hp,
    mvfderiv_chrB_apply (cov := cov) x₀ p a b v hp]
  simp only [Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  have hcoord : (Module.finBasis ℝ E).coord j (c • b) = c * (Module.finBasis ℝ E).coord j b := by
    rw [map_smul, smul_eq_mul]
  rw [hcoord, smul_smul]
  congr 1
  ring

/-- The coordinate curvature term is linear in its first argument. -/
theorem chartCurv_smul_fst [ContMDiffCovariantDerivative cov ∞]
    (x₀ p : M) (hp : p ∈ (chartAt H x₀).source) (c : ℝ) (X Y : E) :
    chartCurv cov x₀ p (c • X) Y = c • chartCurv cov x₀ p X Y := by
  rw [chartCurv, chartCurv]
  rw [dB_smul_fst, dB_smul_last _ _ hp,
      chrB_smul_snd (x₀ := x₀) (p := p) (c := c) (a := chrB cov x₀ p Y Y) (b := X),
      chrB_smul_snd (x₀ := x₀) (p := p) (c := c) (a := Y) (b := X),
      chrB_smul_fst (x₀ := x₀) (p := p) (c := c) (a := chrB cov x₀ p Y X) (b := Y) hp]
  simp only [smul_add, smul_sub]

/-- `dB` is additive in its first (direction) argument. -/
lemma dB_add_fst (x₀ p : M) (v a b b' : E) :
    dB cov x₀ p (v + a) b b' = dB cov x₀ p v b b' + dB cov x₀ p a b b' := by
  rw [dB, dB, dB, frameVector_add, map_add]

/-- `dB` is additive in its last (vector) argument. -/
lemma dB_add_last [ContMDiffCovariantDerivative cov ∞] (x₀ p : M)
    (hp : p ∈ (chartAt H x₀).source) (v a b b' : E) :
    dB cov x₀ p v a (b + b') = dB cov x₀ p v a b + dB cov x₀ p v a b' := by
  rw [dB, dB, dB,
    mvfderiv_chrB_apply (cov := cov) x₀ p a (b + b') v hp,
    mvfderiv_chrB_apply (cov := cov) x₀ p a b v hp,
    mvfderiv_chrB_apply (cov := cov) x₀ p a b' v hp]
  simp only [map_add, mul_add, add_smul, Finset.sum_add_distrib]

/-- The coordinate curvature term is additive in its first argument. -/
theorem chartCurv_add_fst [ContMDiffCovariantDerivative cov ∞]
    (x₀ p : M) (hp : p ∈ (chartAt H x₀).source) (X Z Y : E) :
    chartCurv cov x₀ p (X + Z) Y = chartCurv cov x₀ p X Y + chartCurv cov x₀ p Z Y := by
  simp only [chartCurv, dB_add_fst, dB_add_last _ _ hp,
    chrB_add_fst _ _ _ _ _ hp, chrB_add_snd]
  abel

end

end Submission.JacobiVec
