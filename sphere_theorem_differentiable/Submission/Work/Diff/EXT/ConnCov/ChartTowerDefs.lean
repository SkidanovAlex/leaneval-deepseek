import Mathlib
import Submission.Work.Diff.EXT.ChartCoreDefs
import Submission.Work.Diff.GE.covRmChartExpr_eq

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The chart recursions for the moving curvature tower and for the `(0,3)`-towers of the
connection difference

This module (definitions only, sorry-free) provides the two chart recursions used by
`Work.Diff.EXT.ConnCov.dAOfTower_chart_bound`:

* `Work.Diff.EXT.ConnCov.rmChartTower` — the *chart recursion for the iterated moving covariant
  derivatives of the curvature*: level `0` is the chart curvature array `rmChartExpr`, and each
  level is the chart derivative of the previous one in the direction `v 0`, corrected by the four
  Christoffel contractions of the coordinate frame (`chrCoord`).  For `m = 1` this is exactly
  the proved `Work.Diff.GE.covRmChartExpr` (which by `Work.Diff.GE.covRmChartExpr_eq` agrees with
  the geometric `∇Rm` components `covRmC5`); the general level is the same object with
  `∇^{G t, m}Rm` in place of `∇Rm`.

* `Work.Diff.EXT.ConnCov.tower3Arr` — the chart recursion for a `(0,3)`-array *with arbitrary
  base* `A`, with respect to the *fixed* background connection `∇^{G 0}`: level `0` is `A` and each
  level is again the chart derivative of the previous level, corrected by `cGam (G 0)` in the
  direction slot and in the three tensor slots.  `tower3Arr` is linear in the base `A`; this is
  what makes it possible to differentiate the chart recursion in time (the coefficients
  `cGam (G 0)` do not depend on the time parameter), see
  `Work.Diff.EXT.ConnCov.aCovArr_eq_tower3Arr` and the companion file.

* `aCompArr G x₀ t` is the base array of the chart recursion of the connection difference
  (`Work.Diff.EXT.aComp`), and `reactArr G x₀ t` is its time derivative — the base array of the
  reaction tower which is the object bounded by `dAOfTower_chart_bound`.
-/

set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle ContDiff Set VectorField CovariantDerivative Metric

namespace Work.Diff.EXT.ConnCov

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]

/-- **The chart recursion for the moving tower of the curvature.**  `rmChartTower G x₀ t m v i j k l`
is a function of the chart coordinate; at level `0` it is the chart curvature array
`rmChartExpr`, and at level `m + 1` it is the chart derivative in the direction `v 0` of the
level-`m` array minus the five Christoffel contractions of the coordinate frame (`chrCoord`),
exactly as the proved `Work.Diff.GE.covRmChartExpr` does at level `1`. -/
noncomputable def rmChartTower (G : ℝ → Submission.Diff.SMet I M) (x₀ : M) (t : ℝ) :
    ∀ m : ℕ, (Fin m → Fin (Module.finrank ℝ E)) →
      Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) →
      Fin (Module.finrank ℝ E) → (E → ℝ)
  | 0, _, i, j, k, l => fun y =>
      Work.Diff.GE.rmChartExpr (I := I) G x₀ i j k l t (Work.Diff.EXT.pt (I := I) x₀ y)
  | m + 1, v, i, j, k, l => fun y =>
      fderiv ℝ (rmChartTower G x₀ t m (fun s : Fin m => v s.succ) i j k l) y
          (Work.Diff.GE.cBasis (E := E) (v 0))
        - ∑ r : Fin m, ∑ p : Fin (Module.finrank ℝ E),
            Work.Diff.GE.chrCoord (I := I) G x₀ p (v 0) (v r.succ) t
                (Work.Diff.EXT.pt (I := I) x₀ y)
              * rmChartTower G x₀ t m (Function.update (fun s : Fin m => v s.succ) r p)
                  i j k l y
        - ∑ p : Fin (Module.finrank ℝ E),
            Work.Diff.GE.chrCoord (I := I) G x₀ p (v 0) i t (Work.Diff.EXT.pt (I := I) x₀ y)
              * rmChartTower G x₀ t m (fun s : Fin m => v s.succ) p j k l y
        - ∑ p : Fin (Module.finrank ℝ E),
            Work.Diff.GE.chrCoord (I := I) G x₀ p (v 0) j t (Work.Diff.EXT.pt (I := I) x₀ y)
              * rmChartTower G x₀ t m (fun s : Fin m => v s.succ) i p k l y
        - ∑ p : Fin (Module.finrank ℝ E),
            Work.Diff.GE.chrCoord (I := I) G x₀ p (v 0) k t (Work.Diff.EXT.pt (I := I) x₀ y)
              * rmChartTower G x₀ t m (fun s : Fin m => v s.succ) i j p l y
        - ∑ p : Fin (Module.finrank ℝ E),
            Work.Diff.GE.chrCoord (I := I) G x₀ p (v 0) l t (Work.Diff.EXT.pt (I := I) x₀ y)
              * rmChartTower G x₀ t m (fun s : Fin m => v s.succ) i j k p y

/-- Unfolding of the chart recursion at level `0`. -/
@[simp] theorem rmChartTower_zero (G : ℝ → Submission.Diff.SMet I M) (x₀ : M) (t : ℝ)
    (v : Fin 0 → Fin (Module.finrank ℝ E)) (i j k l : Fin (Module.finrank ℝ E)) :
    rmChartTower (I := I) (M := M) G x₀ t 0 v i j k l
      = fun y => Work.Diff.GE.rmChartExpr (I := I) G x₀ i j k l t (Work.Diff.EXT.pt (I := I) x₀ y) :=
  rfl

/-- Unfolding of the chart recursion at level `m + 1`. -/
theorem rmChartTower_succ (G : ℝ → Submission.Diff.SMet I M) (x₀ : M) (t : ℝ) (m : ℕ)
    (v : Fin (m + 1) → Fin (Module.finrank ℝ E)) (i j k l : Fin (Module.finrank ℝ E)) :
    rmChartTower (I := I) (M := M) G x₀ t (m + 1) v i j k l
      = fun y =>
          fderiv ℝ (rmChartTower G x₀ t m (fun s : Fin m => v s.succ) i j k l) y
              (Work.Diff.GE.cBasis (E := E) (v 0))
            - ∑ r : Fin m, ∑ p : Fin (Module.finrank ℝ E),
                Work.Diff.GE.chrCoord (I := I) G x₀ p (v 0) (v r.succ) t
                    (Work.Diff.EXT.pt (I := I) x₀ y)
                  * rmChartTower G x₀ t m (Function.update (fun s : Fin m => v s.succ) r p)
                      i j k l y
            - ∑ p : Fin (Module.finrank ℝ E),
                Work.Diff.GE.chrCoord (I := I) G x₀ p (v 0) i t (Work.Diff.EXT.pt (I := I) x₀ y)
                  * rmChartTower G x₀ t m (fun s : Fin m => v s.succ) p j k l y
            - ∑ p : Fin (Module.finrank ℝ E),
                Work.Diff.GE.chrCoord (I := I) G x₀ p (v 0) j t (Work.Diff.EXT.pt (I := I) x₀ y)
                  * rmChartTower G x₀ t m (fun s : Fin m => v s.succ) i p k l y
            - ∑ p : Fin (Module.finrank ℝ E),
                Work.Diff.GE.chrCoord (I := I) G x₀ p (v 0) k t (Work.Diff.EXT.pt (I := I) x₀ y)
                  * rmChartTower G x₀ t m (fun s : Fin m => v s.succ) i j p l y
            - ∑ p : Fin (Module.finrank ℝ E),
                Work.Diff.GE.chrCoord (I := I) G x₀ p (v 0) l t (Work.Diff.EXT.pt (I := I) x₀ y)
                  * rmChartTower G x₀ t m (fun s : Fin m => v s.succ) i j k p y :=
  rfl

/-- **The chart recursion for a `(0,3)`-array with the fixed background connection.**  The base
`A : E → Fin n → Fin n → Fin n → ℝ` is an arbitrary chart array; each recursion step is the chart
derivative of the previous level in the direction `v 0` minus the four `cGam (G 0)`-contractions.
`tower3Arr G x₀ t A m v i j l` is *linear* in `A`. -/
noncomputable def tower3Arr (G : ℝ → Submission.Diff.SMet I M) (x₀ : M) (t : ℝ)
    (A : E → Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ) :
    ∀ m : ℕ, (Fin m → Fin (Module.finrank ℝ E)) →
      Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → (E → ℝ)
  | 0, _, i, j, l => fun y => A y i j l
  | m + 1, v, i, j, l => fun y =>
      fderiv ℝ (tower3Arr G x₀ t A m (fun s : Fin m => v s.succ) i j l) y
          (Work.Diff.GE.cBasis (E := E) (v 0))
        - ∑ r : Fin m, ∑ p : Fin (Module.finrank ℝ E),
            Work.Diff.GE.cGam (G 0) x₀ (Work.Diff.EXT.pt (I := I) x₀ y) p (v r.succ) (v 0)
              * tower3Arr G x₀ t A m (Function.update (fun s : Fin m => v s.succ) r p) i j l y
        - ∑ p : Fin (Module.finrank ℝ E),
            Work.Diff.GE.cGam (G 0) x₀ (Work.Diff.EXT.pt (I := I) x₀ y) p i (v 0)
              * tower3Arr G x₀ t A m (fun s : Fin m => v s.succ) p j l y
        - ∑ p : Fin (Module.finrank ℝ E),
            Work.Diff.GE.cGam (G 0) x₀ (Work.Diff.EXT.pt (I := I) x₀ y) p j (v 0)
              * tower3Arr G x₀ t A m (fun s : Fin m => v s.succ) i p l y
        - ∑ p : Fin (Module.finrank ℝ E),
            Work.Diff.GE.cGam (G 0) x₀ (Work.Diff.EXT.pt (I := I) x₀ y) p l (v 0)
              * tower3Arr G x₀ t A m (fun s : Fin m => v s.succ) i j p y

/-- Unfolding of `tower3Arr` at level `0`. -/
@[simp] theorem tower3Arr_zero (G : ℝ → Submission.Diff.SMet I M) (x₀ : M) (t : ℝ)
    (A : E → Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ)
    (v : Fin 0 → Fin (Module.finrank ℝ E)) (i j l : Fin (Module.finrank ℝ E)) :
    tower3Arr (I := I) (M := M) G x₀ t A 0 v i j l = fun y => A y i j l :=
  rfl

/-- Unfolding of `tower3Arr` at level `m + 1`. -/
theorem tower3Arr_succ (G : ℝ → Submission.Diff.SMet I M) (x₀ : M) (t : ℝ)
    (A : E → Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ)
    (m : ℕ) (v : Fin (m + 1) → Fin (Module.finrank ℝ E))
    (i j l : Fin (Module.finrank ℝ E)) :
    tower3Arr (I := I) (M := M) G x₀ t A (m + 1) v i j l
      = fun y =>
          fderiv ℝ (tower3Arr G x₀ t A m (fun s : Fin m => v s.succ) i j l) y
              (Work.Diff.GE.cBasis (E := E) (v 0))
            - ∑ r : Fin m, ∑ p : Fin (Module.finrank ℝ E),
                Work.Diff.GE.cGam (G 0) x₀ (Work.Diff.EXT.pt (I := I) x₀ y) p (v r.succ) (v 0)
                  * tower3Arr G x₀ t A m (Function.update (fun s : Fin m => v s.succ) r p)
                      i j l y
            - ∑ p : Fin (Module.finrank ℝ E),
                Work.Diff.GE.cGam (G 0) x₀ (Work.Diff.EXT.pt (I := I) x₀ y) p i (v 0)
                  * tower3Arr G x₀ t A m (fun s : Fin m => v s.succ) p j l y
            - ∑ p : Fin (Module.finrank ℝ E),
                Work.Diff.GE.cGam (G 0) x₀ (Work.Diff.EXT.pt (I := I) x₀ y) p j (v 0)
                  * tower3Arr G x₀ t A m (fun s : Fin m => v s.succ) i p l y
            - ∑ p : Fin (Module.finrank ℝ E),
                Work.Diff.GE.cGam (G 0) x₀ (Work.Diff.EXT.pt (I := I) x₀ y) p l (v 0)
                  * tower3Arr G x₀ t A m (fun s : Fin m => v s.succ) i j p y :=
  rfl

/-- The base array of the chart recursion for the connection difference. -/
noncomputable def aCompArr (G : ℝ → Submission.Diff.SMet I M) (x₀ : M) (t : ℝ) :
    E → Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ :=
  fun y i j l => Work.Diff.EXT.aComp (I := I) (M := M) G x₀ t y i j l

/-- **The base array of the reaction tower**: the time derivative of the chart array of the
connection difference.  Its `∇^{G 0}`-chart tower is (by Clairaut in time and the bridge
`aCovArr_eq_covKAExt`) exactly the left-hand side of `dAOfTower_chart_bound`. -/
noncomputable def reactArr (G : ℝ → Submission.Diff.SMet I M) (x₀ : M) (t : ℝ) :
    E → Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ :=
  fun y i j l => deriv (fun s : ℝ => Work.Diff.EXT.aComp (I := I) (M := M) G x₀ s y i j l) t

end Work.Diff.EXT.ConnCov
