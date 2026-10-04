import Mathlib
import Submission.Work.Diff.EXT.LocalExtDefs
import Submission.Work.Diff.GE.curvbasic
import Submission.Work.Diff.GE.chartcalc
import Submission.Work.Diff.GE.norms_defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Field-level iterated covariant derivatives for the continuation/Shi step (`EXT`)

This module provides the *field-level* formulation of the covariant derivatives of the
**connection difference** `A(t) := ∇^{G(t)} - ∇^{G(0)}` and of the **metric** `G(t)`, taken with
respect to the *fixed* background connection `∇^{G(0)}`.

The point of these definitions is that the coordinate (chart) derivatives of the metric are
controlled by the *covariant* derivatives of `G(t)` with respect to the fixed initial connection,
and that the latter are in turn controlled by the covariant derivatives of `A(t)`; the connection
difference vanishes at `t = 0`, which is what makes the a priori estimates on `[T/2,T)` possible
without any analysis of the (gauge) part of the second derivatives of the metric.

Everything is stated as a `Classical.epsilon`-free recursive formula on `M`, evaluated at points
through the smooth extensions `smoothExt x ·` (as in `covKRmExt`), so that no bundle theory is
needed: `covKAExt G t k v A B C x` is the `k`-th covariant derivative (with respect to `∇^{G(0)}`)
of the lowered connection difference `A`, evaluated on the `k` directions `v i` and on the three
arguments `A x`, `B x`, `C x`; `covKGExt G t k v A B x` is the same for the metric `G t`.
-/

set_option linter.unusedSectionVars false

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology
open Bundle ContDiff Set VectorField CovariantDerivative Metric

namespace Work.Diff.EXT

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]

/-- The *lowered connection difference* of the flow `G` at time `t` with respect to the initial
metric `G 0`: a (0,3)-tensor field level object. -/
noncomputable def aOf (G : ℝ → SMet I M) (t : ℝ)
    (A B C : Π y : M, TangentSpace I y) (y : M) : ℝ :=
  (G t).inner y (((lcOf (G t)) B y (A y)) - ((lcOf (G 0)) B y (A y))) (C y)

/-- **Iterated covariant derivatives of the connection difference** with respect to the fixed
connection `∇^{G(0)}`, evaluated on `k` direction fields and three argument fields. -/
noncomputable def covKAExt (G : ℝ → SMet I M) (t : ℝ) :
    ∀ k : ℕ, (Fin k → (Π y : M, TangentSpace I y)) →
      (Π y : M, TangentSpace I y) → (Π y : M, TangentSpace I y) →
      (Π y : M, TangentSpace I y) → M → ℝ
  | 0, _, A, B, C => aOf G t A B C
  | k + 1, v, A, B, C => fun x =>
      mvfderiv I (covKAExt G t k (fun i : Fin k => v i.succ) A B C) x (v 0 x)
        - ∑ i : Fin k, covKAExt G t k
            (Function.update (fun j : Fin k => v j.succ) i
              (fun y => (lcOf (G 0)) (v i.succ) y (v 0 y))) A B C x
        - covKAExt G t k (fun i : Fin k => v i.succ)
            (fun y => (lcOf (G 0)) A y (v 0 y)) B C x
        - covKAExt G t k (fun i : Fin k => v i.succ) A
            (fun y => (lcOf (G 0)) B y (v 0 y)) C x
        - covKAExt G t k (fun i : Fin k => v i.succ) A B
            (fun y => (lcOf (G 0)) C y (v 0 y)) x

/-- **Iterated covariant derivatives of the metric** `G t` with respect to the fixed connection
`∇^{G(0)}`, evaluated on `k` direction fields and two argument fields. -/
noncomputable def covKGExt (G : ℝ → SMet I M) (t : ℝ) :
    ∀ k : ℕ, (Fin k → (Π y : M, TangentSpace I y)) →
      (Π y : M, TangentSpace I y) → (Π y : M, TangentSpace I y) → M → ℝ
  | 0, _, A, B => fun y => (G t).inner y (A y) (B y)
  | k + 1, v, A, B => fun x =>
      mvfderiv I (covKGExt G t k (fun i : Fin k => v i.succ) A B) x (v 0 x)
        - ∑ i : Fin k, covKGExt G t k
            (Function.update (fun j : Fin k => v j.succ) i
              (fun y => (lcOf (G 0)) (v i.succ) y (v 0 y))) A B x
        - covKGExt G t k (fun i : Fin k => v i.succ)
            (fun y => (lcOf (G 0)) A y (v 0 y)) B x
        - covKGExt G t k (fun i : Fin k => v i.succ) A
            (fun y => (lcOf (G 0)) B y (v 0 y)) x

/-! ## Chart form of the same objects

The chart at `x₀` reads the lowered connection difference as an array `aComp` (a function of the
chart coordinate), and the background covariant derivatives `∇^{G(0),k}` of that array are again
computed by an explicit recursion with the *background* Christoffel symbols `cGam (G 0)`.
These are the quantities whose uniform boundedness on `[T/2,T)` gives the chart bounds of the
metric (the fixed background frame has bounded `C^k` data). -/

/-- The point of the manifold with chart coordinate `y` in the chart at `x₀`. -/
noncomputable def pt (x₀ : M) (y : E) : M := (extChartAt I x₀).symm y

/-- **The chart components of the lowered connection difference** `g_t(∇^{g_t} - ∇^{g_0})` in the
coordinate frame of the chart at `x₀`. -/
noncomputable def aComp (G : ℝ → SMet I M) (x₀ : M) (t : ℝ) (y : E)
    (i j k : Fin (Module.finrank ℝ E)) : ℝ :=
  ∑ l : Fin (Module.finrank ℝ E),
    Work.Diff.GE.GramM G x₀ t (pt (I := I) x₀ y) k l
      * (Work.Diff.GE.cGam (G t) x₀ (pt (I := I) x₀ y) l i j
         - Work.Diff.GE.cGam (G 0) x₀ (pt (I := I) x₀ y) l i j)

/-- **The chart form of the iterated background covariant derivatives of the connection
difference**: the recursion with the background Christoffel symbols `cGam (G 0)` applied to the
array `aComp`.  The `k` derivative directions are given by `v : Fin k → Fin n` (chart directions). -/
noncomputable def aCovArr (G : ℝ → SMet I M) (x₀ : M) (t : ℝ) :
    ∀ k : ℕ, (Fin k → Fin (Module.finrank ℝ E)) →
      Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → (E → ℝ)
  | 0, _, i, j, k => fun y => aComp G x₀ t y i j k
  | m + 1, v, i, j, k => fun y =>
      fderiv ℝ (aCovArr G x₀ t m (fun s : Fin m => v s.succ) i j k) y
          (Work.Diff.GE.cBasis (E := E) (v 0))
        - ∑ r : Fin m, ∑ p : Fin (Module.finrank ℝ E),
            (Work.Diff.GE.cGam (G 0) x₀ (pt (I := I) x₀ y) p (v r.succ) (v 0))
              * (aCovArr G x₀ t m
                  (Function.update (fun s : Fin m => v s.succ) r p) i j k) y
        - ∑ p : Fin (Module.finrank ℝ E),
            (Work.Diff.GE.cGam (G 0) x₀ (pt (I := I) x₀ y) p i (v 0))
              * (aCovArr G x₀ t m (fun s : Fin m => v s.succ) p j k) y
        - ∑ p : Fin (Module.finrank ℝ E),
            (Work.Diff.GE.cGam (G 0) x₀ (pt (I := I) x₀ y) p j (v 0))
              * (aCovArr G x₀ t m (fun s : Fin m => v s.succ) i p k) y
        - ∑ p : Fin (Module.finrank ℝ E),
            (Work.Diff.GE.cGam (G 0) x₀ (pt (I := I) x₀ y) p k (v 0))
              * (aCovArr G x₀ t m (fun s : Fin m => v s.succ) i j p) y

end Work.Diff.EXT
