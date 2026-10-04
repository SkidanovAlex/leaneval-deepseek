import Mathlib
import Submission.Work.Diff.EXT.ChartCoreDefs
import Submission.Work.Diff.EXT.Tower.Defs
import Submission.Work.Diff.GE.curvbasic

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The tower of covariant derivatives of the connection difference (`A`), with a connection parameter

`Work.Diff.EXT.covKAExt G t k` (frozen, in `Submission.Work.Diff.EXT.ChartCoreDefs`) is the `k`-th
covariant derivative, with respect to the *fixed* background connection `∇^{G 0} = lcOf (G 0)`, of
the lowered connection difference `aOf G t = g_t(∇^{g_t} − ∇^{g_0})`, evaluated on `k` direction
fields and three argument fields.

This module isolates the recursion from the frozen definition, exactly as
`Submission.Work.Diff.EXT.Tower.Defs` does for the curvature: it provides

* `Op3 k` — a field-level operator with `k` derivative slots and three value slots;
* `step cov τ` — the recursion step: the covariant derivative of `τ` with connection `cov`;
* `tower cov base k` — the `k`-th iterated covariant derivative of the base `base`;
* `tower_eq_covKAExt` — `tower (lcOf (G 0)) (aOf G t) k = covKAExt G t k` (definitional);
* `valOp` / `ValBound` — the value-level operator (on the `Classical.epsilon`-chosen extensions
  `smoothExt x ·`) and the operator-norm bound shape used by the conclusion of
  `Work.Diff.EXT.conn_diff_cov_bounds`;
* the *insertion* operators `insD`, `insA`, `insB`, `insC` expressing the effect of the connection
  difference `Δ = ∇^{g_t} − ∇^{g_0}` on one recursion step, and the statement `step_flip` of the
  **flip identity**: changing the connection in one `step` only inserts the *value* of the
  connection difference into a slot.

The point of the parallel tower `tower cov' base` (for a second connection `cov'`) is the
*conversion* between the two towers: the fixed-connection tower `∇^{0,k}` (the frozen `covKAExt`)
and the moving-connection tower `∇^{g_t,k}` (whose derivatives of the *curvature* are bounded by
`ShiBounds`).  `step_flip` is the first-order relation from which that conversion is built.
-/

set_option linter.unusedSectionVars false

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology
open Bundle ContDiff Set VectorField CovariantDerivative Metric

namespace Work.Diff.EXT.ATower

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]

/-- A tangent field on `M`. -/
abbrev TF : Type _ := Π y : M, TangentSpace I y

/-- **A field-level operator with `k` derivative slots and three value slots** (the arity of the
connection-difference tower). -/
abbrev Op3 (k : ℕ) : Type _ := (Fin k → TF (I := I) (M := M)) → TF (I := I) (M := M) →
  TF (I := I) (M := M) → TF (I := I) (M := M) → M → ℝ

/-- The *recursion step*: `step cov τ` is `∇_{V 0} τ` computed with the connection `cov`, i.e. the
ordinary derivative of `τ` along `V 0` minus the connection correction in every slot. -/
noncomputable def step (cov : CovariantDerivative I E (TangentSpace I (M := M))) {k : ℕ}
    (τ : Op3 (I := I) (M := M) k) : Op3 (I := I) (M := M) (k + 1) :=
  fun v A B C x =>
    mvfderiv I (τ (fun i : Fin k => v i.succ) A B C) x (v 0 x)
      - ∑ i : Fin k, τ (Function.update (fun j : Fin k => v j.succ) i
          (fun y => cov (v i.succ) y (v 0 y))) A B C x
      - τ (fun i : Fin k => v i.succ) (fun y => cov A y (v 0 y)) B C x
      - τ (fun i : Fin k => v i.succ) A (fun y => cov B y (v 0 y)) C x
      - τ (fun i : Fin k => v i.succ) A B (fun y => cov C y (v 0 y)) x

/-- **The tower**: the `k`-th iterated covariant derivative of the base operator with respect to
the connection `cov`. -/
noncomputable def tower (cov : CovariantDerivative I E (TangentSpace I (M := M)))
    (base : Op3 (I := I) (M := M) 0) :
    ∀ k : ℕ, Op3 (I := I) (M := M) k
  | 0, v, A, B, C => base v A B C
  | k + 1, v, A, B, C => step cov (tower cov base k) v A B C

/-- **The frozen definition is the tower of `aOf` with the background connection `∇^{G 0}`.**
Definitional, by induction on `k`. -/
theorem tower_eq_covKAExt (G : ℝ → SMet I M) (t : ℝ) (k : ℕ) :
    tower (lcOf (G 0)) (fun _ => aOf G t) k = covKAExt G t k := by
  induction k with
  | zero => rfl
  | succ k ih =>
      funext v A B C x
      simp only [tower, step, covKAExt, ih]

/-- **The value-level operator**: `τ` evaluated on the `Classical.epsilon`-chosen smooth extensions
of the `k` direction vectors and the three argument vectors.  This is the object bounded by
`Work.Diff.EXT.conn_diff_cov_bounds`. -/
noncomputable def valOp {k : ℕ} (τ : Op3 (I := I) (M := M) k) (x : M)
    (v : Fin k → TangentSpace I x) (a b c : TangentSpace I x) : ℝ :=
  τ (fun i => smoothExt x (v i)) (smoothExt x a) (smoothExt x b) (smoothExt x c) x

/-- The value of the frozen `covKAExt` is `valOp` of the tower. -/
theorem valOp_tower_eq_covKAExt (G : ℝ → SMet I M) (t : ℝ) (k : ℕ)
    (x : M) (v : Fin k → TangentSpace I x) (a b c : TangentSpace I x) :
    valOp (tower (lcOf (G 0)) (fun _ => aOf G t) k) x v a b c
      = covKAExt G t k (fun i => smoothExt x (v i)) (smoothExt x a) (smoothExt x b)
          (smoothExt x c) x := by
  rw [tower_eq_covKAExt]
  rfl

/-- **The operator-norm bound shape** (in the metric `G t`).  `ValBound G t k τ C` is the statement
that the `k`-th tower object `τ`, evaluated at any `x` on any vectors, is bounded by `C` times the
product of the `G t`-norms. -/
def ValBound (G : ℝ → SMet I M) (t : ℝ) (k : ℕ) (τ : Op3 (I := I) (M := M) k) (C : ℝ) : Prop :=
  ∀ x : M, ∀ (v : Fin k → TangentSpace I x) (a b c : TangentSpace I x),
    |valOp τ x v a b c|
      ≤ C * (Finset.univ.prod (fun i : Fin k => Real.sqrt ((G t).inner x (v i) (v i))))
          * Real.sqrt ((G t).inner x a a) * Real.sqrt ((G t).inner x b b)
          * Real.sqrt ((G t).inner x c c)

/-! ## The insertion operators and the flip identity

For a `(1,2)`-tensor field `δ` (used with `δ = ∇^{g_t} − ∇^{g_0}`) and an operator `τ`, the
operators `insD i δ τ`, `insA δ τ`, `insB δ τ`, `insC δ τ` are `τ` with one slot replaced by the
field `δ(·, V 0)`; they are exactly the correction terms appearing when one changes the connection
in `step`. -/

/-- Insertion of the difference field into the `i`-th derivative slot. -/
noncomputable def insD {k : ℕ} (i : Fin k) (δ : TF (I := I) (M := M) → TF (I := I) (M := M) → TF (I := I) (M := M))
    (τ : Op3 (I := I) (M := M) k) : Op3 (I := I) (M := M) (k + 1) :=
  fun v A B C x =>
    τ (Function.update (fun j : Fin k => v j.succ) i (fun y => δ (v i.succ) (v 0) y)) A B C x

/-- Insertion of the difference field into the first value slot. -/
noncomputable def insA {k : ℕ} (δ : TF (I := I) (M := M) → TF (I := I) (M := M) → TF (I := I) (M := M))
    (τ : Op3 (I := I) (M := M) k) : Op3 (I := I) (M := M) (k + 1) :=
  fun v A B C x => τ (fun j : Fin k => v j.succ) (fun y => δ A (v 0) y) B C x

/-- Insertion of the difference field into the second value slot. -/
noncomputable def insB {k : ℕ} (δ : TF (I := I) (M := M) → TF (I := I) (M := M) → TF (I := I) (M := M))
    (τ : Op3 (I := I) (M := M) k) : Op3 (I := I) (M := M) (k + 1) :=
  fun v A B C x => τ (fun j : Fin k => v j.succ) A (fun y => δ B (v 0) y) C x

/-- Insertion of the difference field into the third value slot. -/
noncomputable def insC {k : ℕ} (δ : TF (I := I) (M := M) → TF (I := I) (M := M) → TF (I := I) (M := M))
    (τ : Op3 (I := I) (M := M) k) : Op3 (I := I) (M := M) (k + 1) :=
  fun v A B C x => τ (fun j : Fin k => v j.succ) A B (fun y => δ C (v 0) y) x

/-- A tangent field which is smooth. -/
abbrev Sm (X : TF (I := I) (M := M)) : Prop := CMDiff ∞ (T% X)

/-- Smoothness of a tangent field, with the model and the manifold *explicit* (so that the
statement of a lemma pins them down without relying on inference). -/
def SmE (I : ModelWithCorners ℝ E H) (M : Type*) [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I (⊤ : ℕ∞) M] (X : Π y : M, TangentSpace I y) : Prop := CMDiff ∞ (T% X)

/-- Smoothness of a *scalar* function on `M`, with the model and the manifold explicit. -/
def SmF (I : ModelWithCorners ℝ E H) (M : Type*) [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I (⊤ : ℕ∞) M] (f : M → ℝ) : Prop := CMDiff ∞ f

/-- `SlotAdd τ` says that `τ` is additive in each of its `k + 3` slots, **on smooth fields**.
(The smoothness side conditions are essential: `mvfderiv` is additive only on differentiable
functions, so unconditional additivity of `tower cov base k` would be false.) -/
def SlotAdd {k : ℕ} (τ : Op3 (I := I) (M := M) k) : Prop :=
  (∀ (i : Fin k) (v : Fin k → TF (I := I) (M := M)) (W W' : TF (I := I) (M := M))
      (A B C : TF (I := I) (M := M)),
    (∀ j, SmE I M (v j)) → SmE I M W → SmE I M W' → SmE I M A → SmE I M B → SmE I M C →
    τ (Function.update v i (W + W')) A B C = τ (Function.update v i W) A B C
      + τ (Function.update v i W') A B C) ∧
  (∀ (v : Fin k → TF (I := I) (M := M)) (A A' B C : TF (I := I) (M := M)),
    (∀ j, SmE I M (v j)) → SmE I M A → SmE I M A' → SmE I M B → SmE I M C →
    τ v (A + A') B C = τ v A B C + τ v A' B C) ∧
  (∀ (v : Fin k → TF (I := I) (M := M)) (A B B' C : TF (I := I) (M := M)),
    (∀ j, SmE I M (v j)) → SmE I M A → SmE I M B → SmE I M B' → SmE I M C →
    τ v A (B + B') C = τ v A B C + τ v A B' C) ∧
  (∀ (v : Fin k → TF (I := I) (M := M)) (A B C C' : TF (I := I) (M := M)),
    (∀ j, SmE I M (v j)) → SmE I M A → SmE I M B → SmE I M C → SmE I M C' →
    τ v A B (C + C') = τ v A B C + τ v A B C')

end Work.Diff.EXT.ATower
