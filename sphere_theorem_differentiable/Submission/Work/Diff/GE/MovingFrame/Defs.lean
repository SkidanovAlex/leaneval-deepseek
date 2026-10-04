import Mathlib
import Submission.Work.Diff.GE.NablaRm

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Shared definitions for the moving-frame evolution estimate of `∇Rm`

The target lemma `Work.Diff.GE.hasDerivWithinAt_covRm_frame_le` states the evolution estimate for
the components of `∇Rm` **in a moving orthonormal frame** `s ↦ e s` at a point `x`:

`∂ₛ ⟪∇Rm, e s m ⊗ e s i ⊗ e s j ⊗ e s k ⊗ e s l⟫ ≤ Δ∇Rm + C(1+K)|Rm||∇Rm|`.

The proof splits into two halves.

* The *fixed-vector* half (the colleague's lemma `Work.Diff.GE.hasDerivWithinAt_covRm_le`): the
  derivative of `s ↦ covRm (G s) x v a b c d` for fixed vectors `v,a,b,c,d`, bounded by the rough
  Laplacian plus `C'|Rm||∇Rm|∏√(g(vᵢ,vᵢ))`.
* The *moving-frame* half (this file's user): a product rule, which needs `covRm` to be a genuine
  multilinear form of its five arguments (`covRm5_multilinear`), the Frobenius bound
  `|∇Rm(w₁,…,w₅)| ≤ √|∇Rm|² ∏√(g(wᵢ,wᵢ))` (`covRm5_frobBound`), and the fact that a family of
  multilinear forms converging pointwise is eventually bounded in operator norm
  (`multilinear_eventually_bounded`).

This module only fixes the vocabulary (`covRm5`, the frame tuple, the product of the argument
norms, the multilinearity predicate) so that the pieces can be stated uniformly.
-/

set_option linter.unusedSectionVars false

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle ContDiff Set VectorField CovariantDerivative Metric

namespace Work.Diff.GE.MovingFrame

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]

/-- The `(0,5)`-tensor `∇Rm` as a function of the five tangent vectors. -/
noncomputable def covRm5 (g : SMet I M) (x : M) (w : Fin 5 → TangentSpace I x) : ℝ :=
  covRm g x (w 0) (w 1) (w 2) (w 3) (w 4)

/-- The tuple `(e m, e i, e j, e k, e l)` of vectors of a frame `e`. -/
def frameTuple (x : M) {n : ℕ} (e : Fin n → TangentSpace I x) (m i j k l : Fin n) :
    Fin 5 → TangentSpace I x :=
  ![e m, e i, e j, e k, e l]

@[simp] lemma frameTuple_apply (x : M) {n : ℕ} (e : Fin n → TangentSpace I x) (m i j k l : Fin n)
    (p : Fin 5) :
    frameTuple (I := I) x e m i j k l p =
      (![e m, e i, e j, e k, e l] : Fin 5 → TangentSpace I x) p := rfl

@[simp] lemma frameTuple_zero (x : M) {n : ℕ} (e : Fin n → TangentSpace I x) (m i j k l : Fin n) :
    frameTuple (I := I) x e m i j k l 0 = e m := rfl

@[simp] lemma frameTuple_one (x : M) {n : ℕ} (e : Fin n → TangentSpace I x) (m i j k l : Fin n) :
    frameTuple (I := I) x e m i j k l 1 = e i := rfl

@[simp] lemma frameTuple_two (x : M) {n : ℕ} (e : Fin n → TangentSpace I x) (m i j k l : Fin n) :
    frameTuple (I := I) x e m i j k l 2 = e j := rfl

@[simp] lemma frameTuple_three (x : M) {n : ℕ} (e : Fin n → TangentSpace I x)
    (m i j k l : Fin n) :
    frameTuple (I := I) x e m i j k l 3 = e k := rfl

@[simp] lemma frameTuple_four (x : M) {n : ℕ} (e : Fin n → TangentSpace I x) (m i j k l : Fin n) :
    frameTuple (I := I) x e m i j k l 4 = e l := rfl

/-- The time-dependent tuple `s ↦ (e s m, e s i, e s j, e s k, e s l)`, evaluated at time `t`. -/
def frameTupleS (x : M) {n : ℕ} (e : ℝ → Fin n → TangentSpace I x) (t : ℝ) (m i j k l : Fin n) :
    Fin 5 → TangentSpace I x :=
  ![e t m, e t i, e t j, e t k, e t l]

@[simp] lemma frameTupleS_apply (x : M) {n : ℕ} (e : ℝ → Fin n → TangentSpace I x) (t : ℝ)
    (m i j k l : Fin n) (p : Fin 5) :
    frameTupleS (I := I) x e t m i j k l p =
      (![e t m, e t i, e t j, e t k, e t l] : Fin 5 → TangentSpace I x) p := rfl

@[simp] lemma frameTupleS_zero (x : M) {n : ℕ} (e : ℝ → Fin n → TangentSpace I x) (t : ℝ)
    (m i j k l : Fin n) : frameTupleS (I := I) x e t m i j k l 0 = e t m := rfl

@[simp] lemma frameTupleS_one (x : M) {n : ℕ} (e : ℝ → Fin n → TangentSpace I x) (t : ℝ)
    (m i j k l : Fin n) : frameTupleS (I := I) x e t m i j k l 1 = e t i := rfl

@[simp] lemma frameTupleS_two (x : M) {n : ℕ} (e : ℝ → Fin n → TangentSpace I x) (t : ℝ)
    (m i j k l : Fin n) : frameTupleS (I := I) x e t m i j k l 2 = e t j := rfl

@[simp] lemma frameTupleS_three (x : M) {n : ℕ} (e : ℝ → Fin n → TangentSpace I x) (t : ℝ)
    (m i j k l : Fin n) : frameTupleS (I := I) x e t m i j k l 3 = e t k := rfl

@[simp] lemma frameTupleS_four (x : M) {n : ℕ} (e : ℝ → Fin n → TangentSpace I x) (t : ℝ)
    (m i j k l : Fin n) : frameTupleS (I := I) x e t m i j k l 4 = e t l := rfl

/-- The list of indices `(m,i,j,k,l)` as an element of `Fin 5 → Fin n`.  (Note that these need not be
distinct: only the *diagonal* entries of the metric on the tuple are used.) -/
def frameIndex {n : ℕ} (m i j k l : Fin n) : Fin 5 → Fin n := ![m, i, j, k, l]

@[simp] lemma frameIndex_zero {n : ℕ} (m i j k l : Fin n) : frameIndex m i j k l 0 = m := rfl

@[simp] lemma frameIndex_one {n : ℕ} (m i j k l : Fin n) : frameIndex m i j k l 1 = i := rfl

@[simp] lemma frameIndex_two {n : ℕ} (m i j k l : Fin n) : frameIndex m i j k l 2 = j := rfl

@[simp] lemma frameIndex_three {n : ℕ} (m i j k l : Fin n) : frameIndex m i j k l 3 = k := rfl

@[simp] lemma frameIndex_four {n : ℕ} (m i j k l : Fin n) : frameIndex m i j k l 4 = l := rfl

/-- The rough Laplacian `Δ∇Rm` as a function of the five vectors. -/
noncomputable def lapCovRmAt5 (g : SMet I M) (x : M) (w : Fin 5 → TangentSpace I x) : ℝ :=
  lapCovRmAt g x (w 0) (w 1) (w 2) (w 3) (w 4)

/-- The product of the `g`-norms of the five arguments (the factor multiplying `C|Rm||∇Rm|` in the
fixed-vector estimate). -/
noncomputable def argNorms (g : SMet I M) (x : M) (w : Fin 5 → TangentSpace I x) : ℝ :=
  ∏ p, Real.sqrt ((g.inner x (w p) (w p)))

/-- The Frobenius norm `√|∇Rm|²` of the metric `g` at `x`. -/
noncomputable def dRmNorm (g : SMet I M) (x : M) : ℝ :=
  Real.sqrt (dRmNormSq g x)

/-- `f` is a five-fold multilinear form (in the `Function.update` formulation, i.e. the two fields
of `MultilinearMap.mk`). -/
def IsMulti5 (V : Type*) [AddCommMonoid V] [Module ℝ V] (f : (Fin 5 → V) → ℝ) : Prop :=
  (∀ (w : Fin 5 → V) (i : Fin 5) (a b : V),
      f (Function.update w i (a + b)) = f (Function.update w i a) + f (Function.update w i b)) ∧
    (∀ (w : Fin 5 → V) (i : Fin 5) (c : ℝ) (a : V),
      f (Function.update w i (c • a)) = c * f (Function.update w i a))

end Work.Diff.GE.MovingFrame
