import Mathlib
import Submission.Work.Diff.EXT.curvDefs
import Submission.Work.Diff.GE.dRmPhi
import Submission.Commons.Geometry.Manifold.VectorField.mvfderiv_apply_contMDiff
import Submission.Commons.Geometry.Manifold.VectorField.exists_frame_decomposition_of_apply_eq_zero
import Submission.Commons.Geometry.Manifold.VectorBundle.CovariantDerivative.contMDiff_cov_apply

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The tower of covariant derivatives of the curvature as a `C^∞(M)`-multilinear operation

The frozen definition `Work.Diff.EXT.covKRmExt g k` (`Submission/Work/Diff/EXT/local_ext_of_bounded_curv.lean`)
defines `∇^k Rm` on *smooth fields*: the `(k+1)`-st covariant derivative is
`∂_{v₀}(∇^k Rm) − Σ_slots (∇^k Rm)(…, ∇_{v₀}(slot), …)`, evaluated at the point where the fields
are read off.

This module isolates the recursion from the (fixed) definition, so that the *structural* properties
of `∇^k Rm` can be proved once and for all by induction on `k`, independently of the metric:

* `SmField`, `SmFun`, `SmTuple` — smooth sections / functions / tuples;
* `KOp k` — a field-level operator with `k` derivative slots and four curvature slots;
* `IsTens k τ` — `τ` is `C^∞(M)`-multilinear in its `k + 4` slots and smooth on smooth tuples;
* `step g τ` — the recursion step: the covariant derivative in the direction of a *new* first slot;
* `tower g k` — the tower, `tower g 0` = the curvature form `rmP`, `tower g (k+1) = step g (tower g k)`;
* `tower_eq_covKRmExt` (in `Tower/bridge.lean`) — `tower g k V F = covKRmExt g k V (F 0) (F 1) (F 2) (F 3)`;
* `valOp k τ x p` — the *value-level* operator: `τ` evaluated on the `Classical.epsilon`-chosen
  extensions `smoothExt x ·` of the components of `p : Fin k ⊕ Fin 4 → TₓM` (the `Fin k` part are
  the derivative slots, the `Fin 4` part the four curvature slots).

The mathematics of the induction is `IsTens k τ → IsTens (k+1) (step g τ)`.  The delicate part is
the *homogeneity* in a slot of the old operator: differentiating `f • τ V F` produces the Leibniz
term `(df) ⊗ (τ V F)`, which is exactly cancelled by the corresponding connection term
`τ (update … (∇ (f • Vᵢ))) = τ (update … (f • ∇Vᵢ)) + (df) · τ (update … Vᵢ)`.
-/

set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle ContDiff Set VectorField CovariantDerivative Metric

namespace Work.Diff.EXT.Tower

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M] [T2Space M]

/-- A smooth section of the tangent bundle. -/
abbrev SmField (X : TField (I := I) (M := M)) : Prop := CMDiff ∞ (T% X)

/-- A smooth function on `M`. -/
abbrev SmFun (f : M → ℝ) : Prop := CMDiff ∞ f

/-- A tuple of smooth sections. -/
abbrev SmTuple {ι : Type*} (F : ι → TField (I := I) (M := M)) : Prop := ∀ i, SmField (F i)

/-- A field-level operator with `k` derivative slots and four curvature slots. -/
abbrev KOp (k : ℕ) : Type _ :=
  (Fin k → TField (I := I) (M := M)) → (Fin 4 → TField (I := I) (M := M)) → M → ℝ

/-- **`τ` is a `C^∞(M)`-multilinear smooth operation** on its `k + 4` smooth sections: additive in
each slot, homogeneous with respect to multiplication by a smooth function, and `τ V F` is a smooth
function of the point.  (These are exactly the facts that the induction `k → k+1` needs; together
with germ-locality they imply that `τ` depends only on the *values* at the point and is multilinear
there — see `Tower/value_dep.lean` and `Tower/valOp_linear.lean`.) -/
def IsTens (k : ℕ) (τ : KOp (I := I) (M := M) k) : Prop :=
  (∀ (i : Fin k) (V : Fin k → TField (I := I) (M := M)) (W : TField (I := I) (M := M))
      (F : Fin 4 → TField (I := I) (M := M)),
      SmTuple V → SmField W → SmTuple F →
      τ (Function.update V i (V i + W)) F = τ V F + τ (Function.update V i W) F) ∧
  (∀ (i : Fin k) (f : M → ℝ) (V : Fin k → TField (I := I) (M := M))
      (F : Fin 4 → TField (I := I) (M := M)),
      SmFun (I := I) (M := M) f → SmTuple V → SmTuple F →
      τ (Function.update V i (f • V i)) F = f • τ V F) ∧
  (∀ (j : Fin 4) (V : Fin k → TField (I := I) (M := M)) (F : Fin 4 → TField (I := I) (M := M))
      (W : TField (I := I) (M := M)),
      SmTuple V → SmTuple F → SmField W →
      τ V (Function.update F j (F j + W)) = τ V F + τ V (Function.update F j W)) ∧
  (∀ (j : Fin 4) (f : M → ℝ) (V : Fin k → TField (I := I) (M := M))
      (F : Fin 4 → TField (I := I) (M := M)),
      SmFun (I := I) (M := M) f → SmTuple V → SmTuple F →
      τ V (Function.update F j (f • F j)) = f • τ V F) ∧
  (∀ (V : Fin k → TField (I := I) (M := M)) (F : Fin 4 → TField (I := I) (M := M)),
      SmTuple V → SmTuple F → SmFun (I := I) (M := M) (τ V F))

/-- **The recursion step.**  `step g τ V F` is the covariant derivative of the operation `τ` in the
direction of the field `V 0`, evaluated on the remaining `k` derivative slots `V (i+1)` and the four
curvature slots `F`: it is `∂_{V 0}(τ (V∘succ) F)` minus the connection correction in each of the
`k + 4` slots of `τ`. -/
noncomputable def step (g : SMet I M) {k : ℕ} (τ : KOp (I := I) (M := M) k) :
    KOp (I := I) (M := M) (k + 1) :=
  fun V F y =>
    mvfderiv I (τ (fun i : Fin k => V i.succ) F) y (V 0 y)
      - (∑ i : Fin k, τ (Function.update (fun j : Fin k => V j.succ) i
            (fun z => lcOf g (V i.succ) z (V 0 z))) F y)
      - ∑ j : Fin 4, τ (fun i : Fin k => V i.succ)
            (Function.update F j (fun z => lcOf g (F j) z (V 0 z))) y

/-- **The tower of covariant derivatives of the curvature**, as a field-level operation:
`tower g 0` is the curvature form `rmP`, and `tower g (k+1) = step g (tower g k)`.  By
`tower_eq_covKRmExt` this is the frozen `covKRmExt g k` with the four curvature slots packaged as a
`Fin 4`-tuple. -/
noncomputable def tower (g : SMet I M) : ∀ k : ℕ, KOp (I := I) (M := M) k
  | 0, _, F => fun y => rmP g y (F 0 y) (F 1 y) (F 2 y) (F 3 y)
  | k + 1, V, F => step g (tower g k) V F

/-- **The value-level operator**: `τ` evaluated on the `Classical.epsilon`-chosen smooth extensions
`smoothExt x ·` of the components of `p`.  The `Fin k` part of the index type carries the `k`
derivative slots, the `Fin 4` part the four curvature slots. -/
noncomputable def valOp (k : ℕ) (τ : KOp (I := I) (M := M) k) (x : M)
    (p : Fin k ⊕ Fin 4 → TangentSpace I x) : ℝ :=
  τ (fun i => smoothExt x (p (Sum.inl i))) (fun j => smoothExt x (p (Sum.inr j))) x

/-- `valOp` written out. -/
theorem valOp_apply (k : ℕ) (τ : KOp (I := I) (M := M) k) (x : M)
    (p : Fin k ⊕ Fin 4 → TangentSpace I x) :
    valOp k τ x p = τ (fun i => smoothExt x (p (Sum.inl i)))
      (fun j => smoothExt x (p (Sum.inr j))) x := rfl

end Work.Diff.EXT.Tower
