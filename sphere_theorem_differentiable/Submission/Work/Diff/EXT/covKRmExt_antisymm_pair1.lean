import Mathlib
import Submission.Work.Diff.EXT.evolKDefs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Antisymmetry of `∇^k Rm` in its first two curvature slots

`Work.Diff.EXT.covKRmExt g k v A B C D` is the `k`-th covariant derivative `∇^k Rm` of the
curvature of the metric `g`, evaluated on the `k` derivative slots `v` and the four curvature
slots `A B C D`.  Curvature of any connection is skew in its first two slots,
`R(X,Y)Z = -R(Y,X)Z`, and covariant differentiation preserves that: `∇^k Rm` is skew in its first
two curvature slots as well.  This file records that fact:

`covKRmExt g k v A B C D x = - covKRmExt g k v B A C D x`.

The proof is an induction on `k` on the defining recursion of `covKRmExt`.  At `k = 0` it is the
algebraic skewness of the curvature (`rmP_antisymm_pair1` below, proved directly from the
definition `rmP g x a b c d = ⟪R(a,b)d, c⟫` and `curv_antisymm` of the *general* covariant
derivative, so that no smoothness hypothesis on the metric and no `T2Space M` is needed).  At
`k+1` each of the `k + 4` terms of the Leibniz expansion (`∂_{v₀}` in the direction slot, the `k`
corrections on the derivative slots, and the four corrections on the curvature slots) is the
negative of the corresponding term of the transposed tuple: for the `mvfderiv` term because the
function is pointwise the negative of the other one (`mvfderiv_neg`), for the other `k + 4` terms
directly by the induction hypothesis.  The resulting identity is then linear algebra (`ring`).
-/

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1000000

namespace Work.Diff.EXT

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle ContDiff Set VectorField CovariantDerivative Metric

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]

/-! ## The two algebraic inputs -/

/-- Pointwise version of the antisymmetry `R(X,Y)Z = -R(Y,X)Z` of the curvature of an arbitrary
covariant derivative.  (This is `Submission.Curvature.curv_antisymm_apply`, restated so that no
`T2Space M` hypothesis is carried along; the skewness is pure algebra from the definition
`R(X,Y)Z = ∇_X∇_Y Z − ∇_Y∇_X Z − ∇_{[X,Y]}Z` and `[X,Y] = -[Y,X]`.) -/
theorem curv_antisymm_apply_noT2 (cov : CovariantDerivative I E (TangentSpace I (M := M)))
    (X Y Z : Π x : M, TangentSpace I x) (x : M) :
    curv cov X Y Z x = - curv cov Y X Z x := by
  have hfun : curv cov X Y Z = - curv cov Y X Z := by
    funext y
    unfold curv
    simp only [Pi.neg_apply]
    rw [VectorField.mlieBracket_swap_apply]
    rw [map_neg]
    abel
  exact congrFun hfun x

/-- `rmP g x a b c d = ⟪R(a,b)d, c⟫` is antisymmetric in its first two arguments.  Pure algebra:
no smoothness of `g` (no `LCSmooth`) and no `T2Space M` is involved. -/
theorem rmP_antisymm_pair1 (g : SMet I M) (x : M) (a b c d : TangentSpace I x) :
    rmP g x a b c d = - rmP g x b a c d := by
  letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  have h := curv_antisymm_apply_noT2 (I := I) (M := M) (lcOf g) (smoothExt x b) (smoothExt x a)
    (smoothExt x d) x
  simp only [rmP, rmVec]
  rw [h]
  simp

/-! ## The induction -/

/-- `∇^k Rm` is antisymmetric in its first two curvature slots.  Stated with the `k`-dependence in
the front so that the induction hypothesis is usable for every choice of the fields. -/
theorem covKRmExt_antisymm_pair1_aux (g : Submission.Diff.SMet I M) (k : ℕ) :
    ∀ (v : Fin k → (Π y : M, TangentSpace I y)) (A B C D : Π y : M, TangentSpace I y) (x : M),
      Work.Diff.EXT.covKRmExt g k v A B C D x
        = - Work.Diff.EXT.covKRmExt g k v B A C D x := by
  induction k with
  | zero =>
    intro v A B C D x
    simp only [Work.Diff.EXT.covKRmExt]
    exact rmP_antisymm_pair1 g x (A x) (B x) (C x) (D x)
  | succ k ih =>
    intro v A B C D x
    -- Expand both sides through the defining recursion of `covKRmExt`.
    simp only [Work.Diff.EXT.covKRmExt]
    -- The `∂_{v₀}` term: the transposed function is the pointwise negative of the original one.
    have h0 : (mvfderiv I (Work.Diff.EXT.covKRmExt g k (fun i : Fin k => v i.succ) B A C D) x)
          (v 0 x)
        = - (mvfderiv I (Work.Diff.EXT.covKRmExt g k (fun i : Fin k => v i.succ) A B C D) x)
          (v 0 x) := by
      have hfun : Work.Diff.EXT.covKRmExt g k (fun i : Fin k => v i.succ) B A C D
          = - (Work.Diff.EXT.covKRmExt g k (fun i : Fin k => v i.succ) A B C D) :=
        funext fun y => ih (fun i : Fin k => v i.succ) B A C D y
      rw [hfun, mvfderiv_neg]
      simp
    -- The `k` derivative-slot corrections.
    have hsum : ∀ i : Fin k, Work.Diff.EXT.covKRmExt g k
          (Function.update (fun j : Fin k => v j.succ) i
            (fun y => lcOf g (v i.succ) y (v 0 y))) B A C D x
        = - Work.Diff.EXT.covKRmExt g k
          (Function.update (fun j : Fin k => v j.succ) i
            (fun y => lcOf g (v i.succ) y (v 0 y))) A B C D x :=
      fun i => ih _ B A C D x
    -- The four curvature-slot corrections.
    have h1 := ih (fun i : Fin k => v i.succ) (fun y => lcOf g B y (v 0 y)) A C D x
    have h2 := ih (fun i : Fin k => v i.succ) B (fun y => lcOf g A y (v 0 y)) C D x
    have h3 := ih (fun i : Fin k => v i.succ) B A (fun y => lcOf g C y (v 0 y)) D x
    have h4 := ih (fun i : Fin k => v i.succ) B A C (fun y => lcOf g D y (v 0 y)) x
    simp only [h0, h1, h2, h3, h4, hsum, Finset.sum_neg_distrib]
    ring

/-- **`∇^k Rm` is antisymmetric in its first two curvature slots.** -/
theorem covKRmExt_antisymm_pair1
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
    (g : Submission.Diff.SMet I M) (x : M) (k : ℕ)
    (v : Fin k → (Π y : M, TangentSpace I y)) (A B C D : Π y : M, TangentSpace I y) :
    Work.Diff.EXT.covKRmExt g k v A B C D x = - Work.Diff.EXT.covKRmExt g k v B A C D x :=
  covKRmExt_antisymm_pair1_aux g k v A B C D x

end Work.Diff.EXT
