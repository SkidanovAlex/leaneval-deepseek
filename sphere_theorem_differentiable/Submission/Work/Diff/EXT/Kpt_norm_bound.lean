import Mathlib
import Submission.Work.Diff.EXT.covKRmExt_eval_bound

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

open Bundle Submission.Diff
open scoped ContDiff

namespace Work.Diff.EXT

/-- **The Hilbert–Schmidt (Frobenius) evaluation bound for `∇^k Rm`.**

The pointwise value `Kpt g x k w` of the `k`-th covariant derivative of the curvature at `x` on the
tuple of tangent vectors `w` is bounded by the square root of the Frobenius norm `curvNormK g x k`
(of `∇^k Rm` in the orthonormal frame `onFrame g x`) times the product of the Euclidean norms of the
vectors.  This is the sharp form (no additive constant) of the evaluation bound: it is the
Hilbert–Schmidt inequality `|T w| ≤ ‖T‖_Frobenius · ∏ ‖w s‖` applied to the multilinear form
`KptLin hLC g x k`, whose Frobenius norm squares to `curvNormK g x k`. -/

theorem Kpt_norm_bound
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M] [T2Space M]
    (hLC : Submission.Diff.LCSmooth I M) (g : Submission.Diff.SMet I M) (x : M) (k : ℕ)
    (w : Fin (k + 4) → TangentSpace I x) :
    |Work.Diff.EXT.Kpt g x k w| ≤ Real.sqrt (Work.Diff.EXT.curvNormK g x k)
      * ∏ r : Fin (k + 4), Real.sqrt (g.inner x (w r) (w r)) := by
  classical
  letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  haveI : IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x) :=
    inferInstance
  have hone : Orthonormal ℝ (onFrame g x) := by
    rw [orthonormal_iff_ite]
    intro i j
    rw [show inner ℝ (onFrame g x i) (onFrame g x j)
        = g.inner x (onFrame g x i) (onFrame g x j) from rfl]
    exact Work.Diff.GE.isONFrame_onFrame g x i j
  -- the Hilbert–Schmidt bound for the multilinear form `KptLin`
  have hb := multilinear_frame_bound (N := k + 4) (by omega) (KptLin hLC g x k)
    (onFrame g x) hone w
  have hb2 : |Kpt g x k w| ≤ Real.sqrt (∑ w' : Fin (k + 4) → Fin (Module.finrank ℝ E),
        (Kpt g x k (fun s => onFrame g x (w' s))) ^ 2)
      * ∏ s : Fin (k + 4), Real.sqrt (inner ℝ (w s) (w s)) := hb
  -- the Frobenius norm of `∇^k Rm` is `curvNormK`
  rw [Kpt_component_sum g x k] at hb2
  -- the inner product on the fibres coincides with `g.inner`
  have hprod : (∏ s : Fin (k + 4), Real.sqrt (inner ℝ (w s) (w s)))
      = ∏ r : Fin (k + 4), Real.sqrt (g.inner x (w r) (w r)) := by
    refine Finset.prod_congr rfl (fun r _ => ?_)
    rfl
  rw [hprod] at hb2
  exact hb2

end Work.Diff.EXT
