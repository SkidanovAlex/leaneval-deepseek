import Mathlib
import Submission.Work.Diff.GE.NablaRm
import Submission.Work.Diff.GE.ReactionDefs
import Submission.Work.Diff.GE.curvbasic
import Submission.Work.Diff.EXT.covKRmExt_eval_bound
import Submission.Work.Diff.EXT.evolK_bridges

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The evaluation bound for `∇Rm`

`Work.Diff.EXT.multilinear_frame_bound` is the Hilbert–Schmidt (Frobenius) bound for an arbitrary
multilinear form `T` on a finite-dimensional real inner product space: for an orthonormal family `e`
of full cardinality,

`|T p| ≤ √(∑_w (T (e ∘ w))²) · ∏_s √⟪p s, p s⟫`.

`∇Rm` is exactly such a multilinear form: the `EXT` area has the packaged tower
`Work.Diff.EXT.Kpt g x 1 = ckt g 1`, whose multilinear version is `Work.Diff.EXT.KptLin hLC g x 1`,
and the two bridges

* `Work.Diff.EXT.covKRm_one` : `covKRm g x 1 (fun _ ↦ v) a b c d = covRm g x v a b c d`,
* `Work.Diff.EXT.Kpt_component_sum`/`curvNormK_one_eq_dRmNormSq` :
  `∑_w (Kpt g x 1 (e ∘ w))² = curvNormK g x 1 = dRmNormSq g x`,

identify both sides of the Hilbert–Schmidt bound with the frozen quantities `covRm` and
`dRmNormSq`.  The product of the five square roots is the product of the `g`-norms of the five
vectors by `Fin.prod_univ_five`.
-/

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology
open Bundle ContDiff Set VectorField CovariantDerivative Metric

set_option linter.style.haveILetI false

namespace Work.Diff.GE

theorem covRm_norm_bound
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ((⊤ : ENat) : WithTop ENat) M]
    [I.Boundaryless] [T2Space M] [CompactSpace M]
    (hLC : Submission.Diff.LCSmooth I M) :
    ∀ (g : Submission.Diff.SMet I M) (x : M) (v a b c d : TangentSpace I x),
      |Submission.Diff.covRm g x v a b c d|
        ≤ Real.sqrt (Submission.Diff.dRmNormSq g x)
          * (Real.sqrt (g.inner x v v) * Real.sqrt (g.inner x a a)
             * Real.sqrt (g.inner x b b) * Real.sqrt (g.inner x c c)
             * Real.sqrt (g.inner x d d)) := by
  intro g x v a b c d
  -- work in the metric `g`: `g.inner` is then the instance inner product
  letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  haveI : IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x) := inferInstance
  -- the chosen frame is orthonormal
  have hone : Orthonormal ℝ (onFrame g x) := by
    rw [orthonormal_iff_ite]
    intro i j
    rw [show inner ℝ (onFrame g x i) (onFrame g x j)
        = g.inner x (onFrame g x i) (onFrame g x j) from rfl]
    exact isONFrame_onFrame g x i j
  -- the tuple of the five arguments
  set p : Fin 5 → TangentSpace I x := ![v, a, b, c, d]
  -- the Hilbert–Schmidt bound for the multilinear form `∇Rm`
  have hb := Work.Diff.EXT.multilinear_frame_bound (N := 5) (by norm_num)
    (Work.Diff.EXT.KptLin hLC g x 1) (onFrame g x) hone p
  -- the left-hand side is `covRm g x v a b c d`
  have hL : (Work.Diff.EXT.KptLin hLC g x 1) p = Submission.Diff.covRm g x v a b c d := by
    show Work.Diff.EXT.Kpt g x 1 p = Submission.Diff.covRm g x v a b c d
    have hfun : p = Fin.append (fun _ : Fin 1 => v) ![a, b, c, d] := by
      funext i
      fin_cases i <;> rfl
    rw [hfun, ← Work.Diff.EXT.covKRm_eq_Kpt g x 1 (fun _ : Fin 1 => v) a b c d,
      Work.Diff.EXT.covKRm_one]
  -- the Frobenius sum is `dRmNormSq`
  have hS : (∑ w : Fin 5 → Fin (Module.finrank ℝ E),
        ((Work.Diff.EXT.KptLin hLC g x 1) (fun s => onFrame g x (w s))) ^ 2)
      = Submission.Diff.dRmNormSq g x := by
    rw [show (∑ w : Fin 5 → Fin (Module.finrank ℝ E),
          ((Work.Diff.EXT.KptLin hLC g x 1) (fun s => onFrame g x (w s))) ^ 2)
        = ∑ w : Fin (1 + 4) → Fin (Module.finrank ℝ E),
            (Work.Diff.EXT.Kpt g x 1 (fun s => onFrame g x (w s))) ^ 2 from rfl,
      Work.Diff.EXT.Kpt_component_sum g x 1, Work.Diff.EXT.curvNormK_one_eq_dRmNormSq]
  -- the product of the five square roots
  have hP : (∏ s : Fin 5, Real.sqrt (inner ℝ (p s) (p s)))
      = Real.sqrt (g.inner x v v) * Real.sqrt (g.inner x a a) * Real.sqrt (g.inner x b b)
        * Real.sqrt (g.inner x c c) * Real.sqrt (g.inner x d d) := by
    have h0 : Real.sqrt (inner ℝ (p 0) (p 0)) = Real.sqrt (g.inner x v v) := rfl
    have h1 : Real.sqrt (inner ℝ (p 1) (p 1)) = Real.sqrt (g.inner x a a) := rfl
    have h2 : Real.sqrt (inner ℝ (p 2) (p 2)) = Real.sqrt (g.inner x b b) := rfl
    have h3 : Real.sqrt (inner ℝ (p 3) (p 3)) = Real.sqrt (g.inner x c c) := rfl
    have h4 : Real.sqrt (inner ℝ (p 4) (p 4)) = Real.sqrt (g.inner x d d) := rfl
    rw [Fin.prod_univ_five, h0, h1, h2, h3, h4]
  calc |Submission.Diff.covRm g x v a b c d|
      = |(Work.Diff.EXT.KptLin hLC g x 1) p| := by rw [hL]
    _ ≤ Real.sqrt (∑ w : Fin 5 → Fin (Module.finrank ℝ E),
            ((Work.Diff.EXT.KptLin hLC g x 1) (fun s => onFrame g x (w s))) ^ 2)
          * ∏ s : Fin 5, Real.sqrt (inner ℝ (p s) (p s)) := hb
    _ = Real.sqrt (Submission.Diff.dRmNormSq g x)
          * (Real.sqrt (g.inner x v v) * Real.sqrt (g.inner x a a)
             * Real.sqrt (g.inner x b b) * Real.sqrt (g.inner x c c)
             * Real.sqrt (g.inner x d d)) := by rw [hS, hP]

end Work.Diff.GE
