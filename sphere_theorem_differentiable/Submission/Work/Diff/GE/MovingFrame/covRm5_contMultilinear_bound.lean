import Mathlib
import Submission.Work.Diff.GE.MovingFrame.Defs
import Submission.Work.Diff.GE.MovingFrame.covRm5_multilinear
import Submission.Work.Diff.GE.curvbasic
import Submission.Work.Diff.EXT.covKRmExt_eval_bound

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.GE.MovingFrame

namespace Work.Diff.GE.MovingFrame

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle ContDiff Set VectorField CovariantDerivative Metric

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]

/-! ## The five-fold sum over tuples as an iterated sum

`dRmNormSq g x` is *defined* as the five-fold iterated sum of the squares of the components of
`∇Rm` in the frame `onFrame g x`.  The Cauchy–Schwarz (Hilbert–Schmidt) bound
`Work.Diff.EXT.multilinear_frame_bound`, on the other hand, produces the sum of the same squares
over all tuples `Fin 5 → Fin (finrank ℝ E)`.  The combinatorial lemma `sum_pi_fin5` below converts
between the two descriptions. -/

/-- The obvious equivalence between `Fin 5 → α` and the five-fold product `α × ⋯ × α`. -/
noncomputable def tupleEquiv5 (α : Type*) : (Fin 5 → α) ≃ (α × α × α × α × α) where
  toFun w := (w 0, w 1, w 2, w 3, w 4)
  invFun p := ![p.1, p.2.1, p.2.2.1, p.2.2.2.1, p.2.2.2.2]
  left_inv w := by funext i; fin_cases i <;> simp
  right_inv p := by simp

/-- A `Fin 5`-tuple is determined by its five values. -/
theorem vec5_eq {α : Type*} (w : Fin 5 → α) : ![w 0, w 1, w 2, w 3, w 4] = w := by
  funext i; fin_cases i <;> rfl

/-- **A sum over all tuples is the iterated sum.** -/
theorem sum_pi_fin5 {α : Type*} [Fintype α] (H : (Fin 5 → α) → ℝ) :
    (∑ w : Fin 5 → α, H w) = ∑ a, ∑ b, ∑ c, ∑ d, ∑ e, H ![a, b, c, d, e] := by
  rw [Fintype.sum_equiv (tupleEquiv5 α) H
      (fun p : α × α × α × α × α => H ![p.1, p.2.1, p.2.2.1, p.2.2.2.1, p.2.2.2.2])
      (fun w => by
        show H w = H ![w 0, w 1, w 2, w 3, w 4]
        exact congrArg H (vec5_eq w).symm)]
  simp only [Fintype.sum_prod_type]

/-! ## `∇Rm` as a multilinear form -/

/-- `∇Rm` as a genuine `ℝ`-multilinear form of its five arguments (the `MultilinearMap` version of
`Work.Diff.GE.MovingFrame.covRm5_multilinear`). -/
noncomputable def covRm5Lin (hLC : LCSmooth I M) (g : SMet I M) (x : M) :
    MultilinearMap ℝ (fun _ : Fin 5 => TangentSpace I x) ℝ :=
  MultilinearMap.mk' (covRm5 (I := I) g x) (covRm5_multilinear hLC g x).1
    (fun w i c a => by
      rw [smul_eq_mul]
      exact (covRm5_multilinear hLC g x).2 w i c a)

@[simp] theorem covRm5Lin_apply (hLC : LCSmooth I M) (g : SMet I M) (x : M)
    (w : Fin 5 → TangentSpace I x) :
    covRm5Lin hLC g x w = covRm5 (I := I) g x w := rfl

/-- `dRmNormSq g x` is the sum of the squares of the components of `∇Rm` over *all* tuples of
frame vectors (as produced by the Hilbert–Schmidt bound `multilinear_frame_bound`). -/
theorem dRmNormSq_eq_pi_sum (hLC : LCSmooth I M) (g : SMet I M) (x : M) :
    (∑ w : Fin 5 → Fin (Module.finrank ℝ E),
        (covRm5Lin hLC g x (fun s => onFrame g x (w s))) ^ 2) = dRmNormSq g x := by
  rw [sum_pi_fin5]
  rw [dRmNormSq]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  refine Finset.sum_congr rfl (fun b _ => ?_)
  refine Finset.sum_congr rfl (fun c _ => ?_)
  refine Finset.sum_congr rfl (fun d _ => ?_)
  refine Finset.sum_congr rfl (fun e _ => ?_)
  simp only [covRm5Lin, MultilinearMap.mk'_apply, covRm5,
    Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_zero, Matrix.cons_val]

/-- **Expansion of `∇Rm` in an orthonormal frame.** -/
theorem covRm5Lin_expand (hLC : LCSmooth I M) (g : SMet I M) (x : M)
    (m : Fin 5 → TangentSpace I x) :
    covRm5Lin hLC g x m =
      ∑ a : Fin 5 → Fin (Module.finrank ℝ E),
        (∏ p, g.inner x (onFrame g x (a p)) (m p)) *
          covRm5 (I := I) g x (fun p => onFrame g x (a p)) := by
  classical
  by_cases hn : 0 < Module.finrank ℝ E
  · -- the frame is a basis: expand every argument
    have hexp : ∀ p : Fin 5, ∑ i : Fin (Module.finrank ℝ E),
        g.inner x (onFrame g x i) (m p) • onFrame g x i = m p := fun p =>
      Work.Diff.GE.sum_inner_smul_eq_self g x hn (onFrame g x)
        (Work.Diff.GE.isONFrame_onFrame g x) (m p)
    have hm : (fun p => ∑ i : Fin (Module.finrank ℝ E),
        g.inner x (onFrame g x i) (m p) • onFrame g x i) = m := funext hexp
    have hmain : covRm5Lin hLC g x (fun p => ∑ i : Fin (Module.finrank ℝ E),
          g.inner x (onFrame g x i) (m p) • onFrame g x i)
        = ∑ a : Fin 5 → Fin (Module.finrank ℝ E),
            (∏ p, g.inner x (onFrame g x (a p)) (m p)) *
              covRm5 (I := I) g x (fun p => onFrame g x (a p)) := by
      rw [MultilinearMap.map_sum]
      refine Finset.sum_congr rfl (fun a _ => ?_)
      rw [MultilinearMap.map_smul_univ, smul_eq_mul, covRm5Lin_apply]
    conv_lhs => rw [← hm]
    exact hmain
  · -- degenerate case: the tangent space is trivial, and the sum is empty
    have hf0 : Module.finrank ℝ E = 0 := Nat.eq_zero_of_not_pos hn
    have hzero : ∀ v : TangentSpace I x, v = 0 := by
      intro v
      obtain ⟨r, hr, hrv⟩ := (Module.finrank_eq_zero_iff (R := ℝ) (M := E)).mp hf0 v
      rcases smul_eq_zero.mp hrv with h' | h'
      · exact absurd h' hr
      · exact h'
    have hm0 : m = 0 := funext (fun p => hzero (m p))
    rw [hm0]
    have hL : covRm5Lin hLC g x (0 : Fin 5 → TangentSpace I x) = 0 := by
      have h := MultilinearMap.map_update_smul (covRm5Lin hLC g x)
        (m := (0 : Fin 5 → TangentSpace I x)) (i := (0 : Fin 5)) (c := (0 : ℝ))
        (x := (0 : TangentSpace I x))
      have e1 : Function.update (0 : Fin 5 → TangentSpace I x) (0 : Fin 5)
          ((0 : ℝ) • (0 : TangentSpace I x)) = (0 : Fin 5 → TangentSpace I x) := by
        funext i; simp [Function.update_apply]
      have e2 : Function.update (0 : Fin 5 → TangentSpace I x) (0 : Fin 5)
          (0 : TangentSpace I x) = (0 : Fin 5 → TangentSpace I x) := by
        funext i; simp [Function.update_apply]
      rw [e1, e2] at h
      simpa using h
    rw [hL]
    symm
    refine Finset.sum_eq_zero (fun a _ => ?_)
    exact absurd (a 0).isLt (by simp [hf0])

/-- **Expansion of `∇Rm` in an orthonormal frame** (stated for `covRm5`). -/
theorem covRm5_expand (hLC : LCSmooth I M) (g : SMet I M) (x : M)
    (m : Fin 5 → TangentSpace I x) :
    covRm5 (I := I) g x m =
      ∑ a : Fin 5 → Fin (Module.finrank ℝ E),
        (∏ p, g.inner x (onFrame g x (a p)) (m p)) *
          covRm5 (I := I) g x (fun p => onFrame g x (a p)) := by
  show covRm5Lin hLC g x m = _
  exact covRm5Lin_expand hLC g x m

/-- `∇Rm` is continuous as a function of its five arguments.  This follows from the expansion in
the orthonormal frame: every coordinate functional `v ↦ g.inner x e v` is a continuous linear map,
and the expansion exhibits `∇Rm` as a finite sum of products of such functionals. -/
theorem covRm5_continuous (hLC : LCSmooth I M) (g : SMet I M) (x : M) :
    Continuous (fun m : Fin 5 → TangentSpace I x => covRm5 (I := I) g x m) := by
  rw [funext (fun m => covRm5_expand hLC g x m)]
  refine continuous_finsetSum _ (fun a _ => ?_)
  have hprod : Continuous (fun m : Fin 5 → TangentSpace I x =>
      ∏ p, g.inner x (onFrame g x (a p)) (m p)) :=
    continuous_finsetProd _ (fun p _ =>
      (ContinuousLinearMap.continuous (g.inner x (onFrame g x (a p)))).comp
        (continuous_apply p))
  exact hprod.mul continuous_const

/-- The classical Cauchy–Schwarz (Hilbert–Schmidt) bound for `∇Rm`: the value of `∇Rm` on arbitrary
vectors is bounded by `√|∇Rm|²` (the square root of the sum of the squares of its components in an
orthonormal frame) times the product of the `g`-norms of the arguments. -/
theorem covRm5_frobBound (hLC : LCSmooth I M) (g : SMet I M) (x : M)
    (w : Fin 5 → TangentSpace I x) :
    |covRm5 (I := I) g x w| ≤ dRmNorm (I := I) g x * argNorms (I := I) g x w := by
  classical
  letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  haveI : IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x) := inferInstance
  have hone : Orthonormal ℝ (onFrame g x) := by
    rw [orthonormal_iff_ite]
    intro i j
    rw [show Inner.inner ℝ (onFrame g x i) (onFrame g x j)
        = g.inner x (onFrame g x i) (onFrame g x j) from rfl]
    exact Work.Diff.GE.isONFrame_onFrame g x i j
  have hb := Work.Diff.EXT.multilinear_frame_bound (N := 5) (by norm_num) (covRm5Lin hLC g x)
    (onFrame g x) hone w
  have hsum : Real.sqrt (∑ w' : Fin 5 → Fin (Module.finrank ℝ (TangentSpace I x)),
        (covRm5Lin hLC g x (fun s => onFrame g x (w' s))) ^ 2) = dRmNorm (I := I) g x := by
    rw [dRmNorm]
    exact congrArg Real.sqrt (dRmNormSq_eq_pi_sum hLC g x)
  have hprod : (∏ s : Fin 5, Real.sqrt (Inner.inner ℝ (w s) (w s)))
      = argNorms (I := I) g x w := rfl
  rw [hsum, hprod] at hb
  exact hb

/-- `∇Rm` bundled as a continuous multilinear form of the five tangent vectors, with the classical
Cauchy–Schwarz (Frobenius) bound: the value of `∇Rm` on arbitrary vectors is bounded by the square
root of the sum of the squares of its components in an orthonormal frame times the product of the
`g`-norms of the arguments.  Here `dRmNorm g x = √(dRmNormSq g x)` and
`argNorms g x w = ∏ i, √(g.inner x (w i) (w i))`.

Suggested route: use `Work.Diff.GE.MovingFrame.covRm5_multilinear` (sibling file) to build the
`MultilinearMap`, prove the bound by expanding each argument in the orthonormal frame
(`Work.Diff.GE.isONFrame_onFrame`, `Work.Diff.GE.sum_inner_smul_eq_self` from
`Submission/Work/Diff/GE/curvbasic.lean`) and Cauchy–Schwarz/Bessel, and then apply
`MultilinearMap.mkContinuous` (the operator-norm bound in the fixed norm follows from
`|(g.inner x) w w| ≤ ‖g.inner x‖ * ‖w‖^2`).  The case `finrank ℝ E = 0` is degenerate
(`TangentSpace I x` is trivial) and may be split off. -/
theorem covRm5_contMultilinear_bound (hLC : LCSmooth I M) (g : SMet I M) (x : M) :
    ∃ A : ContinuousMultilinearMap ℝ (fun _ : Fin 5 => TangentSpace I x) ℝ,
      (∀ w : Fin 5 → TangentSpace I x, A w = covRm5 (I := I) g x w) ∧
      (∀ w : Fin 5 → TangentSpace I x,
        |A w| ≤ dRmNorm (I := I) g x * argNorms (I := I) g x w) := by
  refine ⟨ContinuousMultilinearMap.mk (covRm5Lin hLC g x) (covRm5_continuous hLC g x), ?_, ?_⟩
  · intro w
    rfl
  · intro w
    exact covRm5_frobBound hLC g x w

end Work.Diff.GE.MovingFrame

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle ContDiff Set VectorField CovariantDerivative Metric

/-- The same statement, exposed under the `Work.Diff.GE.MovingFrame` namespace so that it can be
referred to unqualified after `open Work.Diff.GE.MovingFrame`. -/
theorem covRm5_contMultilinear_bound
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
    (hLC : LCSmooth I M) (g : SMet I M) (x : M) :
    ∃ A : ContinuousMultilinearMap ℝ (fun _ : Fin 5 => TangentSpace I x) ℝ,
      (∀ w : Fin 5 → TangentSpace I x, A w = covRm5 (I := I) g x w) ∧
      (∀ w : Fin 5 → TangentSpace I x,
        |A w| ≤ dRmNorm (I := I) g x * argNorms (I := I) g x w) :=
  Work.Diff.GE.MovingFrame.Work.Diff.GE.MovingFrame.covRm5_contMultilinear_bound hLC g x

end Work.Diff.GE.MovingFrame
