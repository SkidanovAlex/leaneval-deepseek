import Mathlib
import Submission.Work.Diff.EXT.LocalExtDefs
import Submission.Work.Diff.GE.curvbasic

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.EXT

open Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle ContDiff Set VectorField CovariantDerivative Metric

/-- Component bounds for a curvature array give a bound on its Frobenius square. -/
private lemma frobSq_le_of_abs_le_local {n : ℕ} (R : Curv4 n) (C : ℝ)
    (h : ∀ i j k l, |R i j k l| ≤ C) : frobSq R ≤ ((n : ℝ) ^ 2 * |C|) ^ 2 := by
  have hterm : ∀ i j k l, R i j k l ^ 2 ≤ C ^ 2 := fun i j k l =>
    sq_le_sq' (abs_le.mp (h i j k l)).1 (abs_le.mp (h i j k l)).2
  calc frobSq R = ∑ i, ∑ j, ∑ k, ∑ l, R i j k l ^ 2 := rfl
    _ ≤ ∑ i, ∑ j, ∑ k, ∑ l, C ^ 2 :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ =>
          Finset.sum_le_sum fun k _ => Finset.sum_le_sum fun l _ => hterm i j k l
    _ = ∑ _i : Fin n, ∑ _j : Fin n, ∑ _k : Fin n, ∑ _l : Fin n, |C| ^ 2 := by
        simp only [sq_abs]
    _ = ((n : ℝ) ^ 2 * |C|) ^ 2 := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring

/-- For `k = 0` the `k`-th curvature norm is the Frobenius square of the curvature; `CurvBound g C`
(componentwise bounds in orthonormal frames) therefore bounds it by `(n^2 |C|)^2`. -/
theorem curvNormK_zero_le_of_curvBound
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M] [T2Space M]
    (g : Submission.Diff.SMet I M) (x : M) (C : ℝ)
    (hb : Submission.Diff.CurvBound g C) :
    Work.Diff.EXT.curvNormK g x 0 ≤ ((Module.finrank ℝ E : ℝ) ^ 2 * |C|) ^ 2 := by
  have hframe : IsONFrame g x (onFrame g x) := Work.Diff.GE.isONFrame_onFrame g x
  have key : curvNormK g x 0 = frobSq (rmFrame g x (onFrame g x)) := by
    have hcomp : ∀ (ι : Fin 0 → Fin (Module.finrank ℝ E)) (i j l m : Fin (Module.finrank ℝ E)),
        covKRmC g x (onFrame g x) 0 ι i j l m = rmFrame g x (onFrame g x) i j l m :=
      fun ι i j l m => by
        simp only [covKRmC, covKRmExt, rmFrame, rmP, Work.Diff.GE.smoothExt_apply]
    simp only [Work.Diff.EXT.curvNormK, frobSq, hcomp]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin, one_smul,
      pow_zero]
  rw [key]
  exact frobSq_le_of_abs_le_local _ C fun i j k l => hb x (onFrame g x) hframe i j k l

end Work.Diff.EXT
