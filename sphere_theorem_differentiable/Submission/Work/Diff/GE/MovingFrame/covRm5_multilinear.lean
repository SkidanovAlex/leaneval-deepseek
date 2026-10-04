import Mathlib
import Submission.Work.Diff.GE.MovingFrame.Defs
import Submission.Work.Diff.GE.cov2RmExt_prelim
import Submission.Work.Diff.GE.Kato3.CovRmKit

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.GE.MovingFrame

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle ContDiff Set VectorField CovariantDerivative Metric

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]

/-! ## `covRm` is two-term linear in each of its five arguments

The frozen `covRm g x v a b c d` is the `(0,5)`-tensor `∇Rm` evaluated on five tangent vectors, so it
is `ℝ`-linear in each of them.  The five two-term statements are already in the workspace:

* first argument `v` (the direction): `Work.Diff.GE.covRm_linear_fst`
  (`Submission/Work/Diff/GE/cov2RmExt_prelim.lean`);
* second argument `a`: `Work.Diff.GE.covRm_linear_snd`
  (`Submission/Work/Diff/GE/dRmPhi_slotA.lean`);
* third argument `b`: `Work.Diff.GE.covRm_linear_thd`;
* fourth argument `c`: `Work.Diff.GE.covRm_linear_fth`;
* fifth argument `d`: `Work.Diff.GE.Kato3.covRm_linear_fith`
  (via the skew-symmetry in the last two arguments).

The `IsMulti5` predicate is expressed with `Function.update` on `Fin 5 → TangentSpace I x`; its two
clauses are the additivity and the homogeneity in each slot, which follow from the five lemmas above
with `(r,s) = (1,1)` resp. `(r,s) = (c,0)`. -/

/-- Additivity of `covRm5` in the slot `0` (the direction `v`). -/
private lemma covRm5_add_zero (hLC : LCSmooth I M) (g : SMet I M) (x : M)
    (w : Fin 5 → TangentSpace I x) (a b : TangentSpace I x) :
    covRm5 (I := I) g x (Function.update w 0 (a + b))
      = covRm5 (I := I) g x (Function.update w 0 a)
        + covRm5 (I := I) g x (Function.update w 0 b) := by
  simp only [covRm5]
  simpa using covRm_linear_fst hLC g x 1 1 a b (w 1) (w 2) (w 3) (w 4)

/-- Additivity of `covRm5` in the slot `1` (the argument `a`). -/
private lemma covRm5_add_one (hLC : LCSmooth I M) (g : SMet I M) (x : M)
    (w : Fin 5 → TangentSpace I x) (a b : TangentSpace I x) :
    covRm5 (I := I) g x (Function.update w 1 (a + b))
      = covRm5 (I := I) g x (Function.update w 1 a)
        + covRm5 (I := I) g x (Function.update w 1 b) := by
  simp only [covRm5]
  simpa using covRm_linear_snd hLC g x (w 0) 1 1 a b (w 2) (w 3) (w 4)

/-- Additivity of `covRm5` in the slot `2` (the argument `b`). -/
private lemma covRm5_add_two (hLC : LCSmooth I M) (g : SMet I M) (x : M)
    (w : Fin 5 → TangentSpace I x) (a b : TangentSpace I x) :
    covRm5 (I := I) g x (Function.update w 2 (a + b))
      = covRm5 (I := I) g x (Function.update w 2 a)
        + covRm5 (I := I) g x (Function.update w 2 b) := by
  simp only [covRm5]
  simpa using covRm_linear_thd hLC g x (w 0) (w 1) 1 1 a b (w 3) (w 4)

/-- Additivity of `covRm5` in the slot `3` (the argument `c`). -/
private lemma covRm5_add_three (hLC : LCSmooth I M) (g : SMet I M) (x : M)
    (w : Fin 5 → TangentSpace I x) (a b : TangentSpace I x) :
    covRm5 (I := I) g x (Function.update w 3 (a + b))
      = covRm5 (I := I) g x (Function.update w 3 a)
        + covRm5 (I := I) g x (Function.update w 3 b) := by
  simp only [covRm5]
  simpa using covRm_linear_fth hLC g x (w 0) (w 1) (w 2) 1 1 a b (w 4)

/-- Additivity of `covRm5` in the slot `4` (the argument `d`). -/
private lemma covRm5_add_four (hLC : LCSmooth I M) (g : SMet I M) (x : M)
    (w : Fin 5 → TangentSpace I x) (a b : TangentSpace I x) :
    covRm5 (I := I) g x (Function.update w 4 (a + b))
      = covRm5 (I := I) g x (Function.update w 4 a)
        + covRm5 (I := I) g x (Function.update w 4 b) := by
  simp only [covRm5]
  simpa using Work.Diff.GE.Kato3.covRm_linear_fith hLC g x (w 0) (w 1) (w 2) (w 3) 1 1 a b

/-- Homogeneity of `covRm5` in the slot `0` (the direction `v`). -/
private lemma covRm5_smul_zero (hLC : LCSmooth I M) (g : SMet I M) (x : M)
    (w : Fin 5 → TangentSpace I x) (c : ℝ) (a : TangentSpace I x) :
    covRm5 (I := I) g x (Function.update w 0 (c • a))
      = c * covRm5 (I := I) g x (Function.update w 0 a) := by
  simp only [covRm5]
  simpa using covRm_linear_fst hLC g x c 0 a a (w 1) (w 2) (w 3) (w 4)

/-- Homogeneity of `covRm5` in the slot `1` (the argument `a`). -/
private lemma covRm5_smul_one (hLC : LCSmooth I M) (g : SMet I M) (x : M)
    (w : Fin 5 → TangentSpace I x) (c : ℝ) (a : TangentSpace I x) :
    covRm5 (I := I) g x (Function.update w 1 (c • a))
      = c * covRm5 (I := I) g x (Function.update w 1 a) := by
  simp only [covRm5]
  simpa using covRm_linear_snd hLC g x (w 0) c 0 a a (w 2) (w 3) (w 4)

/-- Homogeneity of `covRm5` in the slot `2` (the argument `b`). -/
private lemma covRm5_smul_two (hLC : LCSmooth I M) (g : SMet I M) (x : M)
    (w : Fin 5 → TangentSpace I x) (c : ℝ) (a : TangentSpace I x) :
    covRm5 (I := I) g x (Function.update w 2 (c • a))
      = c * covRm5 (I := I) g x (Function.update w 2 a) := by
  simp only [covRm5]
  simpa using covRm_linear_thd hLC g x (w 0) (w 1) c 0 a a (w 3) (w 4)

/-- Homogeneity of `covRm5` in the slot `3` (the argument `c`). -/
private lemma covRm5_smul_three (hLC : LCSmooth I M) (g : SMet I M) (x : M)
    (w : Fin 5 → TangentSpace I x) (c : ℝ) (a : TangentSpace I x) :
    covRm5 (I := I) g x (Function.update w 3 (c • a))
      = c * covRm5 (I := I) g x (Function.update w 3 a) := by
  simp only [covRm5]
  simpa using covRm_linear_fth hLC g x (w 0) (w 1) (w 2) c 0 a a (w 4)

/-- Homogeneity of `covRm5` in the slot `4` (the argument `d`). -/
private lemma covRm5_smul_four (hLC : LCSmooth I M) (g : SMet I M) (x : M)
    (w : Fin 5 → TangentSpace I x) (c : ℝ) (a : TangentSpace I x) :
    covRm5 (I := I) g x (Function.update w 4 (c • a))
      = c * covRm5 (I := I) g x (Function.update w 4 a) := by
  simp only [covRm5]
  simpa using Work.Diff.GE.Kato3.covRm_linear_fith hLC g x (w 0) (w 1) (w 2) (w 3) c 0 a a

/-- `∇Rm` is a five-fold multilinear form of its five vector arguments
(`covRm5 g x w = covRm g x (w 0) (w 1) (w 2) (w 3) (w 4)`).  This is what makes the product rule
for the components of `∇Rm` in a moving frame work.

Suggested route: `covRm` is `dRmPhi` on the `Classical.epsilon`-chosen extensions
(`Work.Diff.GE.covRm_eq_dRmPhi`), and the available partial results
(`Submission/Work/Diff/GE/dRmPhi_slotA.lean`: `dRmPhi_linear_fst`, `dRmPhi_smul_fst`,
`dRmPhi_add_fst`, `dRmPhi_germ_fst`, `dRmPhi_sum_fst`; `Submission/Work/Diff/GE/covRm_linear.lean`,
`covRm_linear_thd.lean`) reduce each slot to the same computation; alternatively translate the
`rmP_add_*`/`rmP_smul_*` lemmas of `Work.Diff.GE.NablaRm` across the `smoothExt` extensions. -/
theorem covRm5_multilinear (hLC : LCSmooth I M) (g : SMet I M) (x : M) :
    IsMulti5 (TangentSpace I x) (covRm5 (I := I) g x) := by
  constructor
  · intro w i a b
    fin_cases i
    · exact covRm5_add_zero hLC g x w a b
    · exact covRm5_add_one hLC g x w a b
    · exact covRm5_add_two hLC g x w a b
    · exact covRm5_add_three hLC g x w a b
    · exact covRm5_add_four hLC g x w a b
  · intro w i c a
    fin_cases i
    · exact covRm5_smul_zero hLC g x w c a
    · exact covRm5_smul_one hLC g x w c a
    · exact covRm5_smul_two hLC g x w c a
    · exact covRm5_smul_three hLC g x w c a
    · exact covRm5_smul_four hLC g x w c a

end Work.Diff.GE.MovingFrame
