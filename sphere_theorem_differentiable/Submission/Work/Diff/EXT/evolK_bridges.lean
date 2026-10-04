import Mathlib
import Submission.Work.Diff.EXT.evolKDefs
import Submission.Work.Diff.GE.NablaRm
import Submission.Work.Diff.EXT.covKRmExt_tensorial

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Bridges between the `∇^k Rm` vocabulary of the `EXT` area and the `k = 1` vocabulary of `GE`

`Work.Diff.EXT.covKRm g x k u a b c d` is the value of the `k`-th covariant derivative of the
curvature on `k` derivative slots and the four curvature slots, and `Work.Diff.EXT.lapCovKRm` is the
corresponding component of its *rough* Laplacian `Δ∇^k Rm` (traced in `onFrame g x`).  The GE area
works with the same objects at `k = 1` under the names `Submission.Diff.covRm` and
`Work.Diff.GE.lapCovRmAt`, and with the squared norms `Submission.Diff.rmNormSq` (`|Rm|²`) and
`Submission.Diff.dRmNormSq` (`|∇Rm|²`).

This file records the dictionary, so that the `k = 1` results of the GE area (`covRm_frame_evol_abs`,
`hasDerivWithinAt_covRm_le`, in progress) can be fed into the `k`-th order interface `EvolCompK`:

* `covKRm_one` : the `k = 1` case of `covKRm` is `covRm`;
* `curvNormK_zero_eq_rmNormSq` : `|∇^0 Rm|² = |Rm|²` (a relabelling of the two curvature-pair slots);
* `curvNormK_one_eq_dRmNormSq` : `|∇^1 Rm|² = |∇Rm|²` (the two index sets `Fin 1 → Fin n` and
  `Fin n` are identified);
* `lapCovKRm_one_eq_lapCovRmAt` : the `k = 1` case of `lapCovKRm` is `lapCovRmAt`.  (Being proved
  separately; it needs the tensoriality of the `Ext` tower, which is the *proved*
  `Work.Diff.EXT.covKRmExt_tensorial` of `Submission/Work/Diff/EXT/covKRmExt_tensorial.lean` —
  available under `[T2Space M]`, with `LCSmooth I M` from `[T2Space M]` alone via
  `Work.EXT.lcSmooth_noBoundary`.  This module imports it, so it is in scope here.)
-/

set_option linter.unusedSectionVars false

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle ContDiff Set VectorField CovariantDerivative Metric

namespace Work.Diff.EXT

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M] [T2Space M]

/-- The `k = 1` case of `covKRm` is `covRm`. -/
theorem covKRm_one (g : Submission.Diff.SMet I M) (x : M) (v a b c d : TangentSpace I x) :
    Work.Diff.EXT.covKRm g x 1 (fun _ => v) a b c d = Submission.Diff.covRm g x v a b c d := by
  simp only [Work.Diff.EXT.covKRm, Submission.Diff.covRm, Work.Diff.EXT.covKRmExt,
    Work.Diff.GE.smoothExt_apply, Finset.univ_eq_empty, Finset.sum_empty]
  ring

/-- `|∇^0 Rm|²` is `|Rm|²`. -/
theorem curvNormK_zero_eq_rmNormSq (g : Submission.Diff.SMet I M) (x : M) :
    Work.Diff.EXT.curvNormK g x 0 = Submission.Diff.rmNormSq g x := by
  simp only [Work.Diff.EXT.curvNormK, Work.Diff.EXT.covKRmC, Work.Diff.EXT.covKRmExt,
    Submission.Diff.rmNormSq, Submission.Diff.rmC, Submission.Diff.rmFrame,
    Submission.Diff.rmP, Submission.Diff.rmVec, Submission.Diff.Alg.frobSq,
    Work.Diff.GE.smoothExt_apply, Fintype.sum_unique]

/-- A sum over `Fin 1 → α` is a sum over `α`. -/
theorem sum_fin_one_arrow {α M : Type*} [Fintype α] [AddCommMonoid M] (F : (Fin 1 → α) → M) :
    (∑ ι : Fin 1 → α, F ι) = ∑ a : α, F (fun _ => a) := by
  refine Fintype.sum_equiv (Equiv.funUnique (Fin 1) α) F (fun a => F (fun _ => a)) ?_
  intro ι
  congr 1
  funext i
  exact congrArg ι (Subsingleton.elim i default)

/-- `|∇^1 Rm|²` is `|∇Rm|²`. -/
theorem curvNormK_one_eq_dRmNormSq (g : Submission.Diff.SMet I M) (x : M) :
    Work.Diff.EXT.curvNormK g x 1 = Submission.Diff.dRmNormSq g x := by
  have key : ∀ (F : (Fin 1 → Fin (Module.finrank ℝ E)) → ℝ),
      (∑ ι : Fin 1 → Fin (Module.finrank ℝ E), F ι) = ∑ m, F (fun _ => m) :=
    fun F => Work.Diff.EXT.sum_fin_one_arrow F
  simp only [Work.Diff.EXT.curvNormK, Work.Diff.EXT.covKRmC, Work.Diff.EXT.covKRmExt,
    Submission.Diff.dRmNormSq, Submission.Diff.covRm, Work.Diff.GE.smoothExt_apply,
    Finset.univ_eq_empty, Finset.sum_empty, sub_zero]
  rw [key]

end Work.Diff.EXT
