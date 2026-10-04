import Mathlib
import Submission.Work.Diff.EXT.curvNormK_jointSmooth
import Submission.Work.Diff.EXT.curvDefs
import Submission.Work.Diff.GE.curvbasic

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# `Work.Diff.EXT.dRmNormSq_bound_slab`

A priori bound on `|∇Rm|²` near the initial time, along a Ricci flow `G` on `[0,T)` with `M`
compact: `∃ B, ∀ s ∈ [0,T/2), ∀ x, dRmNormSq (G s) x ≤ B`.

## Route

`dRmNormSq (G s) x` is the `k = 1` case of the geometric curvature norm `curvNormK (G s) x 1`
(proved by unfolding both definitions: `curvNormK` sums over the `k`-fold index `Fin 1 → Fin n`,
which collapses to `Fin n`).  The `NormSmoothK` interface, proved in
`Submission/Work/Diff/EXT/curvNormK_jointSmooth.lean` (`Work.Diff.EXT.curvNormK_jointSmooth`), says
that `(t,x) ↦ curvNormK (G t) x k` is `C^∞` on the half-open slab `[0,T) × M`; the flow is
available there because `IsRicciFlow G T` supplies joint smoothness on `Ico 0 T`.  Composing with
the identification and restricting to the *compact* set `[0,T/2] × M ⊆ [0,T) × M` gives the bound
(`IsCompact.exists_bound_of_continuousOn`).
-/

set_option linter.unusedSectionVars false

namespace Work.Diff.EXT

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle ContDiff Set VectorField CovariantDerivative Metric

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M] [T2Space M]

/-- A sum over `Fin 1 → α` is a sum over `α`. -/
theorem dRmSlab_sum_fin_one_arrow {α N : Type*} [Fintype α] [AddCommMonoid N]
    (F : (Fin 1 → α) → N) :
    (∑ ι : Fin 1 → α, F ι) = ∑ a : α, F (fun _ => a) := by
  refine Fintype.sum_equiv (Equiv.funUnique (Fin 1) α) F (fun a => F (fun _ => a)) ?_
  intro ι
  congr 1
  funext i
  exact congrArg ι (Subsingleton.elim i default)

/-- The `k = 1` case of `covKRm` is `covRm`. -/
theorem dRmSlab_covKRm_one (g : Submission.Diff.SMet I M) (x : M)
    (v a b c d : TangentSpace I x) :
    Work.Diff.EXT.covKRm g x 1 (fun _ => v) a b c d = Submission.Diff.covRm g x v a b c d := by
  simp only [Work.Diff.EXT.covKRm, Submission.Diff.covRm, Work.Diff.EXT.covKRmExt,
    Work.Diff.GE.smoothExt_apply, Finset.univ_eq_empty, Finset.sum_empty]
  ring

/-- `|∇^1 Rm|²` is `|∇Rm|²`. -/
theorem curvNormK_one_eq_dRmNormSq_slab (g : Submission.Diff.SMet I M) (x : M) :
    Work.Diff.EXT.curvNormK g x 1 = Submission.Diff.dRmNormSq g x := by
  rw [Work.Diff.EXT.curvNormK_eq_sum_covKRm]
  rw [show (∑ ι : Fin 1 → Fin (Module.finrank ℝ E), ∑ i, ∑ j, ∑ l, ∑ m,
        (Work.Diff.EXT.covKRm g x 1 (fun s => Submission.Diff.onFrame g x (ι s))
          (Submission.Diff.onFrame g x i) (Submission.Diff.onFrame g x j)
          (Submission.Diff.onFrame g x l) (Submission.Diff.onFrame g x m)) ^ 2)
      = ∑ m, ∑ i, ∑ j, ∑ k, ∑ l,
        (Work.Diff.EXT.covKRm g x 1 (fun _ => Submission.Diff.onFrame g x m)
          (Submission.Diff.onFrame g x i) (Submission.Diff.onFrame g x j)
          (Submission.Diff.onFrame g x k) (Submission.Diff.onFrame g x l)) ^ 2 from ?_]
  · simp only [Submission.Diff.dRmNormSq, dRmSlab_covKRm_one]
  · rw [dRmSlab_sum_fin_one_arrow]

/-- **A priori bound on `|∇Rm|²` near the initial time.** -/
theorem dRmNormSq_bound_slab
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
    [I.Boundaryless] [T2Space M] [CompactSpace M]
    (hLC : Submission.Diff.LCSmooth I M)
    (G : ℝ → Submission.Diff.SMet I M) (T : ℝ) (hT : 0 < T)
    (hflow : Submission.Diff.IsRicciFlow G T) :
    ∃ B : ℝ, ∀ s ∈ Set.Ico 0 (T / 2), ∀ x : M, Submission.Diff.dRmNormSq (G s) x ≤ B := by
  have hsm := Work.Diff.EXT.curvNormK_jointSmooth (I := I) (M := M) hLC G T hflow 1
  have hcont : ContinuousOn (fun p : ℝ × M => Work.Diff.EXT.curvNormK (G p.1) p.2 1)
      (Set.Icc 0 (T / 2) ×ˢ (Set.univ : Set M)) :=
    hsm.continuousOn.mono fun p hp =>
      ⟨⟨hp.1.1, lt_of_le_of_lt hp.1.2 (by linarith [hT])⟩, hp.2⟩
  obtain ⟨B, hB⟩ := (isCompact_Icc.prod isCompact_univ).exists_bound_of_continuousOn hcont
  refine ⟨max B 0, fun s hs x => ?_⟩
  have hs' : (s, x) ∈ Set.Icc 0 (T / 2) ×ˢ (Set.univ : Set M) :=
    ⟨⟨hs.1, le_of_lt hs.2⟩, mem_univ x⟩
  have h1 : Work.Diff.EXT.curvNormK (G s) x 1 ≤ B := by
    simpa only [Real.norm_eq_abs] using le_trans (le_abs_self _) (hB (s, x) hs')
  rw [← curvNormK_one_eq_dRmNormSq_slab (I := I) (M := M) (G s) x]
  exact le_trans h1 (le_max_left _ _)

end Work.Diff.EXT
