import Mathlib
import Submission.Work.Diff.EXT.ConnCov.RicTr.DT.DeltaTower

set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Slot additivity of the lowered connection difference `aOf G t` (the `k = 0` base case)

`Work.Diff.EXT.ATower.SlotAdd` is the additivity predicate of the tower machinery of
`Submission/Work/Diff/EXT/ATower/Defs.lean`: an operator `τ` with `k` derivative slots and three
value slots is `SlotAdd` if it is additive in each of those `k + 3` slots **on smooth fields**
(the smoothness side conditions are essential, since `mvfderiv` is additive only on differentiable
functions).

The present file discharges the `k = 0` case for the base operator of the connection-difference
tower, `(A, B, C) ↦ aOf G t A B C`, where
`aOf G t A B C y = (G t).inner y (∇^{G t}_B A − ∇^{G 0}_B A)(y)` is the *lowered* connection
difference.  Note that the name of the file (and of the lemma) carries `_local`: it is stated with
the ambient hypotheses of the `ConnCov` area, in particular **without** `[I.Boundaryless]`, and the
three additivities are proved directly from the definition of `aOf`:

* slot `0` (the direction argument) and slot `2` (the third, "result", argument): pure linearity of
  the continuous linear maps `∇^g_B y` and `(G t).inner y` — no smoothness needed;
* slot `1` (the differentiated section): additivity of the connection difference itself,
  `Work.Diff.EXT.ConnCov.DT.covDiff_add_section` (proved in `deltaTower.lean`), transported through
  the pairing `(G t).inner y`, which only needs the sections to be differentiable at the point
  (supplied by `SmE`).
-/

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle ContDiff Set VectorField CovariantDerivative Metric

set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false

namespace Work.Diff.EXT.ConnCov.DT

open Work.Diff.EXT.ATower

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]

/-- **Additivity of `aOf` in the direction slot.**  Purely linearity of the continuous linear maps
`∇^g_B y` in their argument; no smoothness hypothesis is needed. -/
theorem aOfSlotAdd_add_dir (G : ℝ → SMet I M) (t : ℝ)
    (A A' B C : Π y : M, TangentSpace I y) :
    Work.Diff.EXT.aOf G t (A + A') B C
      = Work.Diff.EXT.aOf G t A B C + Work.Diff.EXT.aOf G t A' B C := by
  funext y
  simp only [Work.Diff.EXT.aOf, Pi.add_apply, map_add, map_sub]
  simp only [add_apply, sub_apply]
  abel

/-- **Additivity of `aOf` in the differentiated (section) slot.**

`aOf` is the pairing of the moving metric with the connection difference
`δ = covDiff G t` (`aOf G t A B C = g_t (δ B A) C`, definitionally), so additivity in `B` is
additivity of `δ` in its section slot — which for each of the two Levi-Civita connections is the
`IsCovariantDerivativeOn.add` axiom, hence needs differentiability of the two sections at the
point.  Both connections have the *same* difference (`covDiff_add_section` of `deltaTower.lean`),
which is therefore additive. -/
theorem aOfSlotAdd_add_sec (G : ℝ → SMet I M) (t : ℝ)
    (A B B' C : Π y : M, TangentSpace I y)
    (hB : SmE I M B) (hB' : SmE I M B') :
    Work.Diff.EXT.aOf G t A (B + B') C
      = Work.Diff.EXT.aOf G t A B C + Work.Diff.EXT.aOf G t A B' C := by
  funext y
  -- Definitional unfolding: `aOf G t A B C y = ⟪covDiff G t B A y, C y⟫`.
  change (G t).inner y (covDiff G t (B + B') A y) (C y)
      = (G t).inner y (covDiff G t B A y) (C y) + (G t).inner y (covDiff G t B' A y) (C y)
  rw [covDiff_add_section (I := I) (M := M) G t B B' A hB hB' y, map_add, add_apply]

/-- **Additivity of `aOf` in the third ("result") slot.**  Linearity of the metric pairing
`(G t).inner y` in its second argument; no smoothness hypothesis is needed. -/
theorem aOfSlotAdd_add_res (G : ℝ → SMet I M) (t : ℝ)
    (A B C C' : Π y : M, TangentSpace I y) :
    Work.Diff.EXT.aOf G t A B (C + C')
      = Work.Diff.EXT.aOf G t A B C + Work.Diff.EXT.aOf G t A B C' := by
  funext y
  simp only [Work.Diff.EXT.aOf, Pi.add_apply, map_add]

/-- **The `k = 0` base case of the `aOf`-tower slot additivity**, in the *local* form (the ambient
hypotheses of the `ConnCov` area, with no `I.Boundaryless`): the lowered connection difference
`aOf G t` is additive in each of its three value slots on smooth fields.

There is no derivative slot at `k = 0`, so the first conjunct of `SlotAdd` is vacuous
(`Fin 0`-elimination). -/
theorem slotAdd_aOf_local
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
    [T2Space M]
    (hLC : Submission.Diff.LCSmooth I M) (G : ℝ → Submission.Diff.SMet I M) (t : ℝ) :
    Work.Diff.EXT.ATower.SlotAdd
      (fun (_ : Fin 0 → (Π y : M, TangentSpace I y))
        (A B C : Π y : M, TangentSpace I y) (y : M) =>
          Work.Diff.EXT.aOf G t A B C y) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i
    exact i.elim0
  · intro v A A' B C _ _ _ _ _
    exact aOfSlotAdd_add_dir G t A A' B C
  · intro v A B B' C _ _ hB hB' _
    exact aOfSlotAdd_add_sec G t A B B' C hB hB'
  · intro v A B C C' _ _ _ _ _
    exact aOfSlotAdd_add_res G t A B C C'

end Work.Diff.EXT.ConnCov.DT
