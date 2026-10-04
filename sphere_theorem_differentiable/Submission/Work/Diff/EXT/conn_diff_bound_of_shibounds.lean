import Mathlib
import Submission.Work.Diff.EXT.LocalExtDefs
import Submission.Work.Diff.EXT.conn_diff_bound_of_LV
import Submission.Work.Diff.EXT.curvDefs
import Submission.Work.Diff.EXT.dRmNormSq_bound_slab
import Submission.Work.Diff.T.lc_variation

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# `Work.Diff.EXT.conn_diff_bound_of_shibounds`

The connection difference `∇^{g(t)} - ∇^{g(0)}` of a Ricci flow `G` on `[0,T)` whose curvature is
bounded by `C` is bounded on `[T/2,T)` by a constant times `|u|_{g(t)} |w|_{g(t)}`.

Route.

* `Work.Diff.EXT.conn_diff_bound_of_LV` (proved, with the smooth (`C^∞`) manifold binder) gives the
  bound on the *whole* interval `[0,T)` from the a priori bound `hdRm : |∇Rm|² ≤ C₁` on `[0,T)` and
  the first-variation contract `LCVariation` (supplied by `Work.Diff.T.lc_variation hLC`).
* `hdRm` on `[0,T)` is assembled from two halves:
  - on `[T/2,T)` it is `hShi` (`ShiBounds`, at `k = 1`), transported along the identification
    `|∇^1 Rm|² = |∇Rm|²` (`curvNormK_one_eq_dRmNormSq'` below, the `k = 1` case of the `EXT`
    curvature norms, cf. `Work.Diff.EXT.curvNormK_one_eq_dRmNormSq`);
  - on `[0,T/2]` it is `Work.Diff.EXT.dRmNormSq_bound_slab` (the a priori bound near the initial
    time, from the joint smoothness of the flow up to `t = 0` and compactness of `[0,T/2] × M`).

The hypotheses `hC` and `hmet` of the statement are not needed for this argument.
-/

set_option linter.unusedVariables false

namespace Work.Diff.EXT

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle ContDiff Set VectorField CovariantDerivative Metric

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M] [T2Space M]

/-! ## The bridge `|∇^1 Rm|² = |∇Rm|²`

`Work.Diff.EXT.curvNormK` (the `EXT` vocabulary for the norms of the covariant derivatives of the
curvature) and `Submission.Diff.dRmNormSq` (the `GE` vocabulary for `|∇Rm|²`) are the same quantity
at `k = 1`.  This is `Work.Diff.EXT.curvNormK_one_eq_dRmNormSq` of
`Submission/Work/Diff/EXT/evolK_bridges.lean`; it is re-proved here with the same ingredients so that
this file need not import `evolK_bridges`, whose import closure contains
`Work.Diff.GE.frobSq5_frameIndep` (defining `Work.Diff.GE.rot5`), which clashes with
`Work.Diff.GE.norms_defs` (also defining `rot5`), pulled in by `Work.Diff.EXT.conn_diff_bound_of_LV`.
-/

/-- A sum over `Fin 1 → α` is a sum over `α`. -/
theorem sum_fin_one_arrow' {α M : Type*} [Fintype α] [AddCommMonoid M] (F : (Fin 1 → α) → M) :
    (∑ ι : Fin 1 → α, F ι) = ∑ a : α, F (fun _ => a) := by
  refine Fintype.sum_equiv (Equiv.funUnique (Fin 1) α) F (fun a => F (fun _ => a)) ?_
  intro ι
  congr 1
  funext i
  exact congrArg ι (Subsingleton.elim i default)

/-- The `k = 1` case of `covKRm` is `covRm`. -/
theorem covKRm_one' (g : Submission.Diff.SMet I M) (x : M) (v a b c d : TangentSpace I x) :
    Work.Diff.EXT.covKRm g x 1 (fun _ => v) a b c d = Submission.Diff.covRm g x v a b c d := by
  simp only [Work.Diff.EXT.covKRm, Submission.Diff.covRm, Work.Diff.EXT.covKRmExt,
    Work.Diff.GE.smoothExt_apply, Finset.univ_eq_empty, Finset.sum_empty]
  ring

/-- `|∇^1 Rm|²` is `|∇Rm|²`. -/
theorem curvNormK_one_eq_dRmNormSq' (g : Submission.Diff.SMet I M) (x : M) :
    Work.Diff.EXT.curvNormK g x 1 = Submission.Diff.dRmNormSq g x := by
  rw [Work.Diff.EXT.curvNormK_eq_sum_covKRm]
  rw [show (∑ ι : Fin 1 → Fin (Module.finrank ℝ E),
      ∑ i, ∑ j, ∑ l, ∑ m,
        (Work.Diff.EXT.covKRm g x 1 (fun s => Submission.Diff.onFrame g x (ι s))
          (Submission.Diff.onFrame g x i) (Submission.Diff.onFrame g x j)
          (Submission.Diff.onFrame g x l) (Submission.Diff.onFrame g x m)) ^ 2)
      = ∑ m, ∑ i, ∑ j, ∑ k, ∑ l,
        (Work.Diff.EXT.covKRm g x 1 (fun _ => Submission.Diff.onFrame g x m)
          (Submission.Diff.onFrame g x i) (Submission.Diff.onFrame g x j)
          (Submission.Diff.onFrame g x k) (Submission.Diff.onFrame g x l)) ^ 2 from ?_]
  · simp only [Submission.Diff.dRmNormSq, covKRm_one']
  · rw [sum_fin_one_arrow']

theorem conn_diff_bound_of_shibounds
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
    [I.Boundaryless] [T2Space M] [CompactSpace M]
    (hLC : Submission.Diff.LCSmooth I M)
    (G : ℝ → Submission.Diff.SMet I M) (T C : ℝ) (hT : 0 < T) (hC : 0 ≤ C)
    (hflow : Submission.Diff.IsRicciFlow G T)
    (hbound : ∀ t ∈ Set.Ico 0 T, Submission.Diff.CurvBound (G t) C)
    (hmet : ∀ t ∈ Set.Ico 0 T, ∀ x : M, ∀ u : TangentSpace I x,
      (G t).inner x u u ≤ Real.exp (2 * ((Module.finrank ℝ E : ℝ) * C) * t) * (G 0).inner x u u ∧
      (G 0).inner x u u ≤ Real.exp (2 * ((Module.finrank ℝ E : ℝ) * C) * t) * (G t).inner x u u)
    (hShi : Work.Diff.EXT.ShiBounds (I := I) (M := M)) :
    ∃ C' : ℝ, 0 ≤ C' ∧ ∀ t ∈ Set.Ico (T / 2) T, ∀ x : M, ∀ u w : TangentSpace I x,
      Real.sqrt ((G t).inner x
          (Submission.Diff.lcOf (G t) (Submission.Diff.smoothExt x w) x u
            - Submission.Diff.lcOf (G 0) (Submission.Diff.smoothExt x w) x u)
          (Submission.Diff.lcOf (G t) (Submission.Diff.smoothExt x w) x u
            - Submission.Diff.lcOf (G 0) (Submission.Diff.smoothExt x w) x u))
        ≤ C' * Real.sqrt ((G t).inner x u u) * Real.sqrt ((G t).inner x w w) := by
  classical
  -- the first-variation contract
  have hLV : Submission.Diff.LCVariation I M := Work.Diff.T.lc_variation hLC
  -- the a priori bound on the first half of the flow
  obtain ⟨B, hB⟩ :=
    Work.Diff.EXT.dRmNormSq_bound_slab (I := I) (M := M) hLC G T hT hflow
  have hB' : ∀ s ∈ Set.Ico 0 (T / 2), ∀ x : M,
      Submission.Diff.dRmNormSq (G s) x ≤ max B 0 := by
    intro s hs x
    exact le_trans (hB s hs x) (le_max_left B 0)
  -- the a priori bound on `[T/2,T)`, from Shi's estimate (at `k = 1`)
  obtain ⟨Ck, hCk⟩ := hShi G T C (T / 2) hT hflow hbound (by linarith) (by linarith) 1
  have hCk' : ∀ t ∈ Set.Ico (T / 2) T, ∀ x : M,
      Submission.Diff.dRmNormSq (G t) x ≤ max (max Ck B) 0 := by
    intro t ht x
    rw [← curvNormK_one_eq_dRmNormSq' (G t) x]
    exact le_trans (hCk t ht x) (le_trans (le_max_left Ck B) (le_max_left _ _))
  -- the a priori bound on all of `[0,T)`
  have hdRm : ∀ t ∈ Set.Ico 0 T, ∀ x : M,
      Submission.Diff.dRmNormSq (G t) x ≤ max (max Ck B) 0 := by
    intro t ht x
    rcases lt_or_ge t (T / 2) with hlt | hge
    · refine le_trans (hB' t ⟨ht.1, hlt⟩ x) (max_le ?_ ?_)
      · exact le_trans (le_max_right Ck B) (le_max_left _ _)
      · exact le_max_right _ _
    · exact hCk' t ⟨hge, ht.2⟩ x
  -- the connection-difference estimate on `[0,T)`
  obtain ⟨C₂, hC₂⟩ := Work.Diff.EXT.conn_diff_bound_of_LV (I := I) (M := M) G T C
    (max (max Ck B) 0) hT hLV hflow hbound hdRm
  refine ⟨max C₂ 0, le_max_right _ _, ?_⟩
  intro t ht x u w
  have htT : t ∈ Set.Ico 0 T := ⟨le_trans (by linarith : (0 : ℝ) ≤ T / 2) ht.1, ht.2⟩
  refine le_trans (hC₂ t htT x u w) ?_
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (le_max_left C₂ 0) (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _)

end Work.Diff.EXT
