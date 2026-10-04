import Mathlib
import Submission.Work.Diff.EXT.ConnCov.covKAExt_bound_kit
import Submission.Work.Diff.EXT.ConnCov.reactionPar

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# `covKAExt_bound` from the proved parametric reaction bound `reactionPar`

`Work.Diff.EXT.ConnCov.covKAExt_bound` (the uniform bound on the `∇^{G 0}`-tower of the lowered
connection difference `aOf` on `[T/2,T)`) is obtained here from

* the *assembly* `Work.Diff.EXT.ConnCov.V2.covKAExt_bound_of_react` — a copy, in the fresh
  namespace `V2`, of the proved grid/monotone-envelope Gronwall argument of
  `Submission.Work.Diff.EXT.ConnCov.covKAExt_bound` with the reaction bound as an explicit
  hypothesis, and
* the *parametric reaction bound* `Work.Diff.EXT.ConnCov.reactionPar`.

This bypasses the module `Submission.Work.Diff.EXT.ConnCov.dAOfTowerBoundShiPar`, whose proof still
carries a `sorry` (and which is imported, but not used, by the original `covKAExt_bound`); as a
consequence the theorem below depends only on `propext`, `Classical.choice` and `Quot.sound`.

The consumer is `Submission.Work.Diff.EXT.chartBounds_of_shibounds` (coordinate bounds on the
slab), hence the target `Work.Diff.EXT.local_ext_of_bounded_curv`.
-/

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle ContDiff Set VectorField CovariantDerivative Metric

namespace Work.Diff.EXT.ConnCov

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]

/-- **The parametric reaction bound in the shape consumed by the assembly.**  This is
`Work.Diff.EXT.ConnCov.reactionPar` re-read through the vocabulary (`levT`, `levR`, `qf`) of the
assembly: at each `t ∈ [T/2,T)` and for every valid level-`k` constant `U` of the `aOf`-tower at
that time, the level-`k` tower of the reaction `∂ₜ aOf` is bounded by
`Cd · (1 + Σ_{j<k} B j + U) · qf`, with `Cd` independent of `t` and of `U`. -/
theorem hReact_of_reactionPar
    [I.Boundaryless] [T2Space M] [CompactSpace M]
    (hLC : Submission.Diff.LCSmooth I M)
    (G : ℝ → Submission.Diff.SMet I M) (T C : ℝ) (hT : 0 < T) (hC : 0 ≤ C)
    (hflow : Submission.Diff.IsRicciFlow G T)
    (hbound : ∀ t ∈ Set.Ico 0 T, Submission.Diff.CurvBound (G t) C)
    (hmet : ∀ t ∈ Set.Ico 0 T, ∀ x : M, ∀ u : TangentSpace I x,
      (G t).inner x u u ≤ Real.exp (2 * ((Module.finrank ℝ E : ℝ) * C) * t) * (G 0).inner x u u ∧
      (G 0).inner x u u ≤ Real.exp (2 * ((Module.finrank ℝ E : ℝ) * C) * t) * (G t).inner x u u)
    (hShi : Work.Diff.EXT.ShiBounds (I := I) (M := M)) :
    ∀ (k : ℕ) (B : ℕ → ℝ), (∀ j, 0 ≤ B j) →
      (∀ j, j < k → ∀ t ∈ Set.Ico (T / 2) T,
        Work.Diff.EXT.ATower.ValBound G t j (V2.levT G j t) (B j)) →
      ∃ Cd : ℝ, 0 ≤ Cd ∧ ∀ t ∈ Set.Ico (T / 2) T, ∀ U : ℝ, 0 ≤ U →
        Work.Diff.EXT.ATower.ValBound G t k (V2.levT G k t) U →
        ∀ (x : M) (v : Fin k → TangentSpace I x) (a b c : TangentSpace I x),
          |Work.Diff.EXT.ATower.valOp (V2.levR G k t) x v a b c|
            ≤ Cd * (1 + Finset.sum (Finset.range k) B + U) * V2.qf G t x v a b c := by
  intro k B hB hA
  obtain ⟨Cd, hCd0, hCd⟩ :=
    reactionPar (I := I) (M := M) hLC G T C hT hC hflow hbound hmet hShi k B hB hA
  refine ⟨Cd, hCd0, fun t ht U hU hV x v a b c => ?_⟩
  have h := hCd t ht U hU hV x v a b c
  simpa only [V2.qf, V2.levR, V2.levT] using h

/-- **The uniform bound on the `∇^{G 0}`-tower of the lowered connection difference**, assembled
from the proved parametric reaction bound `reactionPar`.  Statement identical to
`Work.Diff.EXT.ConnCov.covKAExt_bound`, but with a proof that does not use the `sorry`-carrying
`dAOfTowerBoundShiPar`. -/
theorem covKAExt_bound_v2
    [I.Boundaryless] [T2Space M] [CompactSpace M]
    (hLC : Submission.Diff.LCSmooth I M)
    (G : ℝ → Submission.Diff.SMet I M) (T C : ℝ) (hT : 0 < T) (hC : 0 ≤ C)
    (hflow : Submission.Diff.IsRicciFlow G T)
    (hbound : ∀ t ∈ Set.Ico 0 T, Submission.Diff.CurvBound (G t) C)
    (hmet : ∀ t ∈ Set.Ico 0 T, ∀ x : M, ∀ u : TangentSpace I x,
      (G t).inner x u u ≤ Real.exp (2 * ((Module.finrank ℝ E : ℝ) * C) * t) * (G 0).inner x u u ∧
      (G 0).inner x u u ≤ Real.exp (2 * ((Module.finrank ℝ E : ℝ) * C) * t) * (G t).inner x u u)
    (hShi : Work.Diff.EXT.ShiBounds (I := I) (M := M)) :
    ∀ k : ℕ, ∃ Ck : ℝ, 0 ≤ Ck ∧ ∀ t ∈ Set.Ico (T / 2) T, ∀ x : M,
      ∀ (v : Fin k → TangentSpace I x) (a b c : TangentSpace I x),
      |Work.Diff.EXT.covKAExt G t k (fun i => Submission.Diff.smoothExt x (v i))
          (Submission.Diff.smoothExt x a) (Submission.Diff.smoothExt x b)
          (Submission.Diff.smoothExt x c) x|
        ≤ Ck * (Finset.univ.prod (fun i : Fin k => Real.sqrt ((G t).inner x (v i) (v i))))
            * Real.sqrt ((G t).inner x a a) * Real.sqrt ((G t).inner x b b)
            * Real.sqrt ((G t).inner x c c) :=
  V2.covKAExt_bound_of_react (I := I) (M := M) hLC G T C hT hC hflow hbound hmet hShi
    (hReact_of_reactionPar (I := I) (M := M) hLC G T C hT hC hflow hbound hmet hShi)

end Work.Diff.EXT.ConnCov
