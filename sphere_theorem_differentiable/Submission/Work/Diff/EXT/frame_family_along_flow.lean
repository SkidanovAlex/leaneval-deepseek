import Mathlib
import Submission.Work.Diff.EXT.evolKDefs
import Submission.Work.Diff.GE.uhlenbeck_defs
import Submission.Work.Diff.GE.exists_ON_frame_family_uniformBound
import Submission.Work.Diff.GE.frameFamily_at_self
import Submission.Work.Diff.T.lc_smooth
import Submission.Work.EXT.lcSmooth_noBoundary

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.EXT

/-!
# An orthonormal frame family along a Ricci flow, starting at `onFrame`, with bounded velocity

Along a Ricci flow `G` on `[0,T)`, at a point `x` and a time `t ∈ [0,T)`, there is a family
`s ↦ e s` of frames of `TₓM`, defined and `G s`-orthonormal near `t`, with

* `e t = onFrame (G t) x` (the `Classical.epsilon`-chosen `G t`-orthonormal frame),
* `s ↦ e s i` differentiable at `t` within `[0,T)`, with velocity `edot i`,
* `(G t).inner x (edot i) (edot i) ≤ K · rmNormSq (G t) x` for one *global* constant `K ≥ 0`,

for every such `G, t, x`.

This is the `hFamily` input of the verified assembly `Work.Diff.EXT.evolK_of_pieces`
(`Submission/Work/Diff/EXT/evolK_of_flow.lean`, proving `EvolK` from the componentwise estimates
`EvolCompK k`).

## Proof (wiring, not new mathematics)

The construction is the Gram–Schmidt (Uhlenbeck) frame family `Work.Diff.GE.frameFamily G t x`
with derivative `Work.Diff.GE.frameEdot G t x`, which the `GE` area has already verified up to the
initial condition `e t = onFrame (G t) x`:

* `Work.Diff.GE.uniformBound_isONFrame_frameFamily` — `e s` is `G s`-orthonormal for *every* `s`;
* `Work.Diff.GE.uniformBound_hasDerivWithinAt_frameFamily` — differentiability at `t` within `[0,T)`
  with derivative `frameEdot G t x` (the explicit Uhlenbeck derivative);
* `Work.Diff.GE.uniformBound_frameEdot_inner_le` — the velocity bound, with
  `K = 4 * (finrank ℝ E)³`;
* `Work.Diff.GE.frameFamily_at_self` — `frameFamily G t x t = onFrame (G t) x`.

`Work.Diff.GE.exists_ON_frame_family_uniformBound` is the same statement *without* the conjunct
`e t = onFrame (G t) x`; here the witnesses are produced explicitly in order to add it.
-/

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle ContDiff Set VectorField CovariantDerivative Metric

theorem frame_family_along_flow
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
    [I.Boundaryless] [T2Space M] [CompactSpace M] :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (G : ℝ → Submission.Diff.SMet I M) (T : ℝ),
      Submission.Diff.IsRicciFlow G T →
      ∀ t ∈ Set.Ico 0 T, ∀ x : M,
        ∃ (e : ℝ → Fin (Module.finrank ℝ E) → TangentSpace I x)
          (edot : Fin (Module.finrank ℝ E) → TangentSpace I x),
          (∀ i, e t i = Submission.Diff.onFrame (G t) x i) ∧
          (∀ᶠ s in nhdsWithin t (Set.Ico 0 T), Submission.Diff.IsONFrame (G s) x (e s)) ∧
          (∀ i, HasDerivWithinAt (fun s ↦ e s i) (edot i) (Set.Ico 0 T) t) ∧
          (∀ i, (G t).inner x (edot i) (edot i) ≤ K * Submission.Diff.rmNormSq (G t) x) := by
  classical
  refine ⟨4 * (Module.finrank ℝ E : ℝ) ^ 3, by positivity, ?_⟩
  intro G T hflow t ht x
  by_cases hnt : 0 < Module.finrank ℝ E
  · refine ⟨Work.Diff.GE.frameFamily G t x, Work.Diff.GE.frameEdot G t x, ?_, ?_, ?_, ?_⟩
    · intro i
      exact congrFun (Work.Diff.GE.frameFamily_at_self (I := I) (M := M) G t x) i
    · exact Filter.Eventually.of_forall fun s =>
        Work.Diff.GE.uniformBound_isONFrame_frameFamily G t s x
    · exact Work.Diff.GE.uniformBound_hasDerivWithinAt_frameFamily (G := G) (T := T)
        hflow ht x hnt
    · intro i
      exact Work.Diff.GE.uniformBound_frameEdot_inner_le
        (Work.EXT.lcSmooth_noBoundary (I := I) (M := M)) G t x i
  · have h0 : Module.finrank ℝ E = 0 := Nat.eq_zero_of_not_pos hnt
    haveI : IsEmpty (Fin (Module.finrank ℝ E)) := by rw [h0]; infer_instance
    refine ⟨fun _ _ => 0, fun _ => 0, ?_, ?_, ?_, ?_⟩
    · intro i; exact isEmptyElim i
    · exact Filter.Eventually.of_forall fun s => by intro i; exact isEmptyElim i
    · intro i; exact isEmptyElim i
    · intro i; exact isEmptyElim i

end Work.Diff.EXT
