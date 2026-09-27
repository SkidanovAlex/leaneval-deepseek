import Mathlib
import Submission.Work.Drive.refTripleOneT
import Submission.Work.Drive.planeChartDefs
import Submission.Work.Drive.chartPert_linPlaneChart
import Submission.Work.Drive.refTripleProducerDefs
import Submission.Work.Drive.hn2Clause6Sard
import Submission.Work.Drive.refTripleClause6Data
import Submission.Work.Drive.hn2RefParityDefs
import Submission.Work.Drive.refTripleGenericity_wall_posDense
import Submission.Work.Drive.refParityFamily

/-!
# The `hn2` reference-triple producer, with the disjointness hypothesis `v - u ∈ Zc γ`

This is the node `Work.Drive.hn2_refTripleAt_producer` **with the two hypotheses its clauses actually
consume**: the smooth-embedding hypothesis on `γ` (the `(F1)` mixed factors) and the collision-free
angle difference `huv : v - u ∈ Zc γ` (the whole-plane disjointness of the two configuration blocks).
Its only consumers (`Work.Drive.hn2_germ_antisym`, `Work.Drive.hn2_off_half`) instantiate it exactly at
`u = 0`, `v = a` with `a ∈ Zc γ`, so this is not a weakening; see `HN2_PRODUCER_STATE.md` §1, §2 and the
session notes in `HANDOFF.md`.

## Structure of the proof

`RefTripleAt` is the conjunction (`Work.Drive.refTripleAt_iff_genericity`)

* `RefTripleGenericity Q R u v cblk t` — the level bound, the sweeps' `Meet3Hyp`, the two coupled
  `GoodAt`s and the whole block-factor bundle `∃ g` of the transport `T6` (with the reference block's
  factors even and the two mixed factors odd), and
* `Odd (classTripleSet (fun k z => chartPert (blk k t) (refTriple Q R u v k z))).ncard` — the
  **class-parity** (`hodd`) clause: the mod-`2` degree of the triple intersection of the three class
  `2`-chains.

The first conjunct is *proved, axiom-clean, on disk* for **every** prescribed class-parity family `A`:
`Work.Drive.refTripleGenericity_wall_posDense` (the `A`-parametric Sard
`exists_refTripleGenericity_wall` of `hn2Clause6Sard.lean`, with the density hypothesis on `A` weakened
from "dense at every point of the closed unit ball" to "dense at every *positive-block* point of it" —
which is all its enriched iteration `threeBlock_dense_point` consumes, since that iteration lives in the
ball `B (t • vBlock) (t/2)` where every point has positive blocks).

The second conjunct is the output of the parallel-produced
`Work.Drive.refParityFamily` (`Drive/refParityFamily.lean`): for the level `lam` and the linear family
`φ` of the caller, an open set `A` of parameters, dense at every positive-block point of the closed unit
ball, at every point of which the perturbed reference triple has an **odd** number of class triples
(`Work.Drive.RefParityFamily`, `Drive/hn2RefParityDefs.lean`).  Since the reference plane and the level
are chosen *inside* `refTripleGenericity_wall_posDense`, the family is inserted as a function of
`(φ, lam, hlam)`.
-/

namespace Work.Drive

open Manifold Set
open scoped Manifold ContDiff Topology

attribute [local instance] Work.Drive.cappingCharted Work.Drive.isManifold_cappingCharted
  Work.Drive.t2Space_cappingSpace Work.Drive.projCharted

noncomputable section

set_option maxHeartbeats 1000000
set_option linter.unusedVariables false

theorem hn2_refTripleAt_producerHuv {γ : Circle → ℝ × ℝ} {hγne : ∀ x : Circle, γ x ≠ 0}
    (hγsmooth : Manifold.IsSmoothEmbedding (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 1)))
      (modelWithCornersSelf ℝ (ℝ × ℝ)) ((⊤ : ℕ∞) : WithTop ℕ∞) γ)
    (hγinj : Function.Injective γ) {Q : ℂ → CappingSpace} (hQ : IsPlaneChart γ hγne Q)
    (c : ℝ) (hc : 0 < c) (hcbot : ∀ p ∈ chartDisk Q, c < levelOf p)
    (hdisjZc : ∀ w : UnitAddCircle, w ∈ Zc γ →
      Disjoint (chartDisk Q) (rotCapping w '' chartDisk Q))
    (u v : UnitAddCircle) (hu : v - u ∈ Zc γ) :
    ∃ (lam : ℝ) (hlam : 0 < lam) (φ : Fin 3 → Eucl 3 ≃L[ℝ] Eucl 3),
      (∀ z : ℂ, ‖z‖ ≤ 1 → levelOf (Q z) < lam) ∧
      ∀ ε : ℝ, 0 < ε → ∃ t : EuclideanSpace ℝ (Fin 12), ‖t‖ < ε ∧
        RefTripleAt (Ξ := fun s p => chartPert s p) Q
          (diskPlane (linPlaneChart (φ 2) lam hlam)) u v (![c / 2, c / 3, c / 4] : Fin 3 → ℝ) t := by
  classical
  -- the class-parity family, as a function of the reference plane the Sard chooses
  let A : (φ : Fin 3 → Eucl 3 ≃L[ℝ] Eucl 3) → (lam : ℝ) → 0 < lam →
      Set (EuclideanSpace ℝ (Fin 12)) :=
    fun φ lam hlam =>
      if h : ∀ z : ℂ, ‖z‖ ≤ 1 → levelOf (Q z) < lam then
        (refParityFamily hQ hγsmooth c hc hcbot hdisjZc u v hu φ lam hlam h).choose
      else Set.univ
  have hAopen : ∀ (φ : Fin 3 → Eucl 3 ≃L[ℝ] Eucl 3) (lam : ℝ) (hlam : 0 < lam),
      IsOpen (A φ lam hlam) := by
    intro φ lam hlam
    by_cases h : ∀ z : ℂ, ‖z‖ ≤ 1 → levelOf (Q z) < lam
    · rw [show A φ lam hlam = (refParityFamily hQ hγsmooth c hc hcbot hdisjZc u v hu
        φ lam hlam h).choose from dif_pos h]
      exact (refParityFamily hQ hγsmooth c hc hcbot hdisjZc u v hu φ lam hlam h).choose_spec.1
    · rw [show A φ lam hlam = Set.univ from dif_neg h]
      exact isOpen_univ
  have hAdense : ∀ (φ : Fin 3 → Eucl 3 ≃L[ℝ] Eucl 3) (lam : ℝ) (hlam : 0 < lam)
      (s : EuclideanSpace ℝ (Fin 12)), ‖s‖ ≤ 1 → PosBlocks s →
      ∀ δ : ℝ, 0 < δ → ∃ t ∈ A φ lam hlam, ‖t - s‖ < δ := by
    intro φ lam hlam s hs hpos δ hδ
    by_cases h : ∀ z : ℂ, ‖z‖ ≤ 1 → levelOf (Q z) < lam
    · rw [show A φ lam hlam = (refParityFamily hQ hγsmooth c hc hcbot hdisjZc u v hu
        φ lam hlam h).choose from dif_pos h]
      exact (refParityFamily hQ hγsmooth c hc hcbot hdisjZc u v hu φ lam hlam h).choose_spec.2.1
        s hs hpos δ hδ
    · rw [show A φ lam hlam = Set.univ from dif_neg h]
      exact ⟨s, trivial, by simpa using hδ⟩
  -- the Sard of the reference triple, inside the class-parity family
  obtain ⟨β, lam, hβpos, hlam, hβlam, φ, habove, hprod⟩ :=
    refTripleGenericity_wall_posDense hQ hγsmooth c hc hcbot hdisjZc u v hu A hAopen hAdense
  refine ⟨lam, hlam, φ, habove, ?_⟩
  intro ε hε
  obtain ⟨t, ht, htA, hgen⟩ := hprod ε hε
  -- the class-parity clause at the same parameter
  have hodd : Odd (classTripleSet (fun k z => chartPert (blk k t)
      (refTriple Q (refPlanePres φ lam hlam) u v k z))).ncard := by
    rw [show A φ lam hlam = (refParityFamily hQ hγsmooth c hc hcbot hdisjZc u v hu
      φ lam hlam habove).choose from dif_pos habove] at htA
    exact (refParityFamily hQ hγsmooth c hc hcbot hdisjZc u v hu φ lam hlam
      habove).choose_spec.2.2 t htA
  exact ⟨t, ht, (refTripleAt_iff_genericity Q (refPlanePres φ lam hlam) u v
    (![c / 2, c / 3, c / 4] : Fin 3 → ℝ) t).mpr ⟨hgen, hodd⟩⟩

end

end Work.Drive
