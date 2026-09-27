import Mathlib
import Submission.Work.Drive.T6GenAtDefs
import Submission.Work.Drive.goodPair_rotCapping
import Submission.Work.Drive.perturbedTripleIdentity
import Submission.Work.Drive.chartPert_rotCapping_comm

/-!
# From the design's pair goodness to the transport's `T6GenAt` bundle (the `hdense` blocks)

`Work.Drive.T6GenAt Q P₁ P₂ c₁ c₂` (`T6GenAtDefs.lean`) bundles the at-one-parameter inputs of the
transport `T6`: the core loop of `Q` meets the sweep of `P₁` in general position
(`Work.Drive.GoodLoopChain`), at every core meet the *diameter* loop of `Q` meets the sweep of `P₂` in
general position, and the cut of `Q` misses a neighbourhood of the origin.

For the germ route's design (`Work.Drive.blockChart`/`Work.Drive.blockPlane`,
`perturbedTripleIdentity.lean`) the block-`k` T6 runs with

> `Q := blockChart Ξ Q u τ k`,  `P₁ := blockPlane Ξ Q u τ (k+1)`,  `P₂ := blockPlane Ξ Q u τ (k+2)`

and its **loop** clause is nothing but the `GoodPair` clause of the design's pair goodness
`GoodAt Ξ Q (cblk (k+1)) (u (k+1) - u k) (τ k, τ (k+1))`, transported along the rotation by `-u k`
(`Work.Drive.goodPair_rotCapping`, `Work.Drive.chartPert_rotCapping_comm`).  This file records that
transfer, together with the trivial observation that `GoodPair` *is* the loop clause.
-/

namespace Work.Drive

open Manifold
open scoped Manifold ContDiff Topology

attribute [local instance] Work.Drive.cappingCharted Work.Drive.isManifold_cappingCharted
  Work.Drive.t2Space_cappingSpace Work.Drive.projCharted

noncomputable section

/-- **The loop clause of `T6GenAt` is the `GoodPair` clause** of the same pair: the core loop of `Q₁`
against the clamped sweep of the disk presentation of `Q₂`.  (`coreMeet` and `meetBox` are the same
set by definition, the sweep is the same function, and the transversality clauses agree.) -/
theorem goodLoopChain_of_goodPair {Q₁ Q₂ : ℂ → CappingSpace} {c : ℝ} (h : GoodPair Q₁ Q₂ c) :
    GoodLoopChain (coreLoop Q₁) (clampedSweep c (fun t => 1 - t) (diskPlane Q₂)) :=
  ⟨h.2.2.1, h.2.2.2.1, h.2.2.2.2⟩

/-- **The design's pair goodness is `GoodPair` of the two perturbed rotated block charts.**  From
`GoodAt Ξ Q c w (τ k, τ j)` with `w = u j - u k` — which is `GoodPair` of the perturbed chart
`Ξ (τ k) ∘ Q` against the rotated perturbed chart `rotCapping (u j - u k) ∘ Ξ (τ j) ∘ Q` — one gets
`GoodPair` of `blockChart Ξ Q u τ k` against `blockChart Ξ Q u τ j` for the level `c`, by rotating both
charts by `u k` (`goodPair_rotCapping`) and commuting the perturbation with the rotations
(`chartPert_rotCapping_comm`). -/
theorem goodPair_blockChart_of_goodAt {m : ℕ}
    (Ξ : EuclideanSpace ℝ (Fin m) → CappingSpace → CappingSpace)
    (hcomm : ∀ (s : EuclideanSpace ℝ (Fin m)) (w : UnitAddCircle) (p : CappingSpace),
      Ξ s (rotCapping w p) = rotCapping w (Ξ s p))
    (Q : ℂ → CappingSpace) (u : Fin 3 → UnitAddCircle) (τ : Fin 3 → EuclideanSpace ℝ (Fin m))
    {c : ℝ} {k j : Fin 3}
    (hg : GoodAt Ξ Q c (u j - u k) (τ k, τ j)) :
    GoodPair (blockChart Ξ Q u τ k) (blockChart Ξ Q u τ j) c := by
  change GoodPair (fun z => Ξ (τ k) (rotCapping (u k) (Q z)))
    (fun z => Ξ (τ j) (rotCapping (u j) (Q z))) c
  have hfun : (fun z => Ξ (τ j) (rotCapping (u j) (Q z)))
      = fun z => rotCapping (u k) (rotCapping (u j - u k) (Ξ (τ j) (Q z))) := by
    funext z
    calc Ξ (τ j) (rotCapping (u j) (Q z))
        = Ξ (τ j) (rotCapping (u k) (rotCapping (u j - u k) (Q z))) := by
          congr 1
          rw [← rotCapping_add_apply (u j - u k) (u k) (Q z)]
          congr 1
          abel
      _ = rotCapping (u k) (Ξ (τ j) (rotCapping (u j - u k) (Q z))) := hcomm (τ j) (u k) _
      _ = rotCapping (u k) (rotCapping (u j - u k) (Ξ (τ j) (Q z))) := by
          rw [hcomm (τ j) (u j - u k) (Q z)]
  rw [hfun]
  have hgp : GoodPair (fun z => rotCapping (u k) (Ξ (τ k) (Q z)))
      (fun z => rotCapping (u k) (rotCapping (u j - u k) (Ξ (τ j) (Q z)))) c :=
    goodPair_rotCapping (fun z => Ξ (τ k) (Q z))
      (fun z => rotCapping (u j - u k) (Ξ (τ j) (Q z))) c (u k)
      (by exact hg)
  rw [show (fun z => rotCapping (u k) (Ξ (τ k) (Q z)))
      = (fun z => Ξ (τ k) (rotCapping (u k) (Q z))) from by
    funext z; exact (hcomm (τ k) (u k) (Q z)).symm] at hgp
  exact hgp


/-- **`blockPlane` is the disk presentation of `blockChart`**: `blockPlane Ξ Q u τ j y` is
`Ξ (τ j)` applied to the disk point of the rotated chart, which is `diskPlane (blockChart Ξ Q u τ j) y`
by unfolding `rotPresentation` and `diskPlane`. -/
theorem blockPlane_eq_diskPlane_blockChart {m : ℕ}
    (Ξ : EuclideanSpace ℝ (Fin m) → CappingSpace → CappingSpace)
    (Q : ℂ → CappingSpace) (u : Fin 3 → UnitAddCircle) (τ : Fin 3 → EuclideanSpace ℝ (Fin m))
    (j : Fin 3) : blockPlane Ξ Q u τ j = diskPlane (blockChart Ξ Q u τ j) := rfl

/-- **The finiteness and the base-point conditions of the transport `T6` at the design's block `k`**,
from the design's pair goodness alone: `GoodPair (blockChart k) (blockChart (k+1)) (cblk (k+1))`
(`goodPair_blockChart_of_goodAt`) gives the finiteness of the core meet set and the interiority of its
parameters, and an interior meet with loop parameter `1` is excluded. -/
theorem design_hfin_hbase {m : ℕ}
    (Ξ : EuclideanSpace ℝ (Fin m) → CappingSpace → CappingSpace)
    (hcomm : ∀ (s : EuclideanSpace ℝ (Fin m)) (w : UnitAddCircle) (p : CappingSpace),
      Ξ s (rotCapping w p) = rotCapping w (Ξ s p))
    (Q : ℂ → CappingSpace) (u : Fin 3 → UnitAddCircle) (τ : Fin 3 → EuclideanSpace ℝ (Fin m))
    (cblk : Fin 3 → ℝ) (k : Fin 3)
    (hg : GoodAt Ξ Q (cblk (k + 1)) (u (k + 1) - u k) (τ k, τ (k + 1))) :
    (coreMeet (blockChart Ξ Q u τ k) (cblk (k + 1)) (blockPlane Ξ Q u τ (k + 1))).Finite ∧
      (∀ y ∈ Submission.Drive.unitBox 2,
        coreLoop (blockChart Ξ Q u τ k) 1
          ≠ clampedSweep (cblk (k + 1)) (fun t => 1 - t) (blockPlane Ξ Q u τ (k + 1)) y) := by
  have hgp := goodPair_blockChart_of_goodAt Ξ hcomm Q u τ hg
  obtain ⟨hf, hint, -⟩ := goodLoopChain_of_goodPair hgp
  refine ⟨?_, ?_⟩
  · rw [blockPlane_eq_diskPlane_blockChart]
    exact hf
  · intro y hy heq
    have hmem : (1, y) ∈ coreMeet (blockChart Ξ Q u τ k) (cblk (k + 1))
        (blockPlane Ξ Q u τ (k + 1)) :=
      ⟨Set.right_mem_Icc.mpr zero_le_one, hy, heq⟩
    rw [blockPlane_eq_diskPlane_blockChart] at hmem
    have := hint (1, y) hmem
    exact absurd this.1.2 (lt_irrefl (1 : ℝ))


/-- **The first conjunct of `T6GenAt` for the design's block `k`**: the core loop of the perturbed
rotated chart `blockChart k` meets the clamped sweep of `blockPlane (k+1)` in general position — the
loop clause of `GoodPair (blockChart k) (blockChart (k+1)) (cblk (k+1))`, which the design's pair
goodness provides. -/
theorem goodLoopChain_design_block {m : ℕ}
    (Ξ : EuclideanSpace ℝ (Fin m) → CappingSpace → CappingSpace)
    (hcomm : ∀ (s : EuclideanSpace ℝ (Fin m)) (w : UnitAddCircle) (p : CappingSpace),
      Ξ s (rotCapping w p) = rotCapping w (Ξ s p))
    (Q : ℂ → CappingSpace) (u : Fin 3 → UnitAddCircle) (τ : Fin 3 → EuclideanSpace ℝ (Fin m))
    (cblk : Fin 3 → ℝ) (k : Fin 3)
    (hg : GoodAt Ξ Q (cblk (k + 1)) (u (k + 1) - u k) (τ k, τ (k + 1))) :
    GoodLoopChain (coreLoop (blockChart Ξ Q u τ k))
      (clampedSweep (cblk (k + 1)) (fun t => 1 - t) (blockPlane Ξ Q u τ (k + 1))) := by
  have h := goodLoopChain_of_goodPair (goodPair_blockChart_of_goodAt Ξ hcomm Q u τ hg)
  -- `blockPlane Ξ Q u τ j` is `diskPlane (blockChart Ξ Q u τ j)` by `rfl`
  exact h

end
end Work.Drive


