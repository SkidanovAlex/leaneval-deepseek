import Mathlib
import Submission.Work.Drive.rotSideCount
import Submission.Work.Drive.transportThreeLevel
import Submission.Work.Drive.sideValue

/-!
# The multiplicativity for *every* block of the design's triple

The transport (`Work.Drive.odd_topBdryMeet_zero_iff_coreSideCount_mul`) computes the **`0`-th** top
boundary count of a triple of sweeps through two side values *in the chart of the first plane*.  The
counting route (`Work.Drive.parityCore_of_oddThreeCount`) needs, for the triple of rotated planes
`(P_u, P_v, P_w)`, the identity

> `n_P + n_Q + n_R ≡ 1` (the engine) and `n_P = ε_Q · ε_R` (multiplicativity),

where `n_P, n_Q, n_R` are the top counts of the **three blocks** of one triple.  Two reductions turn
the `0`-th block statement into the statement for the block `k`:

* `Work.Drive.odd_topBdryMeet_block_perm` — the `k`-th top count of a triple is the `0`-th top count
  of the triple with its chains cyclically permuted so that the `k`-th one comes first
  (`Work.Drive.ncard_topBdryMeet_eq_perm`, the relabelling lemma of `cutTransport.lean`);
* `Work.Drive.odd_coreSideCount_block_eq_base` (`coreSideCountRot.lean`) — the side value computed in
  the chart of the block `k` is the base-chart value at the *angle difference*.

This file puts the two together: `Work.Drive.odd_coreSideCount_mul_of_block` is the multiplicativity
for an arbitrary block, in the design's own vocabulary — one line to consume and immune to the
`Fin 3`-relabelling bookkeeping.

All declarations are `sorry`-free and rest on `propext`, `Classical.choice`, `Quot.sound`.
-/

namespace Work.Drive

open Manifold
open scoped Manifold ContDiff Topology

noncomputable section

/-- **The `k`-th top count as the `0`-th top count of a permuted triple.**  Direct `Odd`-form of
`Work.Drive.ncard_topBdryMeet_eq_perm`: for any permutation `σ` of the three chains, the top count of
the block `σ 0` is the `0`-th top count of the permuted triple. -/
theorem odd_topBdryMeet_perm {M : Type*} [TopologicalSpace M]
    (D : Fin 3 → EuclideanSpace ℝ (Fin 3) → M) (σ : Equiv.Perm (Fin 3)) :
    Odd (topBdryMeet M D (σ 0)).ncard ↔ Odd (topBdryMeet M (fun i => D (σ i)) 0).ncard := by
  rw [ncard_topBdryMeet_eq_perm D σ]

/-- **The `k`-th top count as the `0`-th top count of the cyclically shifted triple.**  The case of
`odd_topBdryMeet_perm` used by the design: the permutation `i ↦ k + i` of `Fin 3` brings the block `k`
into the `0`-th slot. -/
theorem odd_topBdryMeet_block_perm {M : Type*} [TopologicalSpace M]
    (D : Fin 3 → EuclideanSpace ℝ (Fin 3) → M) (k : Fin 3) :
    Odd (topBdryMeet M D k).ncard ↔ Odd (topBdryMeet M (fun i => D (k + i)) 0).ncard := by
  have hσ : (Equiv.ofBijective (fun i : Fin 3 => k + i) (by fin_cases k <;> decide)) 0 = k := by
    rw [Equiv.ofBijective_apply]
    fin_cases k <;> rfl
  have h := odd_topBdryMeet_perm D
    (Equiv.ofBijective (fun i : Fin 3 => k + i) (by fin_cases k <;> decide))
  rw [hσ] at h
  have hfun : (fun i : Fin 3 =>
      D ((Equiv.ofBijective (fun i : Fin 3 => k + i) (by fin_cases k <;> decide)) i))
      = fun i => D (k + i) := rfl
  rw [hfun] at h
  exact h

/-- **THE SIDE VALUE OF A BLOCK, READ IN THE BASE CHART.**  For the rotation family of plane
presentations, the side value of the block `k` computed in the chart of the block `k` is the base-chart
value at the angle difference `u j − u k`: rotate the whole configuration by `−u k`, which transports
the chart, the loop and the sweep simultaneously (`Work.Drive.coreSideCount_rotCapping`, in
`rotSideCount.lean`) and turns the presentation `rotPresentation Q (u j)` into
`rotPresentation Q (u j − u k)` (`rotPresentation_add`).  This is the exact analogue for
`coreSideCount` of `Work.Drive.diskCut_block_eq_base`. -/
theorem coreSideCount_block_eq_base (Q : ℂ → CappingSpace) (u : Fin 3 → UnitAddCircle) (c : ℝ)
    (j k : Fin 3) :
    coreSideCount (fun z : ℂ => rotCapping (u k) (Q z)) c (rotPresentation Q (u j))
      = coreSideCount Q c (rotPresentation Q (u j - u k)) := by
  have hfun : (fun y : EuclideanSpace ℝ (Fin 2) =>
        rotCapping (u k) (rotPresentation Q (u j - u k) y))
      = rotPresentation Q (u j) := by
    have h := rotPresentation_add Q (u k) (u j - u k)
    rw [show u k + (u j - u k) = u j from by abel] at h
    exact h
  rw [← hfun]
  exact (coreSideCount_rotCapping Q c (rotPresentation Q (u j - u k)) (u k)).symm

/-- The parity form of `coreSideCount_block_eq_base`. -/
theorem odd_coreSideCount_block_eq_base (Q : ℂ → CappingSpace) (u : Fin 3 → UnitAddCircle) (c : ℝ)
    (j k : Fin 3) :
    Odd (coreSideCount (fun z : ℂ => rotCapping (u k) (Q z)) c (rotPresentation Q (u j)))
      ↔ Odd (coreSideCount Q c (rotPresentation Q (u j - u k))) := by
  rw [coreSideCount_block_eq_base]

/-- **THE MULTIPLICATIVITY FOR AN ARBITRARY BLOCK.**  The `k`-th top count of the design's triple of
rotated sweeps (the chains `j ↦ clampedSweep (cblk j) (1 - ·) (rotPresentation Q (u j))`) is the
product of the two base-chart side values at the angle differences `u (k+1) − u k` and
`u (k+2) − u k`.

The hypothesis `hT6` is the output of the transport
(`Work.Drive.odd_topBdryMeet_zero_iff_coreSideCount_mul`, or its `_of_design` form with the level-face
avoidances derived) for the **chart of the block `k`** — i.e. `rotCapping (u k) ∘ Q`, whose disk plane
is `rotPresentation Q (u k)` — against the two swept planes `rotPresentation Q (u (k+1))`,
`rotPresentation Q (u (k+2))` at the levels `cblk (k+1)`, `cblk (k+2)`.  The conclusion replaces that
chart by the base chart `Q`, which is what the side function `e` of the route is defined in. -/
theorem odd_coreSideCount_mul_of_block (Q : ℂ → CappingSpace) (u : Fin 3 → UnitAddCircle)
    (cblk : Fin 3 → ℝ) (k : Fin 3)
    (hT6 : Odd (topBdryMeet CappingSpace
        (fun i => clampedSweep (cblk (k + i)) (fun t => 1 - t) (rotPresentation Q (u (k + i)))) 0).ncard ↔
      Odd (coreSideCount (fun z => rotCapping (u k) (Q z)) (cblk (k + 1))
            (rotPresentation Q (u (k + 1))))
        ∧ Odd (coreSideCount (fun z => rotCapping (u k) (Q z)) (cblk (k + 2))
            (rotPresentation Q (u (k + 2))))) :
    Odd (topBdryMeet CappingSpace
        (fun j => clampedSweep (cblk j) (fun t => 1 - t) (rotPresentation Q (u j))) k).ncard ↔
      Odd (coreSideCount Q (cblk (k + 1)) (rotPresentation Q (u (k + 1) - u k)))
        ∧ Odd (coreSideCount Q (cblk (k + 2)) (rotPresentation Q (u (k + 2) - u k))) :=
  (odd_topBdryMeet_block_perm
    (fun j => clampedSweep (cblk j) (fun t => 1 - t) (rotPresentation Q (u j))) k).trans
    (hT6.trans (and_congr (odd_coreSideCount_block_eq_base Q u (cblk (k + 1)) (k + 1) k)
      (odd_coreSideCount_block_eq_base Q u (cblk (k + 2)) (k + 2) k)))

end

end Work.Drive
