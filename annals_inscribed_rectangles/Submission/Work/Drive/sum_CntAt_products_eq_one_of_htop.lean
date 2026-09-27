import Mathlib
import Submission.Work.Drive.perturbedTripleIdentity

namespace Work.Drive

open Manifold
open scoped Manifold ContDiff Topology

attribute [local instance] Work.Drive.cappingCharted Work.Drive.isManifold_cappingCharted
  Work.Drive.t2Space_cappingSpace Work.Drive.projCharted

noncomputable section

/-- `Work.Drive.sum_CntAt_products_eq_one_of_blockT6` with the engine's output `htop` taken as a
hypothesis instead of being derived from `Meet3Hyp` + the ends clause.  This is item (E2) of the
project lead's `NOTES_LEAD_hdense.md`: the `hdense` endpoint supplies `htop` from
`Work.Drive.odd_sum_topBdryMeet_sweepChartFam`, so the transport data (`hblock`) and the algebra are
separated from the engine. -/
theorem sum_CntAt_products_eq_one_of_htop {m : ℕ}
    [ChartedSpace (EuclideanSpace ℝ (Fin 4)) Work.Drive.CappingSpace]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4)))
      ((⊤ : ℕ∞) : WithTop ℕ∞) Work.Drive.CappingSpace]
    (Ξ : EuclideanSpace ℝ (Fin m) → Work.Drive.CappingSpace → Work.Drive.CappingSpace)
    (Q : ℂ → Work.Drive.CappingSpace)
    (u : Fin 3 → UnitAddCircle) (τ : Fin 3 → EuclideanSpace ℝ (Fin m)) (cblk : Fin 3 → ℝ)
    (htop : Odd ((Work.Drive.topBdryMeet Work.Drive.CappingSpace
          (Work.Drive.designSweep Ξ Q u τ cblk) 0).ncard
        + (Work.Drive.topBdryMeet Work.Drive.CappingSpace
          (Work.Drive.designSweep Ξ Q u τ cblk) 1).ncard
        + (Work.Drive.topBdryMeet Work.Drive.CappingSpace
          (Work.Drive.designSweep Ξ Q u τ cblk) 2).ncard))
    (hblock : ∀ k : Fin 3,
      Odd ((Work.Drive.topBdryMeet Work.Drive.CappingSpace
          (Work.Drive.designSweep Ξ Q u τ cblk) k).ncard) ↔
        (Odd (Work.Drive.coreSideCount (Work.Drive.blockChart Ξ Q u τ k) (cblk (k + 1))
              (Work.Drive.blockPlane Ξ Q u τ (k + 1)))
          ∧ Odd (Work.Drive.coreSideCount (Work.Drive.blockChart Ξ Q u τ k) (cblk (k + 2))
              (Work.Drive.blockPlane Ξ Q u τ (k + 2)))))
    (hcomm : ∀ (s : EuclideanSpace ℝ (Fin m)) (w : UnitAddCircle)
      (p : Work.Drive.CappingSpace),
      Ξ s (Work.Drive.rotCapping w p) = Work.Drive.rotCapping w (Ξ s p)) :
    ((Work.Drive.CntAt Ξ Q (cblk (0 + 1)) (u (0 + 1) - u 0) (τ 0, τ 1) : ℕ) : ZMod 2)
        * ((Work.Drive.CntAt Ξ Q (cblk (0 + 2)) (u (0 + 2) - u 0) (τ 0, τ 2) : ℕ) : ZMod 2)
      + ((Work.Drive.CntAt Ξ Q (cblk (1 + 1)) (u (1 + 1) - u 1) (τ 1, τ 2) : ℕ) : ZMod 2)
        * ((Work.Drive.CntAt Ξ Q (cblk (1 + 2)) (u (1 + 2) - u 1) (τ 1, τ 0) : ℕ) : ZMod 2)
      + ((Work.Drive.CntAt Ξ Q (cblk (2 + 1)) (u (2 + 1) - u 2) (τ 2, τ 0) : ℕ) : ZMod 2)
        * ((Work.Drive.CntAt Ξ Q (cblk (2 + 2)) (u (2 + 2) - u 2) (τ 2, τ 1) : ℕ) : ZMod 2) = 1 := by
  have hsum := zmod2_sum_three_eq_one_of_odd
    (fun k : Fin 3 => (topBdryMeet CappingSpace (designSweep Ξ Q u τ cblk) k).ncard)
    (by simpa using htop)
  have hk : ∀ k : Fin 3,
      (((topBdryMeet CappingSpace (designSweep Ξ Q u τ cblk) k).ncard : ℕ) : ZMod 2)
        = ((coreSideCount (blockChart Ξ Q u τ k) (cblk (k + 1))
              (blockPlane Ξ Q u τ (k + 1)) : ℕ) : ZMod 2)
          * ((coreSideCount (blockChart Ξ Q u τ k) (cblk (k + 2))
              (blockPlane Ξ Q u τ (k + 2)) : ℕ) : ZMod 2) :=
    fun k => zmod2_natCast_eq_mul_of_odd_iff (hblock k)
  have hid : ∀ k j : Fin 3,
      ((coreSideCount (blockChart Ξ Q u τ k) (cblk j) (blockPlane Ξ Q u τ j) : ℕ) : ZMod 2)
        = ((CntAt Ξ Q (cblk j) (u j - u k) (τ k, τ j) : ℕ) : ZMod 2) := by
    intro k j
    have h := coreSideCount_block_eq_CntAt Ξ hcomm Q u τ cblk k j
    change (((coreSideCount (fun z => Ξ (τ k) (rotCapping (u k) (Q z))) (cblk j)
        (fun y => Ξ (τ j) (rotPresentation Q (u j) y)) : ℕ)) : ZMod 2)
      = ((CntAt Ξ Q (cblk j) (u j - u k) (τ k, τ j) : ℕ) : ZMod 2)
    rw [h]
  rw [hk 0, hk 1, hk 2] at hsum
  simp only [hid] at hsum
  rw [show (0 : Fin 3) + 1 = 1 from by decide, show (0 : Fin 3) + 2 = 2 from by decide,
    show (1 : Fin 3) + 1 = 2 from by decide, show (1 : Fin 3) + 2 = 0 from by decide,
    show (2 : Fin 3) + 1 = 0 from by decide, show (2 : Fin 3) + 2 = 1 from by decide] at hsum
  exact hsum

end

end Work.Drive
