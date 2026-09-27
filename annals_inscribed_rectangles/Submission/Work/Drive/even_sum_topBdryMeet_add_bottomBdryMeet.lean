import Mathlib
import Submission.Work.Drive.meet32_bordism_invariance
import Submission.Work.Drive.manifold_triple_inter_boundary_parity
import Submission.Work.Drive.manifold_triple_seam_cancel
import Submission.Work.Drive.tripleBdryMeet_ncard_split
import Submission.Work.Drive.SeamMeetDefs

namespace Work.Drive

open Manifold
open scoped Manifold ContDiff

/-!
# The boundary bookkeeping identity `Σ_k (n_{P_k} + n_{−λ,k}) ≡ 0`

`Work.Drive.manifold_triple_inter_boundary_parity` says that the *total* number of boundary triple
intersections of three transverse `3`-chains in a smooth `4`-manifold is even, and
`Work.Drive.manifold_triple_seam_cancel` says that the *seam* part of that number is even (the
antipodal involution of the parameter square pairs it up).  Since every boundary triple intersection
lies on exactly one of the three kinds of face — the seam, the top face `x 2 = 1` (the plane `P_k`
itself) or the bottom face `x 2 = 0` (the end of the sweep) — the seam part cancels from the total and
the sum of the top and bottom counts over the three blocks is even:

> `Even ((n_{P_0} + n_{−λ,0}) + (n_{P_1} + n_{−λ,1}) + (n_{P_2} + n_{−λ,2}))`.

This is the residue of the paper's parity identity after the seam faces (which are an artefact of
presenting each plane by the boundary of its parameter square) have been removed; the end contributions
are then killed by replacing the bottom faces by linear projective planes
(`Work.Drive.projective_planes_meet_oddly`), leaving `n_P + n_Q + n_R ≡ 0`.
-/

/-- **The sum of the top and bottom boundary triple counts over the three blocks is even.**  For three
`3`-chains `D 0, D 1, D 2` of a smooth `4`-manifold satisfying the packaged hypotheses `Meet3Hyp`
(smoothness, transversality of the triple, the face condition, and the seam invariance of each chain),
whose boundary triple intersections never lie on a seam *and* a sweep slice at the same time, the sum
over the three blocks of the top count (`x k 2 = 1`, i.e. the plane `P_k`) and the bottom count
(`x k 2 = 0`, i.e. the end of the sweep) is even. -/
theorem even_sum_topBdryMeet_add_bottomBdryMeet (M : Type*) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4)))
      ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    (D : Fin 3 → EuclideanSpace ℝ (Fin 3) → M) (h : Work.Drive.Meet3Hyp M D)
    (hdisj : ∀ (k : Fin 3) (x : Fin 3 → EuclideanSpace ℝ (Fin 3)),
      x ∈ Work.Drive.tripleBdryMeet M D k →
      ¬ (Work.Drive.onSeam (x k) ∧ (x k 2 = 0 ∨ x k 2 = 1))) :
    Even (((Work.Drive.topBdryMeet M D 0).ncard + (Work.Drive.bottomBdryMeet M D 0).ncard)
      + ((Work.Drive.topBdryMeet M D 1).ncard + (Work.Drive.bottomBdryMeet M D 1).ncard)
      + ((Work.Drive.topBdryMeet M D 2).ncard + (Work.Drive.bottomBdryMeet M D 2).ncard)) := by
  classical
  -- the coarse boundary parity: the three blocks are finite and their total count is even
  obtain ⟨hfin, hpar⟩ := manifold_triple_inter_boundary_parity M D h.smooth h.trans h.face
  -- the seam contributions are even
  obtain ⟨-, hseameven⟩ := manifold_triple_seam_cancel M D h.smooth h.trans h.face h.seam
  -- the split of each block into seam + top + bottom
  have hsplit : ∀ k : Fin 3, (tripleBdryMeet M D k).ncard
      = (seamBdryMeet M D k).ncard + (topBdryMeet M D k).ncard
        + (bottomBdryMeet M D k).ncard :=
    fun k => tripleBdryMeet_ncard_split M D hdisj hfin k
  -- the three seam counts add up to an even number
  have hS : Even ((seamBdryMeet M D 0).ncard + (seamBdryMeet M D 1).ncard
      + (seamBdryMeet M D 2).ncard) := by
    obtain ⟨x, hx⟩ := hseameven 0
    obtain ⟨y, hy⟩ := hseameven 1
    obtain ⟨z, hz⟩ := hseameven 2
    refine ⟨x + y + z, ?_⟩
    rw [hx, hy, hz]
    ring
  -- the total boundary count is the seam count plus the top/bottom count
  have hkey : (tripleBdryMeet M D 0).ncard + (tripleBdryMeet M D 1).ncard
      + (tripleBdryMeet M D 2).ncard
      = ((seamBdryMeet M D 0).ncard + (seamBdryMeet M D 1).ncard
          + (seamBdryMeet M D 2).ncard)
        + (((topBdryMeet M D 0).ncard + (bottomBdryMeet M D 0).ncard)
          + ((topBdryMeet M D 1).ncard + (bottomBdryMeet M D 1).ncard)
          + ((topBdryMeet M D 2).ncard + (bottomBdryMeet M D 2).ncard)) := by
    rw [hsplit 0, hsplit 1, hsplit 2]
    ring
  -- so the top/bottom count is even as well
  have hSU : Even (((seamBdryMeet M D 0).ncard + (seamBdryMeet M D 1).ncard
        + (seamBdryMeet M D 2).ncard)
      + (((topBdryMeet M D 0).ncard + (bottomBdryMeet M D 0).ncard)
        + ((topBdryMeet M D 1).ncard + (bottomBdryMeet M D 1).ncard)
        + ((topBdryMeet M D 2).ncard + (bottomBdryMeet M D 2).ncard))) :=
    hkey ▸ hpar
  exact (Nat.even_add.mp hSU).mp hS

end Work.Drive
