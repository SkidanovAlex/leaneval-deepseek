import Mathlib
import Submission.Work.SG.NormalForm

namespace Work.SG

open LeanEval.Geometry.SpaceGroupsProblem

/-- **The translation lattice meets every ball in finitely many points.**

Every lattice vector `w` is the `g 0` of an element `g ∈ G` that translates by `w`, so
`‖w‖ = dist (g 0) 0`.  Hence the lattice ball of radius `r` is contained in the image of the
finite set `{g ∈ G | dist (g 0) 0 ≤ max r 1}` supplied by proper discontinuity at the origin
(`max r 1 > 0` covers negative radii as well). -/
theorem lattice_ball_finite (G : LeanEval.Geometry.SpaceGroupsProblem.CrystallographicGroup 3) (r : ℝ) :
    {w : LeanEval.Geometry.SpaceGroupsProblem.E 3 | w ∈ Work.SG.transLattice G.1 ∧ ‖w‖ ≤ r}.Finite := by
  have hR : (0 : ℝ) < max r 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hfin : {g : EuclideanIsom 3 | g ∈ G.1 ∧ dist (g 0) 0 ≤ max r 1}.Finite :=
    G.2.discrete 0 (max r 1) hR
  refine Set.Finite.subset (hfin.image (fun g => g 0)) ?_
  rintro w ⟨hwL, hwr⟩
  obtain ⟨g, hg, hgw⟩ := mem_transLattice.mp hwL
  refine ⟨g, ⟨hg, ?_⟩, ?_⟩
  · rw [show g 0 = w from by simpa using hgw 0, dist_eq_norm, sub_zero]
    exact le_trans hwr (le_max_left _ _)
  · simpa using hgw 0

end Work.SG
