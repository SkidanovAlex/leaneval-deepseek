import Mathlib
import Submission.Work.HornSC.CellBoundaryJordan.WallCycle.Defs
import Submission.Work.HornSC.CellBoundaryJordan.WallCycle.adjSeg_bridge

namespace Work.HornSC.CellBoundaryJordan.WallCycle

theorem WallAdj_adjSeg_subset_wallSet {A : Finset (ℤ × ℤ)} {u v : ℤ × ℤ}
    (h : WallAdj A u v) : adjSeg u v ⊆ wallSet A := by
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [h1, adjSeg_east]
    exact fun z hz => Or.inl (mem_hWallSet.mpr ⟨u, h2, hz⟩)
  · rw [h1, adjSeg_west]
    exact fun z hz => Or.inl (mem_hWallSet.mpr ⟨(u.1 - 1, u.2), h2, hz⟩)
  · rw [h1, adjSeg_north]
    exact fun z hz => Or.inr (mem_vWallSet.mpr ⟨u, h2, hz⟩)
  · rw [h1, adjSeg_south]
    exact fun z hz => Or.inr (mem_vWallSet.mpr ⟨(u.1, u.2 - 1), h2, hz⟩)

end Work.HornSC.CellBoundaryJordan.WallCycle
