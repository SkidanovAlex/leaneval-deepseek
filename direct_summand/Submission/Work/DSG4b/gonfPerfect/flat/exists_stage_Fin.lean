import Mathlib
import Submission.Work.DSG4b.gonfPerfect.Basic

namespace Work.DSG4b.gonfPerfect.flat

/-- Every element of the colimit `D.S` lies in the image of some stage `D.AN N`; a finite tuple of
elements of `D.S` therefore lies in the image of a single (common) stage. -/
theorem exists_stage_Fin (R : Type*) [CommRing R] [IsLocalRing R] (p : ℕ) [Fact p.Prime] [CharP (IsLocalRing.ResidueField R) p] (D : PData R p) (l : ℕ) (x : Fin l → D.S) : ∃ N, ∃ x' : Fin l → D.AN N, ∀ i, D.incl N (x' i) = x i := by
  choose N y hy using fun i => Ring.DirectLimit.exists_of (x i)
  refine ⟨Finset.univ.sup N,
    fun i => D.trans (N i) (Finset.univ.sup N) (Finset.le_sup (Finset.mem_univ i)) (y i), ?_⟩
  intro i
  rw [D.incl_trans, hy i]

end Work.DSG4b.gonfPerfect.flat
