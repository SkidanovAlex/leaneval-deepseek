import Mathlib
import Submission.Work.ORDunwoody.Dunwoody.FaceWalk

namespace Work.ORDunwoody

universe u

/-- The reversed word with every letter swapped represents the inverse free-group element. -/
theorem mk_reverse_map_swapLetter {n : ℕ} (w : List (Fin n × Bool)) :
    FreeGroup.mk (w.reverse.map Cayley.swapLetter) = (FreeGroup.mk w)⁻¹ := by
  rw [FreeGroup.inv_mk]
  congr 1
  unfold FreeGroup.invRev Cayley.swapLetter
  simp [List.map_reverse]

theorem A_endPt_rev {G : Type u} [Group G] {P : Work.ORDunwoody.FinPresentation G}
    (a : G) (w : List (Fin P.n × Bool)) :
    Work.ORDunwoody.Dunwoody.endPt P (Work.ORDunwoody.Dunwoody.endPt P a w)
      (w.reverse.map Work.ORDunwoody.Cayley.swapLetter) = a := by
  rw [Work.ORDunwoody.Dunwoody.endPt_eq_mul, Work.ORDunwoody.Dunwoody.endPt_eq_mul,
    mk_reverse_map_swapLetter, map_inv]
  group

end Work.ORDunwoody
