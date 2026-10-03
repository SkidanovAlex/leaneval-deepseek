import Mathlib
import Submission.Work.OROneRel.winBasisDefs
import Submission.Work.OROneRel.mk_expand
import Submission.Work.OROneRel.coedgeBase

namespace Work.OROneRel

/-- **The signed loop word of an edge of the `Z`-cover has weight zero.**  For a gauge `Wt` whose
level `i` has cohomological weight `i`, the loop word
`edgeWord Wt c e = wordOf (Wt e.2) ++ [(e.1, true)] ++ wordOf ((Wt (e.2 + c e.1))⁻¹)` of the edge
`e` telescopes in weight to `e.2 + c e.1 - (e.2 + c e.1) = 0`; the same holds for the inverted word
`edgeWordSigned Wt c e false`. -/
theorem lsig_edgeWordSigned {α : Type*} (Wt : ℤ → FreeGroup α) (c : α → ℤ) (e : α × ℤ) (b : Bool)
    (hc1 : (cohom c (Wt e.2)).toAdd = e.2)
    (hc2 : (cohom c (Wt (e.2 + c e.1))).toAdd = e.2 + c e.1) :
    lsig c (edgeWordSigned Wt c e b) = 0 := by
  -- The weight of the head word `Wt e.2`.
  have h1 : lsig c (wordOf (Wt e.2)) = e.2 := by
    rw [CoedgeBase.lsig_wordOf, hc1]
  -- The weight of the tail word `(Wt (e.2 + c e.1))⁻¹`, the negative of the target level.
  have h3 : lsig c (wordOf ((Wt (e.2 + c e.1))⁻¹)) = -(e.2 + c e.1) := by
    rw [CoedgeBase.lsig_wordOf_inv, CoedgeBase.lsig_wordOf, hc2]
  -- The unsigned loop word telescopes to `e.2 + c e.1 - (e.2 + c e.1) = 0`.
  have hEdge : lsig c (edgeWord Wt c e) = 0 := by
    rw [edgeWord, CoedgeBase.lsig_append, CoedgeBase.lsig_append, h1,
      CoedgeBase.lsig_singleton_true, h3]
    ring
  cases b
  · simp only [edgeWordSigned, cond_false, CoedgeBase.lsig_invRev, hEdge, neg_zero]
  · simp only [edgeWordSigned, cond_true, hEdge]

end Work.OROneRel
