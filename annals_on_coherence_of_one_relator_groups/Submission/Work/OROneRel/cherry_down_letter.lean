import Mathlib
import Submission.Work.OROneRel.tlWinCherryDefs

namespace Work.OROneRel

/-- **The letter of the cherry, read downwards.**  A letter `y` whose decorated coedge at running
level `m + 1` is one of the two new edges of the window `[0,m+1]` is forced: either it is the letter
`a⁻¹` (`y = (0,false)`) leaving the new vertex `m+1` down to `m+1-q`, or it is the letter `b`
(`y = (1,true)`) leaving `m+1` down to `m+1-p`.  The other two letters of `Fin 2 × Bool` traverse a
coedge that is neither of the two new edges. -/
theorem cherry_down_letter (p q : ℕ) (hp : 1 ≤ p) (hq : 1 ≤ q) {m : ℤ} {y : Fin 2 × Bool}
    (hy : coverEdge (decorAt (tlW p q) (m + 1) y) ∈ cherryNewE p q m) :
    (y = ((0 : Fin 2), false) ∧ (m + 1) + linc (tlW p q) y = m + 1 - (q : ℤ)) ∨
      (y = ((1 : Fin 2), true) ∧ (m + 1) + linc (tlW p q) y = m + 1 - (p : ℤ)) := by
  rcases y with ⟨i, b⟩
  fin_cases i <;> cases b <;> simp [decorAt, coverEdge, cherryNewE, tlW, linc] at hy ⊢ <;> omega

end Work.OROneRel
