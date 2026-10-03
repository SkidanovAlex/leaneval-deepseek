import Mathlib
import Submission.Work.OROneRel.tlWinCherryDefs

namespace Work.OROneRel

theorem cherry_new_letter (p q : ℕ) (hp : 1 ≤ p) (hq : 1 ≤ q) {m : ℤ}
    (hm1 : ((p : ℤ) + (q : ℤ) - 1) ≤ m) {s : ℤ} (h0 : 0 ≤ s) (hm : s ≤ m)
    {x : Fin 2 × Bool}
    (hx : coverEdge (decorAt (tlW p q) s x) ∈ winE (tlW p q) 0 (m + 1))
    (hx' : coverEdge (decorAt (tlW p q) s x) ∉ winE (tlW p q) 0 m) :
    cherryOuter p q m s ∧
      ((s = m + 1 - (q : ℤ) ∧ x = ((0 : Fin 2), true) ∧ s + linc (tlW p q) x = m + 1) ∨
        (s = m + 1 - (p : ℤ) ∧ x = ((1 : Fin 2), false) ∧
          s + linc (tlW p q) x = m + 1)) := by
  rcases x with ⟨i, b⟩
  fin_cases i <;> cases b <;>
    simp [decorAt, coverEdge, winE, tlW, linc, cherryOuter] at hx hx' ⊢ <;> omega

end Work.OROneRel
