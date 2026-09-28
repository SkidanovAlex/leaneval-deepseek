import Mathlib

namespace Work.Q44Child

theorem roots_card_le (q : Polynomial ℤ) (hq : q ≠ 0) (hdeg : q.natDegree ≤ 4) :
    q.roots.toFinset.card ≤ 4 := by
  calc q.roots.toFinset.card ≤ q.roots.card := Multiset.toFinset_card_le _
    _ ≤ q.natDegree := Polynomial.card_roots' q
    _ ≤ 4 := hdeg

end Work.Q44Child
