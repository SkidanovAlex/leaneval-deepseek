import Mathlib
import Submission.Work.HP.HP3.VeroProdExtra

namespace Work.HP.HP3

theorem cond_iff_eq_addE (d n : ℕ) (hd : 1 ≤ d) (m : Mon (d - 1) n) (j : Fin (n + 1)) (m' : Mon d n) :
    (∀ i, ((m'.1 i : ℕ) = (m.1 i : ℕ) + (if i = j then 1 else 0))) ↔ m' = addE d n hd m j := by
  constructor
  · intro h
    apply Subtype.ext
    funext i
    apply Fin.ext
    rw [addE_val]
    exact h i
  · intro h i
    rw [h, addE_val]

end Work.HP.HP3
