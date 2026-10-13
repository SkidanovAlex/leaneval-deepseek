import Mathlib
import Submission.Work.WilE9.Sharp.EffInput
import Submission.Work.WilE7.Defs

namespace Work.WilE9G.Assembly

theorem stratProj_takeZ {n m m' : ℕ} (hm : n + (1 + m) ≤ n + (1 + m'))
    (w : Fin (n + (1 + m')) → ℝ) :
    Work.WilE9.Sharp.stratProj (m := m) (Work.WilE7.takeZ hm w)
      = Work.WilE9.Sharp.stratProj (m := m') w := by
  funext i
  -- Both sides are `w ⟨i.val, _⟩`: `stratProj` reads the `i`-th coordinate, and both
  -- `takeZ ... (stratInj (castAdd m i))` and `stratInj (castAdd m' i)` have value `i.val`.
  simp only [Work.WilE9.Sharp.stratProj, Work.WilE9.Sharp.stratInj, Work.WilE7.takeZ]
  congr 1

end Work.WilE9G.Assembly
