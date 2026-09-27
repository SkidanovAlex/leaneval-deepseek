import Mathlib
import Submission.Work.EKLC8Core.Vol

namespace Work.EKLC8Core

/-- A set whose `vol` exceeds a positive threshold is non-empty: a set of positive
Lebesgue measure in particular has a point. -/
theorem step7_density_nonempty {T ε : ℝ} (hT : 0 < T) (hε : 0 < ε) (hε9 : 9 * ε < 1)
    {A : Set ℝ} (hA : (1 - 9 * ε) * T ≤ Work.EKLC8Core.vol (A ∩ Set.Icc 0 T)) :
    (A ∩ Set.Icc 0 T).Nonempty := by
  have hpos : 0 < (1 - 9 * ε) * T := mul_pos (by linarith) hT
  by_contra hne
  rw [Set.not_nonempty_iff_eq_empty] at hne
  rw [hne, vol_empty] at hA
  linarith

end Work.EKLC8Core
