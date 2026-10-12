import Mathlib.Algebra.Order.Archimedean.Real.Basic
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.Analysis.Clamp

/-- Clamping a real number `t` to an interval `[lo, hi]` moves it only as far as the distance
from `t` to that interval: if `t` lies within `γ/2` below the interval (`lo - t ≤ γ/2`) and within
`γ/2` above it (`t - hi ≤ γ/2`), and `0 ≤ γ`, then the clamp `max lo (min hi t)` differs from `t`
by at most `γ/2`. -/
theorem abs_clamp_sub_le {lo hi t γ : ℝ} (hlo : lo ≤ hi) (hγ : 0 ≤ γ)
    (h1 : lo - t ≤ γ / 2) (h2 : t - hi ≤ γ / 2) :
    |max lo (min hi t) - t| ≤ γ / 2 := by
  rcases le_or_gt t lo with h | h
  · -- `t` is below the interval: the clamp returns `lo`.
    have hmin : min hi t ≤ lo := le_trans (min_le_right _ _) h
    rw [max_eq_left hmin, abs_of_nonneg (by linarith)]
    linarith
  · rcases le_or_gt t hi with h' | h'
    · -- `t` is inside the interval: the clamp returns `t`.
      rw [min_eq_right h', max_eq_right h.le, sub_self, abs_zero]
      linarith
    · -- `t` is above the interval: the clamp returns `hi`.
      rw [min_eq_left h'.le, max_eq_right hlo, abs_of_nonpos (by linarith)]
      linarith

end Work.Analysis.Clamp
