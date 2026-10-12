import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseB6.Scaled
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseB6Est

theorem fsTau_ge_half {εT c1 c2 r : ℝ} (hε0 : 0 ≤ εT) (hε1 : εT ≤ 1) (hc1 : 0 ≤ c1) (hc12 : c1 ≤ c2)
    (hcc : c1 + εT * c2 ≤ 1) (hr : 4 ≤ r) :
    r ^ 2 / 2 ≤ Work.BoseB6.fsTau εT c1 c2 r := by
  -- For `r ≥ 4` the parameter constraint `c₁ + ε_T c₂ ≤ 1` forces `c₁ ≤ 1 ≤ r`, so
  -- both truncations in `τ̃ = (1−ε_T)[|r|−c₁]₊² + ε_T[|r|−c₂]₊²` are evaluated at `r`.
  have hr0 : 0 ≤ r := by linarith
  have htabs : |r| = r := abs_of_nonneg hr0
  have hc2 : 0 ≤ c2 := le_trans hc1 hc12
  have hc1le : c1 ≤ 1 := by nlinarith [mul_nonneg hε0 hc2]
  have h1mε : 0 ≤ 1 - εT := by linarith
  -- the two truncations
  set X := max (|r| - c1) 0 with hX
  set Y := max (|r| - c2) 0 with hY
  have hXr : X = r - c1 := by
    rw [hX, htabs]; exact max_eq_left (by linarith)
  have hYge : r - c2 ≤ Y := by
    rw [hY, htabs]; exact le_max_left _ _
  -- convexity: `(1−ε_T)X² + ε_T Y² ≥ ((1−ε_T)X + ε_T Y)²` (variance `= ε_T(1−ε_T)(X−Y)²`)
  have hvar : ((1 - εT) * X + εT * Y) ^ 2 ≤ (1 - εT) * X ^ 2 + εT * Y ^ 2 := by
    have hz : 0 ≤ εT * (1 - εT) * (X - Y) ^ 2 :=
      mul_nonneg (mul_nonneg hε0 h1mε) (sq_nonneg _)
    nlinarith [hz]
  -- the convex combination dominates `r − 1` since `(1−ε_T)c₁ + ε_T c₂ ≤ c₁ + ε_T c₂ ≤ 1`
  have hlin : r - 1 ≤ (1 - εT) * X + εT * Y := by
    have hm : (1 - εT) * c1 + εT * c2 ≤ 1 := by
      have heq : (1 - εT) * c1 + εT * c2 = c1 + εT * (c2 - c1) := by ring
      rw [heq]
      nlinarith [mul_nonneg hε0 (by linarith : 0 ≤ c2 - c1)]
    rw [hXr]
    nlinarith [mul_nonneg hε0 (by linarith : 0 ≤ Y - (r - c2))]
  have hsq : (r - 1) ^ 2 ≤ ((1 - εT) * X + εT * Y) ^ 2 := by
    have hab : 0 ≤ r - 1 := by linarith
    nlinarith [mul_nonneg (by linarith : 0 ≤ (1 - εT) * X + εT * Y - (r - 1))
      (by linarith : 0 ≤ (1 - εT) * X + εT * Y + (r - 1))]
  have hr2 : r ^ 2 / 2 ≤ (r - 1) ^ 2 := by nlinarith
  rw [Work.BoseB6.fsTau, ← hX, ← hY]
  linarith [hvar, hsq, hr2]

end Work.BoseB6Est
