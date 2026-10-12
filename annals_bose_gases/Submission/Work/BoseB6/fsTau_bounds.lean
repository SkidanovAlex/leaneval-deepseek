import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseB6.Scaled
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Node B6 — the elementary bounds on FS's `τ̃` (`eq:tautilde-Est`)

`fsTau εT c1 c2 t = (1−εT)[t−c₁]₊² + εT[t−c₂]₊²` (`Scaled.lean`), with `0 ≤ c₁ ≤ c₂`.

Write `a = [t−c₁]₊`, `b = [t−c₂]₊` (so `0 ≤ b ≤ a ≤ t` for `t ≥ 0`).  Then

* `0 ≤ fsTau ≤ t²` (both truncations lie in `[0,t]`);
* `t² − fsTau = (t² − a²) + εT(a² − b²) ≤ εT t² + 2c₁t`
  (as `t² − a² ≤ 2c₁t` — with equality `2c₁t − c₁²` for `t ≥ c₁` — and `a² − b² ≤ a² ≤ t²`);
* for `t ≥ 4c₂` one has `b ≥ 3t/4`, whence `fsTau ≥ b² ≥ 9t²/16 ≥ t²/2`;
* for `t ≥ 4c₂`: `t² − fsTau ≤ 2c₁t + 2εT c₂t ≤ 8(c₁ + εT c₂)t`
  (using `a² − b² = (c₂−c₁)(2t−c₁−c₂) ≤ 2c₂t`), and dually
  `fsTau ≤ t² − 2c₁(1−εT)t + 2c₂²`, since
  `t² − 2c₁(1−εT)t + 2c₂² − fsTau = (1−εT)(c₂²−c₁²) + c₂² + 2εT c₂t ≥ 0`.
-/

namespace Work.BoseB6

theorem fsTau_bounds {εT c1 c2 t : ℝ} (hε0 : 0 ≤ εT) (hε1 : εT ≤ 1 / 2)
    (hc1 : 0 ≤ c1) (hc12 : c1 ≤ c2) (ht : 0 ≤ t) :
    0 ≤ Work.BoseB6.fsTau εT c1 c2 t ∧
      Work.BoseB6.fsTau εT c1 c2 t ≤ t ^ 2 ∧
      t ^ 2 - Work.BoseB6.fsTau εT c1 c2 t ≤ εT * t ^ 2 + 2 * c1 * t ∧
      (4 * c2 ≤ t → t ^ 2 / 2 ≤ Work.BoseB6.fsTau εT c1 c2 t) ∧
      (4 * c2 ≤ t → t ^ 2 - Work.BoseB6.fsTau εT c1 c2 t ≤ 8 * (c1 + εT * c2) * t) ∧
      (4 * c2 ≤ t → Work.BoseB6.fsTau εT c1 c2 t ≤ t ^ 2 - 2 * c1 * (1 - εT) * t + 2 * c2 ^ 2) := by
  -- `t ≥ 0`, so the truncations use `|t| = t`.
  have htabs : |t| = t := abs_of_nonneg ht
  have hc2 : 0 ≤ c2 := le_trans hc1 hc12
  have h1mε : 0 ≤ 1 - εT := by linarith
  -- the numerical facts about the two truncations `a = [t−c₁]₊`, `b = [t−c₂]₊`
  have ha0 : 0 ≤ max (t - c1) 0 := le_max_right _ _
  have hb0 : 0 ≤ max (t - c2) 0 := le_max_right _ _
  have hat : max (t - c1) 0 ≤ t := max_le (by linarith) ht
  have hbt : max (t - c2) 0 ≤ t := max_le (by linarith) ht
  have ha2 : (max (t - c1) 0) ^ 2 ≤ t ^ 2 := by
    nlinarith [sq_nonneg (t - max (t - c1) 0)]
  have hb2 : (max (t - c2) 0) ^ 2 ≤ t ^ 2 := by
    nlinarith [sq_nonneg (t - max (t - c2) 0)]
  have hb0sq : 0 ≤ (max (t - c2) 0) ^ 2 := sq_nonneg _
  -- `t² − a² ≤ 2c₁t`
  have hA : t ^ 2 - (max (t - c1) 0) ^ 2 ≤ 2 * c1 * t := by
    rcases le_total c1 t with h | h
    · have hm : max (t - c1) 0 = t - c1 := max_eq_left (by linarith)
      rw [hm]; nlinarith
    · have hm : max (t - c1) 0 = 0 := max_eq_right (by linarith)
      rw [hm]; nlinarith
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- `0 ≤ fsTau`
    simp only [Work.BoseB6.fsTau, htabs]
    nlinarith [sq_nonneg (max (t - c1) 0), sq_nonneg (max (t - c2) 0)]
  · -- `fsTau ≤ t²`
    simp only [Work.BoseB6.fsTau, htabs]
    nlinarith
  · -- `t² − fsTau ≤ εT t² + 2c₁t`
    simp only [Work.BoseB6.fsTau, htabs]
    nlinarith
  · -- `t ≥ 4c₂ ⇒ t²/2 ≤ fsTau`
    intro h4
    have ha : max (t - c1) 0 = t - c1 := max_eq_left (by linarith)
    have hb : max (t - c2) 0 = t - c2 := max_eq_left (by linarith)
    have hsq : (t - c2) ^ 2 ≤ (t - c1) ^ 2 := by nlinarith [sq_nonneg (c2 - c1)]
    have hkey : t ^ 2 / 2 ≤ (t - c2) ^ 2 := by nlinarith
    simp only [Work.BoseB6.fsTau, htabs, ha, hb]
    nlinarith
  · -- `t ≥ 4c₂ ⇒ t² − fsTau ≤ 8(c₁ + εT c₂)t`
    intro h4
    have ha : max (t - c1) 0 = t - c1 := max_eq_left (by linarith)
    have hb : max (t - c2) 0 = t - c2 := max_eq_left (by linarith)
    have key : t ^ 2 - ((1 - εT) * (t - c1) ^ 2 + εT * (t - c2) ^ 2)
        = (1 - εT) * (t ^ 2 - (t - c1) ^ 2) + εT * (t ^ 2 - (t - c2) ^ 2) := by ring
    have h1 : t ^ 2 - (t - c1) ^ 2 ≤ 2 * c1 * t := by nlinarith
    have h2 : t ^ 2 - (t - c2) ^ 2 ≤ 2 * (c1 + c2) * t := by nlinarith
    have e1 := mul_le_mul_of_nonneg_left h1 h1mε
    have e2 := mul_le_mul_of_nonneg_left h2 hε0
    have hcs : 0 ≤ c1 + εT * c2 := by nlinarith [mul_nonneg hε0 hc2]
    have hmul : 0 ≤ (c1 + εT * c2) * t := mul_nonneg hcs ht
    simp only [Work.BoseB6.fsTau, htabs, ha, hb]
    nlinarith [e1, e2, key, hmul]
  · -- `t ≥ 4c₂ ⇒ fsTau ≤ t² − 2c₁(1−εT)t + 2c₂²`
    intro h4
    have ha : max (t - c1) 0 = t - c1 := max_eq_left (by linarith)
    have hb : max (t - c2) 0 = t - c2 := max_eq_left (by linarith)
    have hD : t ^ 2 - 2 * c1 * (1 - εT) * t + 2 * c2 ^ 2
        - ((1 - εT) * (t - c1) ^ 2 + εT * (t - c2) ^ 2)
        = (1 - εT) * ((c2 - c1) * (c2 + c1)) + c2 ^ 2 + 2 * εT * t * c2 := by ring
    have hA' : 0 ≤ (1 - εT) * ((c2 - c1) * (c2 + c1)) := by
      have hm1 : 0 ≤ c2 - c1 := by linarith
      have hm2 : 0 ≤ c2 + c1 := by linarith
      exact mul_nonneg h1mε (mul_nonneg hm1 hm2)
    have hB : 0 ≤ c2 ^ 2 := sq_nonneg c2
    have hC : 0 ≤ 2 * εT * t * c2 := by
      nlinarith [mul_nonneg hε0 ht, mul_nonneg (mul_nonneg hε0 ht) hc2]
    simp only [Work.BoseB6.fsTau, htabs, ha, hb]
    linarith [hD, hA', hB, hC]

end Work.BoseB6
