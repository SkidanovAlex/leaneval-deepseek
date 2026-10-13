import Mathlib

namespace Work.WilE7

/-- If `a : EReal` lies strictly below two real numbers `x` and `y`, then `a` lies strictly
below any convex combination `(1 - s) * x + s * y` with `0 ≤ s ≤ 1`. -/
private lemma ereal_lt_coe_combo {a : EReal} {x y s : ℝ}
    (hx : a < (x : EReal)) (hy : a < (y : EReal)) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    a < (((1 - s) * x + s * y : ℝ) : EReal) := by
  induction a using EReal.rec with
  | bot => exact EReal.bot_lt_coe _
  | top => exact (not_top_lt hx).elim
  | coe ra =>
    rw [EReal.coe_lt_coe_iff] at hx hy ⊢
    rcases eq_or_lt_of_le hs1 with h | h
    · subst h; ring_nf; linarith
    · have hh : ra = (1 - s) * ra + s * ra := by ring
      rw [hh]
      exact add_lt_add_of_lt_of_le (mul_lt_mul_of_pos_left hx (by linarith))
              (mul_le_mul_of_nonneg_left hy.le hs0)

/-- If two real numbers `x` and `y` lie strictly below `b : EReal`, then so does any convex
combination `(1 - s) * x + s * y` with `0 ≤ s ≤ 1`. -/
private lemma ereal_coe_combo_lt {b : EReal} {x y s : ℝ}
    (hx : (x : EReal) < b) (hy : (y : EReal) < b) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    (((1 - s) * x + s * y : ℝ) : EReal) < b := by
  induction b using EReal.rec with
  | bot => exact (not_lt_bot hx).elim
  | top => exact EReal.coe_lt_top _
  | coe rb =>
    rw [EReal.coe_lt_coe_iff] at hx hy ⊢
    rcases eq_or_lt_of_le hs0 with h | h
    · subst h; ring_nf; linarith
    · have hh : rb = (1 - s) * rb + s * rb := by ring
      rw [hh]
      exact add_lt_add_of_le_of_lt (mul_le_mul_of_nonneg_left hx.le (by linarith))
              (mul_lt_mul_of_pos_left hy h)

theorem ereal_between_convex {a b : EReal} {r₁ r₂ : ℝ}
    (h1 : a < (r₁ : EReal) ∧ (r₁ : EReal) < b) (h2 : a < (r₂ : EReal) ∧ (r₂ : EReal) < b)
    {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    a < (((1 - s) * r₁ + s * r₂ : ℝ) : EReal) ∧ (((1 - s) * r₁ + s * r₂ : ℝ) : EReal) < b :=
  ⟨ereal_lt_coe_combo h1.1 h2.1 hs0 hs1, ereal_coe_combo_lt h1.2 h2.2 hs0 hs1⟩

end Work.WilE7
