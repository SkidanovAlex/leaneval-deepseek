import Mathlib

namespace Work.Pert.PinLogDev.AxisAux

theorem axis_arith {rr s ε a b : ℝ} (hrr : 0 < rr) (hs : 3 ≤ s) (hε : 0 < ε)
    (ha0 : 0 ≤ a) (hb0 : 0 ≤ b) (ha : a ≤ 13 / 10 * ε) (hb : b ≤ 19 / 10 / s) :
    4 * (a * (4 * b / rr + 9 / 8 * (9 / 8 * b)) / (7 / 25)) ≤ (200 / rr + 100) * ε / s := by
  -- `9 / 8 * (9 / 8 * b) = 81 / 64 * b`, so the left-hand side is
  -- `(100 / 7) * a * b * (4 / rr + 81 / 64)`; everything is then monotone in `a`, `b`.
  have hs' : (0 : ℝ) < s := by linarith
  -- clear the division in the hypothesis on `b`
  have hb' : b * s ≤ 19 / 10 := (le_div_iff₀ hs').mp hb
  have hbs : 0 ≤ b * s := by positivity
  have hab : a * (b * s) ≤ (13 / 10 * ε) * (19 / 10) :=
    mul_le_mul ha hb' hbs (by positivity)
  have hrr0 : rr ≠ 0 := ne_of_gt hrr
  have hs0 : s ≠ 0 := ne_of_gt hs'
  have hK : 0 ≤ 4 * 8 ^ 2 + rr * 9 ^ 2 := by positivity
  field_simp
  nlinarith [hab, hrr, hε, ha0, hb0, hK]

end Work.Pert.PinLogDev.AxisAux
