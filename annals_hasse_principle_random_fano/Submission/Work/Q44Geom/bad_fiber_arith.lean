import Mathlib

namespace Work.Q44Geom

theorem bad_fiber_arith {C0 c0 s1 s2 Gk Z : ℝ} (hC0 : 0 < C0) (hc0 : 0 < c0)
    (hs1 : 1 ≤ s1) (hs12 : s1 ≤ s2)
    (hA : Gk * (64 * c0 * (s2 ^ 2 / s1 ^ 2)) ≤ Z) (hZ : Z ≤ C0 * (8 * s2) ^ 4) :
    Gk ≤ (64 * C0 / c0 + 1) * s1 ^ 2 * s2 ^ 2 := by
  have hs1pos : 0 < s1 := by linarith
  have hs2pos : 0 < s2 := by linarith
  have hkpos : 0 < 64 * c0 * (s2 ^ 2 / s1 ^ 2) := by positivity
  have h1 : Gk * (64 * c0 * (s2 ^ 2 / s1 ^ 2)) ≤ C0 * (8 * s2) ^ 4 := le_trans hA hZ
  have h2 : Gk ≤ C0 * (8 * s2) ^ 4 / (64 * c0 * (s2 ^ 2 / s1 ^ 2)) :=
    (le_div_iff₀ hkpos).mpr h1
  have hval : C0 * (8 * s2) ^ 4 / (64 * c0 * (s2 ^ 2 / s1 ^ 2)) = 64 * C0 / c0 * s1 ^ 2 * s2 ^ 2 := by
    field_simp
    ring
  rw [hval] at h2
  nlinarith [sq_nonneg s1, sq_nonneg s2, mul_nonneg (sq_nonneg s1) (sq_nonneg s2),
    hc0, hC0, hs1pos, hs2pos]

end Work.Q44Geom
