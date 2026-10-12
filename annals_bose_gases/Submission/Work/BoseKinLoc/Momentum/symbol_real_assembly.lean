import Mathlib.Algebra.Order.Star.Real
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseKinLoc.Momentum

/-- The multiplicative factor coming from the interaction term is dominated by
`4 u`: `min 4 ((3 u / 8)^2) ≤ 4 u` for `u > 0`. -/
lemma min_four_three_div_eight_sq_le (u : ℝ) (hu : 0 < u) :
    min 4 ((3 * u / 8) ^ 2) ≤ 4 * u := by
  rcases lt_or_ge 1 u with h | h
  · have h1 : min 4 ((3 * u / 8) ^ 2) ≤ 4 := min_le_left _ _
    nlinarith
  · have h2 : min 4 ((3 * u / 8) ^ 2) ≤ (3 * u / 8) ^ 2 := min_le_right _ _
    nlinarith [sq_nonneg (u - 1)]

/-- The interaction estimate controls `2 * B` by `8 * C₁ * u / L`, provided the
second factor `min C₁ (C₁ / L)` is bounded by `C₁ / L`. -/
lemma two_mul_B_le (C₁ u L B : ℝ) (hC₁ : 0 < C₁) (hu : 0 < u) (hL : 0 < L)
    (hB : B ≤ min 4 ((3 * u / 8) ^ 2) * min C₁ (C₁ / L)) :
    2 * B ≤ 8 * C₁ * u / L := by
  have hN : min 4 ((3 * u / 8) ^ 2) ≤ 4 * u := min_four_three_div_eight_sq_le u hu
  have hm : min C₁ (C₁ / L) ≤ C₁ / L := min_le_right _ _
  have hnn : 0 ≤ min C₁ (C₁ / L) := le_min hC₁.le (by positivity)
  calc 2 * B ≤ 2 * (min 4 ((3 * u / 8) ^ 2) * min C₁ (C₁ / L)) := by linarith
    _ = (2 * min 4 ((3 * u / 8) ^ 2)) * min C₁ (C₁ / L) := by ring
    _ ≤ (8 * u) * (C₁ / L) := mul_le_mul (by linarith) hm hnn (by positivity)
    _ = 8 * C₁ * u / L := by ring

/-- The slowly varying part of the kinetic tail: on `u ≤ L < 2 √u` the extra
term `min (256 u √u) (4 C₁)` is bounded by `9988 * (C₁ + 1) * u / L`.
(The hypothesis `L < 2 √u` with `u ≤ L` forces `u < 4`.) -/
lemma two_mul_min_tail_le (C₁ u L : ℝ) (hC₁ : 0 < C₁) (hu : 0 < u) (huL : u ≤ L)
    (hL : L < 2 * Real.sqrt u) :
    2 * min (256 * u * Real.sqrt u) (4 * C₁) ≤ 9988 * (C₁ + 1) * u / L := by
  have hsq : Real.sqrt u * Real.sqrt u = u := by rw [← sq, Real.sq_sqrt hu.le]
  have hu4 : u < 4 := by
    have hlt : Real.sqrt u < 2 := by nlinarith
    nlinarith [Real.sqrt_nonneg u, sq_nonneg (Real.sqrt u - 2)]
  have hm : min (256 * u * Real.sqrt u) (4 * C₁) ≤ 256 * u * Real.sqrt u :=
    min_le_left _ _
  rw [le_div_iff₀ (by linarith : (0 : ℝ) < L)]
  calc 2 * min (256 * u * Real.sqrt u) (4 * C₁) * L
      ≤ 512 * (u * Real.sqrt u) * L := by
        apply mul_le_mul_of_nonneg_right _ (le_of_lt (by linarith : (0 : ℝ) < L))
        linarith [hm]
    _ ≤ 512 * (u * Real.sqrt u) * (2 * Real.sqrt u) := by
        apply mul_le_mul_of_nonneg_left (le_of_lt hL); positivity
    _ = 1024 * u ^ 2 := by nlinarith [hsq]
    _ ≤ 9988 * (C₁ + 1) * u := by nlinarith

/-- In the regime `L ≤ u` the ratio `u / (u + L)` is at least `1/2`, which
leaves room for the crude bound `2A + 2B ≤ 16 C₁`. -/
lemma ratio_bound_le (C₁ u L : ℝ) (hC₁ : 0 < C₁) (hu : 0 < u) (hL : 0 < L)
    (hLu : L ≤ u) : 16 * C₁ ≤ 20000 * (C₁ + 1) * u / (u + L) := by
  rw [le_div_iff₀ (by linarith : (0 : ℝ) < u + L)]
  nlinarith

/-- In the regime `u < L` the ratio `u / (u + L)` is at least `u / (2L)`. -/
lemma ratio_bound_lt (C₁ u L : ℝ) (hC₁ : 0 < C₁) (hu : 0 < u) (hL : 0 < L)
    (huL : u < L) : 10000 * (C₁ + 1) * u / L ≤ 20000 * (C₁ + 1) * u / (u + L) := by
  rw [div_le_div_iff₀ hL (by linarith : (0 : ℝ) < u + L)]
  nlinarith [mul_nonneg (mul_nonneg (by linarith : (0 : ℝ) ≤ C₁ + 1) hu.le)
    (by linarith : (0 : ℝ) ≤ L - u)]

theorem symbol_real_assembly (C₁ u L A B I : ℝ) (hC₁ : 0 < C₁) (hu : 0 ≤ u) (hL : 0 < L)
    (hI : I ≤ 2 * A + 2 * B)
    (hA1 : A ≤ 4 * C₁)
    (hA2 : A ≤ 2 * C₁ * u / L +
      (if L < 2 * Real.sqrt u then min (256 * u * Real.sqrt u) (4 * C₁) else 0))
    (hB : B ≤ min 4 ((3 * u / 8) ^ 2) * min C₁ (C₁ / L)) :
    I ≤ 20000 * (C₁ + 1) * u / (u + L) := by
  rcases eq_or_lt_of_le hu with hu0 | hupos
  · -- degenerate case `u = 0`: all the bounds collapse to `0`
    have hu0' : u = 0 := hu0.symm
    have hA0 : A ≤ 0 := by
      have h := hA2
      rw [hu0'] at h
      rw [if_neg (by rw [Real.sqrt_zero]; linarith : ¬ (L < 2 * Real.sqrt 0))] at h
      simpa using h
    have hB0 : B ≤ 0 := by
      have h := hB
      rw [hu0'] at h
      norm_num at h
      exact h
    have hR0 : 20000 * (C₁ + 1) * u / (u + L) = 0 := by
      rw [hu0']; simp
    linarith
  · -- from now on `u > 0`
    rcases lt_or_ge u L with huL | hLu
    · -- case `u < L`
      have hK : 2 * (if L < 2 * Real.sqrt u then min (256 * u * Real.sqrt u) (4 * C₁) else 0)
          ≤ 9988 * (C₁ + 1) * u / L := by
        by_cases h : L < 2 * Real.sqrt u
        · rw [if_pos h]
          exact two_mul_min_tail_le C₁ u L hC₁ hupos (le_of_lt huL) h
        · rw [if_neg h]
          have : (0 : ℝ) ≤ 9988 * (C₁ + 1) * u / L := by positivity
          linarith
      have h2A : 2 * A ≤ 4 * C₁ * u / L +
          2 * (if L < 2 * Real.sqrt u then min (256 * u * Real.sqrt u) (4 * C₁) else 0) := by
        have h := mul_le_mul_of_nonneg_left hA2 (show (0 : ℝ) ≤ 2 by norm_num)
        calc 2 * A ≤ 2 * (2 * C₁ * u / L +
              (if L < 2 * Real.sqrt u then min (256 * u * Real.sqrt u) (4 * C₁) else 0)) := h
          _ = 4 * C₁ * u / L +
              2 * (if L < 2 * Real.sqrt u then min (256 * u * Real.sqrt u) (4 * C₁) else 0) := by
              ring
      have h2B : 2 * B ≤ 8 * C₁ * u / L := two_mul_B_le C₁ u L B hC₁ hupos hL hB
      have h1 : 4 * C₁ * u / L + 8 * C₁ * u / L ≤ 12 * (C₁ + 1) * u / L := by
        rw [← add_div, div_le_div_iff_of_pos_right hL]
        nlinarith
      have h2 : 12 * (C₁ + 1) * u / L + 9988 * (C₁ + 1) * u / L
          = 10000 * (C₁ + 1) * u / L := by ring
      have hmid : 2 * A + 2 * B ≤ 10000 * (C₁ + 1) * u / L := by linarith
      have hratio := ratio_bound_lt C₁ u L hC₁ hupos hL huL
      linarith
    · -- case `L ≤ u`
      have hB4 : B ≤ 4 * C₁ := by
        have h1 : min 4 ((3 * u / 8) ^ 2) ≤ 4 := min_le_left _ _
        have h2 : min C₁ (C₁ / L) ≤ C₁ := min_le_left _ _
        have h3 : (0 : ℝ) ≤ min C₁ (C₁ / L) := le_min hC₁.le (by positivity)
        calc B ≤ min 4 ((3 * u / 8) ^ 2) * min C₁ (C₁ / L) := hB
          _ ≤ 4 * C₁ := mul_le_mul h1 h2 h3 (by norm_num)
      have hI16 : I ≤ 16 * C₁ := by linarith
      have hgoal := ratio_bound_le C₁ u L hC₁ hupos hL hLu
      linarith

end Work.BoseKinLoc.Momentum
