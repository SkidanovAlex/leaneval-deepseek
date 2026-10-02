/-
Copyright: subproject `Submission/Work/LandLeaves/` of `mandelbar_not_path_connected`.

Preliminaries for `Work.LandLeaves.chart_descent_bound`: the second-order Taylor estimate for
`w ↦ w^{-n}` at `w = 1` around a non-zero `z`, which is the analytic content of the "descent"
chart for a germ of order `n + 1 ≥ 2`.
-/
import Mathlib

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.LandLeaves

/-- `n + 1 ≤ 4^n` (as real numbers), the elementary numerical fact controlling the growth of the
constant `4^n` in the Taylor estimate. -/
lemma cast_add_one_le_four_pow (n : ℕ) : ((n : ℝ) + 1) ≤ 4 ^ n := by
  induction n with
  | zero => norm_num
  | succ k ih =>
    have hpos : (1 : ℝ) ≤ 4 ^ k := one_le_pow₀ (by norm_num)
    rw [pow_succ]
    push_cast
    nlinarith [ih, hpos]

/-- **Second-order Taylor estimate at `1` for `w ↦ w^{-n}`.**  If `‖w - 1‖ ≤ 1/2` then the
first-order Taylor polynomial `1 - n(w-1)` approximates `w^{-n}` up to an error controlled by
`4^n ‖w - 1‖²`. -/
lemma norm_inv_pow_taylor (n : ℕ) (w : ℂ) (hw : ‖w - 1‖ ≤ 1 / 2) :
    ‖(w ^ n)⁻¹ - (1 - (n : ℂ) * (w - 1))‖ ≤ (4 : ℝ) ^ n * ‖w - 1‖ ^ 2 := by
  have h1 : (1 : ℝ) / 2 ≤ ‖w‖ := by
    have h := norm_sub_le w (w - 1)
    have hw1 : w - (w - 1) = (1 : ℂ) := by ring
    rw [hw1, norm_one] at h
    linarith
  have hwpos : 0 < ‖w‖ := by linarith
  have hwne : w ≠ 0 := by
    intro h; rw [h] at hwpos; simp at hwpos
  have hinvw : ‖w⁻¹‖ ≤ 2 := by
    rw [norm_inv]
    have h := (inv_le_inv₀ hwpos (by norm_num : (0 : ℝ) < 1 / 2)).mpr h1
    norm_num at h
    exact h
  have h4 : ∀ m : ℕ, (2 : ℝ) * 4 ^ m + 2 * ((m : ℝ) + 1) ≤ 4 ^ (m + 1) := by
    intro m
    have hle : (m : ℝ) + 1 ≤ 4 ^ m := cast_add_one_le_four_pow m
    rw [pow_succ]
    nlinarith [hle]
  have key : ∀ m : ℕ, ‖(w ^ m)⁻¹ - (1 - (m : ℂ) * (w - 1))‖
      ≤ (4 : ℝ) ^ m * ‖w - 1‖ ^ 2 := by
    intro m
    induction m with
    | zero => simp
    | succ k ih =>
      have hcast : ((k + 1 : ℕ) : ℂ) = (k : ℂ) + 1 := by push_cast; ring
      rw [hcast, pow_succ]
      have hrec : (w ^ k * w)⁻¹ - (1 - (↑k + 1) * (w - 1))
          = w⁻¹ * ((w ^ k)⁻¹ - (1 - ↑k * (w - 1))) + (↑k + 1) * (w - 1) ^ 2 * w⁻¹ := by
        field_simp
        ring
      rw [hrec]
      have hb4 : ‖((k : ℂ) + 1)‖ ≤ (k : ℝ) + 1 := by
        calc ‖((k : ℂ) + 1)‖ ≤ ‖(k : ℂ)‖ + ‖(1 : ℂ)‖ := norm_add_le _ _
          _ = (k : ℝ) + 1 := by simp
      have hb5 : ‖((w - 1) ^ 2)‖ = ‖w - 1‖ ^ 2 := norm_pow _ _
      calc ‖w⁻¹ * ((w ^ k)⁻¹ - (1 - ↑k * (w - 1))) + (↑k + 1) * (w - 1) ^ 2 * w⁻¹‖
          ≤ ‖w⁻¹ * ((w ^ k)⁻¹ - (1 - ↑k * (w - 1)))‖ + ‖(↑k + 1) * (w - 1) ^ 2 * w⁻¹‖ :=
            norm_add_le _ _
        _ = ‖w⁻¹‖ * ‖(w ^ k)⁻¹ - (1 - ↑k * (w - 1))‖
              + ‖((k : ℂ) + 1)‖ * ‖((w - 1) ^ 2)‖ * ‖w⁻¹‖ := by
            rw [norm_mul, norm_mul, norm_mul]
        _ ≤ 2 * ((4 : ℝ) ^ k * ‖w - 1‖ ^ 2) + ((k : ℝ) + 1) * ‖w - 1‖ ^ 2 * 2 := by
            have h2 : 0 ≤ ‖w - 1‖ ^ 2 := sq_nonneg _
            have hX : ‖(w ^ k)⁻¹ - (1 - ↑k * (w - 1))‖ ≤ (4 : ℝ) ^ k * ‖w - 1‖ ^ 2 := ih
            have hY : ‖((k : ℂ) + 1)‖ * ‖((w - 1) ^ 2)‖ * ‖w⁻¹‖
                ≤ ((k : ℝ) + 1) * ‖w - 1‖ ^ 2 * 2 := by
              rw [hb5]
              exact mul_le_mul (mul_le_mul hb4 le_rfl h2 (by positivity)) hinvw (by positivity)
                (mul_nonneg (by positivity) h2)
            have hprod : ‖w⁻¹‖ * ‖(w ^ k)⁻¹ - (1 - ↑k * (w - 1))‖
                ≤ 2 * ((4 : ℝ) ^ k * ‖w - 1‖ ^ 2) :=
              mul_le_mul hinvw hX (by positivity) (by norm_num)
            linarith
        _ ≤ (4 : ℝ) ^ (k + 1) * ‖w - 1‖ ^ 2 := by
            rw [pow_succ]
            nlinarith [h4 k, sq_nonneg ‖w - 1‖]
  exact key n

/-- Algebraic factorisation behind the Taylor estimate: writing `d = z(w-1)`,
`((z+d)^n)^{-1}` differs from `z^{-n}` by `-n z^{-n-1} d` up to a remainder which is
`z^{-n} · E_n(w)` with `E_n(w) = (w^n)^{-1} - 1 + n(w-1)`. -/
lemma fac_helper (n : ℕ) (z w d : ℂ) (hz : z ≠ 0) (hzw : z * w = z + d) :
    ((z + d) ^ n)⁻¹ - (z ^ n)⁻¹ + (n : ℂ) * (z ^ (n + 1))⁻¹ * d
      = (z ^ n)⁻¹ * ((w ^ n)⁻¹ - 1 + (n : ℂ) * (w - 1)) := by
  rw [← hzw]
  have hd' : d = z * (w - 1) := by rw [mul_sub, mul_one, hzw]; ring
  rw [hd']
  rw [mul_pow, mul_inv, pow_succ, mul_inv]
  field_simp

/-- The same factorisation with `w = (z+d)/z` made explicit. -/
lemma pow_inv_factor (n : ℕ) (z d : ℂ) (hz : z ≠ 0) :
    ((z + d) ^ n)⁻¹ - (z ^ n)⁻¹ + (n : ℂ) * (z ^ (n + 1))⁻¹ * d
      = (z ^ n)⁻¹ * ((((z + d) / z) ^ n)⁻¹ - 1 + (n : ℂ) * ((z + d) / z - 1)) := by
  refine fac_helper n z ((z + d) / z) d hz ?_
  field_simp

/-- **Linearisation of `z ↦ z^{-n}` at `z`.**  If `‖d‖ ≤ ‖z‖/2` and `z ≠ 0` then
`(z+d)^{-n}` differs from `z^{-n} - n z^{-n-1} d` by at most `4^n ‖d‖² / ‖z‖^{n+2}`. -/
lemma norm_pow_inv_sub_linear (n : ℕ) (z d : ℂ) (hz : z ≠ 0) (hd : ‖d‖ ≤ ‖z‖ / 2) :
    ‖((z + d) ^ n)⁻¹ - (z ^ n)⁻¹ + (n : ℂ) * (z ^ (n + 1))⁻¹ * d‖
      ≤ (4 : ℝ) ^ n * ‖d‖ ^ 2 / ‖z‖ ^ (n + 2) := by
  have hzpos : 0 < ‖z‖ := norm_pos_iff.mpr hz
  set w : ℂ := (z + d) / z with hw_def
  have hzw : z * w = z + d := by rw [hw_def]; field_simp
  have hw1 : w - 1 = z⁻¹ * d := by rw [hw_def]; field_simp; ring
  have hwclose : ‖w - 1‖ ≤ 1 / 2 := by
    rw [hw1, norm_mul, norm_inv]
    calc ‖z‖⁻¹ * ‖d‖ ≤ ‖z‖⁻¹ * (‖z‖ / 2) := mul_le_mul_of_nonneg_left hd (by positivity)
      _ = 1 / 2 := by field_simp
  have hE : ‖(w ^ n)⁻¹ - 1 + (n : ℂ) * (w - 1)‖ ≤ (4 : ℝ) ^ n * ‖w - 1‖ ^ 2 := by
    have hthis := norm_inv_pow_taylor n w hwclose
    have he : (w ^ n)⁻¹ - (1 - (n : ℂ) * (w - 1)) = (w ^ n)⁻¹ - 1 + (n : ℂ) * (w - 1) := by
      ring
    rwa [he] at hthis
  rw [pow_inv_factor n z d hz, norm_mul, norm_inv, norm_pow]
  calc (‖z‖ ^ n)⁻¹ * ‖(w ^ n)⁻¹ - 1 + (n : ℂ) * (w - 1)‖
      ≤ (‖z‖ ^ n)⁻¹ * ((4 : ℝ) ^ n * ‖w - 1‖ ^ 2) :=
        mul_le_mul_of_nonneg_left hE (by positivity)
    _ = (4 : ℝ) ^ n * ‖d‖ ^ 2 / ‖z‖ ^ (n + 2) := by
        rw [hw1, norm_mul, norm_inv]
        field_simp
        ring

end Work.LandLeaves
