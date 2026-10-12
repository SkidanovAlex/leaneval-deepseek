import Mathlib.Analysis.SpecialFunctions.Pow.Real
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseRowsL.Regime.rkh_rpow_arith` — the threshold arithmetic of the
`R K_H` vs `ℓ` row

Pure real-variable `rpow` arithmetic.  The point is that the two exponents occurring in the
row satisfy the *exact* identities

`(326 : ℝ)/323 - (549 : ℝ)/1292 = 755/1292`,   `(1292 : ℝ)/755 * (755 : ℝ)/1292 = 1`,

so the hypothesis `t ≤ (A²/(2R²))^(1292/755)` — after taking the `755/1292`-th power — becomes
`t^(755/1292) ≤ A²/(2R²) ≤ A²/R²`, which is precisely what the conclusion needs:

`R² t^(326/323)/A² ≤ t^(549/1292)`

(the two sides differ exactly by the factor `(A²/R²)·t^(-755/1292)`).  Note that the hypothesis
carries the harmless but *strictly stronger* factor `2` in `A²/(2R²)`: the conclusion only needs
`t^(755/1292) ≤ A²/R²`.
-/

namespace Work.BoseRowsL.Regime

/-- The reduced (factor-free) form of the threshold arithmetic: the hypothesis
`t ≤ (A²/(2R²))^(1292/755)` implies `t^(755/1292) ≤ A²/R²`.

Both bases are nonnegative, `1292/755 > 0`, and `(1292/755)·(755/1292) = 1`, so raising the
hypothesis to the power `755/1292` gives `t^(755/1292) ≤ A²/(2R²)`; the conclusion follows
since `A²/(2R²) ≤ A²/R²`. -/
lemma rpow_755_1292_le {R A t : ℝ} (hR : 0 < R) (hA : 0 < A) (ht : 0 < t)
    (h : t ≤ (A ^ 2 / (2 * R ^ 2)) ^ ((1292 : ℝ) / 755)) :
    t ^ ((755 : ℝ) / 1292) ≤ A ^ 2 / R ^ 2 := by
  have hb : 0 ≤ A ^ 2 / (2 * R ^ 2) := by positivity
  have h1 : t ^ ((755 : ℝ) / 1292)
      ≤ ((A ^ 2 / (2 * R ^ 2)) ^ ((1292 : ℝ) / 755)) ^ ((755 : ℝ) / 1292) :=
    Real.rpow_le_rpow ht.le h (by norm_num)
  rw [← Real.rpow_mul hb] at h1
  have hmul : ((1292 : ℝ) / 755) * ((755 : ℝ) / 1292) = 1 := by norm_num
  rw [hmul, Real.rpow_one] at h1
  have hpos : (0 : ℝ) < R ^ 2 := by positivity
  have hle : A ^ 2 / (2 * R ^ 2) ≤ A ^ 2 / R ^ 2 :=
    div_le_div_of_nonneg_left (by positivity) hpos (by nlinarith [hpos])
  linarith

lemma rkh_rpow_arith {R A t : ℝ} (hR : 0 < R) (hA : 0 < A) (ht : 0 < t)
    (h : t ≤ (A ^ 2 / (2 * R ^ 2)) ^ ((1292 : ℝ) / 755)) :
    R ^ 2 * t ^ ((326 : ℝ) / 323) / A ^ 2 ≤ t ^ ((549 : ℝ) / 1292) := by
  have hY : t ^ ((755 : ℝ) / 1292) ≤ A ^ 2 / R ^ 2 := rpow_755_1292_le hR hA ht h
  have hR2 : (0 : ℝ) < R ^ 2 := by positivity
  have hA2 : (0 : ℝ) < A ^ 2 := by positivity
  have hYpos : (0 : ℝ) < t ^ ((755 : ℝ) / 1292) := Real.rpow_pos_of_pos ht _
  -- the exponent shift `549/1292 = 326/323 - 755/1292`
  have hsub : t ^ ((549 : ℝ) / 1292)
      = t ^ ((326 : ℝ) / 323) / t ^ ((755 : ℝ) / 1292) := by
    rw [show (549 : ℝ) / 1292 = (326 : ℝ) / 323 - (755 : ℝ) / 1292 by norm_num,
      Real.rpow_sub ht]
  rw [hsub]
  -- monotonicity of `x ↦ x / d`, comparing `d = A²/R²` with `d = t^(755/1292)`
  have hX : (0 : ℝ) ≤ t ^ ((326 : ℝ) / 323) := (Real.rpow_pos_of_pos ht _).le
  have h1 : t ^ ((326 : ℝ) / 323) / (A ^ 2 / R ^ 2)
      ≤ t ^ ((326 : ℝ) / 323) / t ^ ((755 : ℝ) / 1292) :=
    div_le_div_of_nonneg_left hX hYpos hY
  have h2 : t ^ ((326 : ℝ) / 323) / (A ^ 2 / R ^ 2)
      = R ^ 2 * t ^ ((326 : ℝ) / 323) / A ^ 2 := by
    field_simp
  linarith

end Work.BoseRowsL.Regime
