import Mathlib
import Submission.Work.PARIMPL2.Direct.oidAux

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.PARIMPL2.Direct

/-! ## Pointwise bound for the growth coefficient `C'_j`

`C'_j = -cr · (ζ_j).im / y_j` where `ζ_j = ecalPt (iλ) (x_j + i y_j)`.  We show

`|C'_j| ≤ |cr| · (λ² + λ²/D_j) = oidCg λ |cr| x y j`,

i.e. the size of the (one-step) growth coefficient of the imaginary recurrence is
controlled by the quantity `oidCg` that the transport estimates sum.  The analytic
input is only `sinh t ≤ t·cosh t` (`t ≥ 0`) together with `cosh² = sinh² + 1`. -/

/-- If `t ≠ 0`, `D > 0` and `D ≥ sinh²(λt)`, then

`λ·sinh(λ|t|)·cosh(λt)/(D·|t|) ≤ λ² + λ²/D`.

This is the numerical core of `oidCf_abs_le`. -/
private theorem oidCf_core_bound (lam t D : ℝ) (hlam : 0 < lam) (hD : 0 < D)
    (hDt : Real.sinh (lam * t) ^ 2 ≤ D) (ht : t ≠ 0) :
    lam * Real.sinh (lam * |t|) * Real.cosh (lam * t) / (D * |t|)
      ≤ lam ^ 2 + lam ^ 2 / D := by
  have ha : 0 < |t| := abs_pos.mpr ht
  have hcosh : Real.cosh (lam * |t|) = Real.cosh (lam * t) := by
    rw [← Real.cosh_abs (lam * t), abs_mul, abs_of_pos hlam]
  have hsinh := sinh_le_mul_cosh (lam * |t|) (by positivity)
  rw [div_le_iff₀ (mul_pos hD ha)]
  have hstep : lam * Real.sinh (lam * |t|) * Real.cosh (lam * |t|)
      ≤ lam * ((lam * |t|) * Real.cosh (lam * |t|)) * Real.cosh (lam * |t|) := by
    have hc : (0 : ℝ) ≤ lam * Real.cosh (lam * |t|) := by positivity
    have h := mul_le_mul_of_nonneg_right hsinh hc
    nlinarith [h]
  have h2 : Real.cosh (lam * t) ^ 2 ≤ D + 1 := by
    rw [Real.cosh_sq]; linarith
  have h3 : (0 : ℝ) ≤ lam ^ 2 * |t| := by positivity
  calc lam * Real.sinh (lam * |t|) * Real.cosh (lam * t)
      = lam * Real.sinh (lam * |t|) * Real.cosh (lam * |t|) := by rw [hcosh]
    _ ≤ lam * ((lam * |t|) * Real.cosh (lam * |t|)) * Real.cosh (lam * |t|) := hstep
    _ = lam ^ 2 * |t| * Real.cosh (lam * t) ^ 2 := by rw [hcosh]; ring
    _ ≤ lam ^ 2 * |t| * (D + 1) := mul_le_mul_of_nonneg_left h2 h3
    _ = (lam ^ 2 + lam ^ 2 / D) * (D * |t|) := by field_simp

theorem oidCf_abs_le (lam cr : ℝ) (hlam : 0 < lam) (x y : ℕ → ℝ) (j : ℕ) :
    |Work.PARIMPL2.Direct.oidCf lam cr x y j| ≤ Work.PARIMPL2.Direct.oidCg lam |cr| x y j := by
  by_cases hy : y j = 0
  · rw [oidCf, oidZeta_im_zero_of lam x y j hy, hy, oidCg]
    simp only [mul_zero, zero_div, abs_zero]
    apply mul_nonneg (abs_nonneg _)
    exact add_nonneg (sq_nonneg _) (div_nonneg (sq_nonneg _) (ocDen_nonneg lam x y j))
  · have hs : Real.sinh (lam * y j) ≠ 0 := by
      intro h
      rcases mul_eq_zero.mp (Real.sinh_eq_zero.mp h) with h1 | h2
      · exact hlam.ne' h1
      · exact hy h2
    have hDpos : 0 < ocDen lam x y j := by
      rw [ocDen]
      nlinarith [sq_pos_of_ne_zero hs, sq_nonneg (Real.sin (lam * x j))]
    have hDt : Real.sinh (lam * y j) ^ 2 ≤ ocDen lam x y j := by
      rw [ocDen]; linarith [sq_nonneg (Real.sin (lam * x j))]
    have hcf : oidCf lam cr x y j
        = cr * (lam * Real.sinh (lam * y j) * Real.cosh (lam * y j))
            / (ocDen lam x y j * y j) := by
      rw [oidCf, oidZeta_im]
      field_simp
    have habs : |oidCf lam cr x y j|
        = |cr| * (lam * Real.sinh (lam * |y j|) * Real.cosh (lam * y j))
            / (ocDen lam x y j * |y j|) := by
      rw [hcf]
      rw [abs_div, abs_mul cr (lam * Real.sinh (lam * y j) * Real.cosh (lam * y j)),
        abs_mul (lam * Real.sinh (lam * y j)) (Real.cosh (lam * y j)),
        abs_mul lam (Real.sinh (lam * y j)), abs_mul (ocDen lam x y j) (y j),
        Real.abs_sinh, abs_of_pos hlam, abs_of_pos hDpos, abs_of_pos (Real.cosh_pos _)]
      rw [abs_mul, abs_of_pos hlam]
    rw [habs, oidCg, mul_div_assoc]
    exact mul_le_mul_of_nonneg_left
      (oidCf_core_bound lam (y j) (ocDen lam x y j) hlam hDpos hDt hy) (abs_nonneg cr)

end Work.PARIMPL2.Direct
