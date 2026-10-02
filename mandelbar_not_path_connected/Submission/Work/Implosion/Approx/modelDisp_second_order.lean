import Mathlib
import Submission.Work.Implosion.Basic
import Submission.Work.Implosion.Ecalle
import Submission.Work.Implosion.Disp
import Submission.Work.Implosion.Approx

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.Implosion.Approx

open Complex

/-- The cubic remainder `Lz z = log (1+z) - z + z²/2` of the complex logarithm.  Since
`Lz' z = z²/(1+z)`, on a convex disc of radius `≤ 1/2` the function `Lz` is Lipschitz with
constant `8·(radius)²`; this is exactly the second-order control of the displacement that
makes the error uniform in `a` (no factor `1/‖a‖`). -/
private noncomputable def Lz (z : ℂ) : ℂ := Complex.log (1 + z) - z + z ^ 2 / 2

/-- `logTaylor 3 z = z - z²/2`, i.e. `Lz z = log (1+z) - logTaylor 3 z`. -/
private lemma logTaylor_three (z : ℂ) : Complex.logTaylor 3 z = z - z ^ 2 / 2 := by
  simp only [Complex.logTaylor_succ, Complex.logTaylor_zero, Pi.add_apply]
  ring

/-- The derivative of the cubic remainder. -/
private lemma hasDerivAt_Lz (x : ℂ) (hx : 1 + x ∈ Complex.slitPlane) :
    HasDerivAt Lz (x ^ 2 / (1 + x)) x := by
  have h := Complex.hasDerivAt_log_sub_logTaylor 2 hx
  convert h using 1
  · ext z
    simp only [Lz, Complex.logTaylor_succ, Complex.logTaylor_zero, Pi.add_apply]
    ring
  · ring

/-- Bound on the derivative of `Lz` on the closed disc of radius `2s` (with `2s ≤ 1/2`). -/
private lemma norm_deriv_Lz_le (x : ℂ) (s : ℝ) (hs : 0 ≤ s) (hxs : ‖x‖ ≤ 2 * s)
    (hs2 : 2 * s ≤ 1 / 2) : ‖deriv Lz x‖ ≤ 8 * s ^ 2 := by
  have hx1 : 1 + x ∈ Complex.slitPlane :=
    Complex.mem_slitPlane_of_norm_lt_one (by linarith)
  rw [(hasDerivAt_Lz x hx1).deriv, norm_div, norm_pow]
  have hden : (1 : ℝ) / 2 ≤ ‖1 + x‖ := by
    have h := norm_sub_norm_le (1 : ℂ) (-x)
    rw [norm_neg, norm_one, sub_neg_eq_add] at h
    linarith
  have hnum : ‖x‖ ^ 2 ≤ (2 * s) ^ 2 := pow_le_pow_left₀ (norm_nonneg x) hxs 2
  have hpos : (0 : ℝ) < ‖1 + x‖ := by linarith
  rw [div_le_iff₀ hpos]
  have h1 : (2 * s) ^ 2 ≤ 8 * s ^ 2 * ‖1 + x‖ := by
    have h := mul_le_mul_of_nonneg_left hden (by positivity : (0 : ℝ) ≤ 8 * s ^ 2)
    nlinarith [h, hs]
  linarith

/-- The elementary algebraic identity behind the estimate: twice `a` times the second-order
error of the exact displacement `modelDisp` is the difference of the cubic remainders at the
two perturbations `A₁ = (ζ-a)h(ζ)`, `A₂ = (ζ+a)h(ζ)`, where `ζ = ecalPt a u`. -/
private lemma two_a_mul_modelDisp (a : ℂ) (h : ℂ → ℂ) (u : ℂ) (ha : a ≠ 0) :
    2 * a * (modelDisp a h u + h (ecalPt a u) - ecalPt a u * h (ecalPt a u) ^ 2)
      = Lz (dispNum1 a h u) - Lz (dispNum2 a h u) := by
  simp only [Lz, modelDisp, dispNum1, dispNum2]
  field_simp
  ring

theorem modelDisp_second_order (a : ℂ) (h : ℂ → ℂ) (u : ℂ) (ha : a ≠ 0)
    (hsmall : 4 * (‖ecalPt a u‖ + ‖a‖) ≤ 1) (hh : ‖h (ecalPt a u)‖ ≤ 2) :
    ‖modelDisp a h u + h (ecalPt a u) - ecalPt a u * h (ecalPt a u) ^ 2‖
      ≤ 32 * (‖ecalPt a u‖ ^ 2 + ‖a‖ ^ 2) := by
  have hna : (0 : ℝ) < ‖a‖ := norm_pos_iff.mpr ha
  set s : ℝ := ‖ecalPt a u‖ + ‖a‖ with hs
  have hs0 : 0 ≤ s := by rw [hs]; positivity
  have hs4 : 4 * s ≤ 1 := by rw [hs]; exact hsmall
  have hs2 : 2 * s ≤ 1 / 2 := by linarith
  set A1 : ℂ := dispNum1 a h u with hA1
  set A2 : ℂ := dispNum2 a h u with hA2
  have hζa : ‖ecalPt a u - a‖ ≤ s := by
    rw [hs]
    exact norm_sub_le _ _
  have hζb : ‖ecalPt a u + a‖ ≤ s := by
    rw [hs]
    exact norm_add_le _ _
  have hA1n : ‖A1‖ ≤ 2 * s := by
    rw [hA1, dispNum1, norm_mul]
    calc ‖ecalPt a u - a‖ * ‖h (ecalPt a u)‖ ≤ s * 2 :=
          mul_le_mul hζa hh (norm_nonneg _) hs0
      _ = 2 * s := by ring
  have hA2n : ‖A2‖ ≤ 2 * s := by
    rw [hA2, dispNum2, norm_mul]
    calc ‖ecalPt a u + a‖ * ‖h (ecalPt a u)‖ ≤ s * 2 :=
          mul_le_mul hζb hh (norm_nonneg _) hs0
      _ = 2 * s := by ring
  have hA1mem : A1 ∈ Metric.closedBall (0 : ℂ) (2 * s) := by
    rw [Metric.mem_closedBall, dist_zero_right]; exact hA1n
  have hA2mem : A2 ∈ Metric.closedBall (0 : ℂ) (2 * s) := by
    rw [Metric.mem_closedBall, dist_zero_right]; exact hA2n
  have hmvt : ‖Lz A1 - Lz A2‖ ≤ 8 * s ^ 2 * ‖A1 - A2‖ := by
    refine Convex.norm_image_sub_le_of_norm_deriv_le (f := Lz)
      (s := Metric.closedBall (0 : ℂ) (2 * s)) (C := 8 * s ^ 2) ?_ ?_
      (convex_closedBall _ _) hA2mem hA1mem
    · intro x hx
      rw [Metric.mem_closedBall, dist_zero_right] at hx
      exact (hasDerivAt_Lz x (Complex.mem_slitPlane_of_norm_lt_one (by linarith))).differentiableAt
    · intro x hx
      rw [Metric.mem_closedBall, dist_zero_right] at hx
      exact norm_deriv_Lz_le x s hs0 hx hs2
  have hA12 : ‖A1 - A2‖ = 2 * ‖a‖ * ‖h (ecalPt a u)‖ := by
    rw [hA1, hA2, dispNum1_sub_dispNum2 a h u,
      show (-2 : ℂ) * a * h (ecalPt a u) = -((2 : ℂ) * (a * h (ecalPt a u))) by ring,
      norm_neg, norm_mul, norm_mul, Complex.norm_ofNat]
    ring
  have hstep : ‖Lz A1 - Lz A2‖ ≤ 32 * s ^ 2 * ‖a‖ := by
    calc ‖Lz A1 - Lz A2‖ ≤ 8 * s ^ 2 * ‖A1 - A2‖ := hmvt
      _ = 8 * s ^ 2 * (2 * ‖a‖ * ‖h (ecalPt a u)‖) := by rw [hA12]
      _ ≤ 8 * s ^ 2 * (2 * ‖a‖ * 2) := by
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            exact mul_le_mul_of_nonneg_left hh (by positivity)
      _ = 32 * s ^ 2 * ‖a‖ := by ring
  have hX : 2 * a * (modelDisp a h u + h (ecalPt a u) - ecalPt a u * h (ecalPt a u) ^ 2)
      = Lz A1 - Lz A2 := by
    rw [hA1, hA2]; exact two_a_mul_modelDisp a h u ha
  have hnorm : ‖modelDisp a h u + h (ecalPt a u) - ecalPt a u * h (ecalPt a u) ^ 2‖
      = ‖Lz A1 - Lz A2‖ / (2 * ‖a‖) := by
    have h2 : 2 * ‖a‖ * ‖modelDisp a h u + h (ecalPt a u)
        - ecalPt a u * h (ecalPt a u) ^ 2‖ = ‖Lz A1 - Lz A2‖ := by
      have hh2 := congrArg Norm.norm hX
      rwa [norm_mul, norm_mul, Complex.norm_ofNat] at hh2
    have hpos : (0 : ℝ) < 2 * ‖a‖ := by linarith
    rw [eq_div_iff (ne_of_gt hpos)]
    linarith
  calc ‖modelDisp a h u + h (ecalPt a u) - ecalPt a u * h (ecalPt a u) ^ 2‖
      = ‖Lz A1 - Lz A2‖ / (2 * ‖a‖) := hnorm
    _ ≤ 32 * s ^ 2 * ‖a‖ / (2 * ‖a‖) := div_le_div_of_nonneg_right hstep (by linarith)
    _ = 16 * s ^ 2 := by field_simp; ring
    _ ≤ 32 * (‖ecalPt a u‖ ^ 2 + ‖a‖ ^ 2) := by
          rw [hs]
          nlinarith [sq_nonneg (‖ecalPt a u‖ - ‖a‖)]

end Work.Implosion.Approx
