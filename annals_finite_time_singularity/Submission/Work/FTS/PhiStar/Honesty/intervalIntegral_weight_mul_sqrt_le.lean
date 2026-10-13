import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Submission.Work.FTS.PhiStar.Honesty.sq_intervalIntegral_mul_le

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.PhiStar.Honesty

/-- Elementary bridge between the square root and the real power: for `x ≥ 0`,
`√(x³) = x^{3/2}`. -/
private lemma sqrt_cube_eq_rpow {x : ℝ} (hx : 0 ≤ x) :
    Real.sqrt (x ^ (3 : ℕ)) = x ^ ((3 : ℝ) / 2) := by
  have h : x ^ (3 : ℕ) = (x ^ ((3 : ℝ) / 2)) ^ (2 : ℕ) := by
    rw [show x ^ (3 : ℕ) = x ^ (3 : ℝ) from (Real.rpow_natCast x 3).symm,
      show (x ^ ((3 : ℝ) / 2)) ^ (2 : ℕ) = (x ^ ((3 : ℝ) / 2)) ^ (2 : ℝ) from
        (Real.rpow_natCast _ 2).symm,
      ← Real.rpow_mul hx (3 / 2) 2]
    norm_num
  exact (Real.sqrt_eq_iff_eq_sq (pow_nonneg hx 3) (Real.rpow_nonneg hx _)).mpr h

/-- Weighted Cauchy–Schwarz on an interval: for `0 < y ≤ x` and `A ≥ 0` with `√A` and `A`
interval integrable on `[y, x]`,
`∫_y^x (t/(1+t)²)·√(A t) ≤ x^{3/2}·√(∫_y^x A t)`.

The weight satisfies `0 ≤ t/(1+t)² ≤ x` and hence `∫_y^x (t/(1+t)²)² ≤ x³`, so the claim
follows from Cauchy–Schwarz. -/
theorem intervalIntegral_weight_mul_sqrt_le {A : ℝ → ℝ} {x y : ℝ}
    (hy : 0 < y) (hyx : y ≤ x) (hAnn : ∀ t, 0 ≤ A t)
    (hAint : IntervalIntegrable A MeasureTheory.volume y x)
    (hsqrtint : IntervalIntegrable (fun t : ℝ => Real.sqrt (A t)) MeasureTheory.volume y x) :
    (∫ t in y..x, (t / (1 + t) ^ 2) * Real.sqrt (A t))
      ≤ x ^ ((3 : ℝ) / 2) * Real.sqrt (∫ t in y..x, A t) := by
  have hx : 0 < x := lt_of_lt_of_le hy hyx
  set w : ℝ → ℝ := fun t => t / (1 + t) ^ 2 with hw
  have hwcont : ContinuousOn w (Set.uIcc y x) := by
    rw [hw, Set.uIcc_of_le hyx]
    refine ContinuousOn.div continuous_id.continuousOn ?_ ?_
    · exact ((continuous_const.add continuous_id).pow 2).continuousOn
    · intro t ht
      exact pow_ne_zero 2 (by linarith [ht.1, hy] : (1 : ℝ) + t ≠ 0)
  have hw2 : IntervalIntegrable (fun t : ℝ => w t ^ 2) MeasureTheory.volume y x :=
    (hwcont.pow 2).intervalIntegrable
  have hAsq : (fun t : ℝ => (Real.sqrt (A t)) ^ 2) = A := by
    funext t
    exact Real.sq_sqrt (hAnn t)
  have hg2 : IntervalIntegrable (fun t : ℝ => (Real.sqrt (A t)) ^ 2) MeasureTheory.volume y x := by
    rw [hAsq]
    exact hAint
  have hprod : IntervalIntegrable (fun t : ℝ => w t * Real.sqrt (A t)) MeasureTheory.volume y x :=
    hsqrtint.continuousOn_mul hwcont
  have hF0 : 0 ≤ ∫ t in y..x, w t * Real.sqrt (A t) := by
    apply intervalIntegral.integral_nonneg hyx
    intro t ht
    have ht0 : 0 ≤ t := le_trans (le_of_lt hy) ht.1
    have hwt : 0 ≤ w t := by
      rw [hw]
      exact div_nonneg ht0 (by positivity)
    exact mul_nonneg hwt (Real.sqrt_nonneg (A t))
  have hJ0 : 0 ≤ ∫ t in y..x, A t :=
    intervalIntegral.integral_nonneg hyx (fun t _ => hAnn t)
  have hK0 : 0 ≤ ∫ t in y..x, w t ^ 2 := by
    apply intervalIntegral.integral_nonneg hyx
    intro t _
    positivity
  have hpt : ∀ t ∈ Set.Icc y x, w t ^ 2 ≤ x ^ 2 := by
    intro t ht
    have ht0 : 0 ≤ t := le_trans (le_of_lt hy) ht.1
    have hden : (0 : ℝ) < (1 + t) ^ 2 := by
      have : (0 : ℝ) < 1 + t := by linarith
      positivity
    have h1 : (1 : ℝ) ≤ (1 + t) ^ 2 := by
      have hlt : (1 : ℝ) ≤ 1 + t := by linarith
      calc (1 : ℝ) = 1 ^ 2 := by norm_num
        _ ≤ (1 + t) ^ 2 := pow_le_pow_left₀ (by norm_num) hlt 2
    have hw0 : 0 ≤ w t := by rw [hw]; exact div_nonneg ht0 (le_of_lt hden)
    have hwt : w t ≤ t := by
      rw [hw, div_le_iff₀ hden]
      nlinarith [ht0, h1]
    exact pow_le_pow_left₀ hw0 (le_trans hwt ht.2) 2
  have hKi : (∫ t in y..x, w t ^ 2) ≤ x ^ (3 : ℕ) := by
    have hx2int : IntervalIntegrable (fun _ : ℝ => x ^ 2) MeasureTheory.volume y x :=
      intervalIntegrable_const
    have hmono := intervalIntegral.integral_mono_on hyx hw2 hx2int hpt
    have hconst : (∫ t in y..x, (fun _ : ℝ => x ^ 2) t) = x ^ 2 * (x - y) := by
      rw [intervalIntegral.integral_const, smul_eq_mul]
      ring
    rw [hconst] at hmono
    have hfin : x ^ 2 * (x - y) ≤ x ^ (3 : ℕ) := by
      have h1 : x ^ 2 * (x - y) ≤ x ^ 2 * x :=
        mul_le_mul_of_nonneg_left (by linarith) (sq_nonneg x)
      have h2 : x ^ 2 * x = x ^ (3 : ℕ) := by ring
      linarith
    linarith
  have hcs := sq_intervalIntegral_mul_le (f := w) (g := fun t : ℝ => Real.sqrt (A t))
    hyx hw2 hg2 hprod
  simp only [hAsq] at hcs
  have hmain : (∫ t in y..x, w t * Real.sqrt (A t))
      ≤ x ^ ((3 : ℝ) / 2) * Real.sqrt (∫ t in y..x, A t) := by
    calc (∫ t in y..x, w t * Real.sqrt (A t))
        = Real.sqrt ((∫ t in y..x, w t * Real.sqrt (A t)) ^ 2) := (Real.sqrt_sq hF0).symm
      _ ≤ Real.sqrt ((∫ t in y..x, w t ^ 2) * (∫ t in y..x, A t)) := Real.sqrt_le_sqrt hcs
      _ = Real.sqrt (∫ t in y..x, w t ^ 2) * Real.sqrt (∫ t in y..x, A t) :=
          Real.sqrt_mul hK0 _
      _ ≤ Real.sqrt (x ^ (3 : ℕ)) * Real.sqrt (∫ t in y..x, A t) :=
          mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt hKi) (Real.sqrt_nonneg _)
      _ = x ^ ((3 : ℝ) / 2) * Real.sqrt (∫ t in y..x, A t) := by
          rw [sqrt_cube_eq_rpow (le_of_lt hx)]
  simpa [hw] using hmain

end Work.FTS.PhiStar.Honesty
