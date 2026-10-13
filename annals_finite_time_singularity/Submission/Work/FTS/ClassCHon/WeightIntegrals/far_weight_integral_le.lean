import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.ClassCHon.RgL2Pointwise

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.ClassCHon.WeightIntegrals

/-!
# The far-field weighted integral bound

We prove

  `∫_{t > z} t ^ (-2P-2) / w(t)^2 ≤ z ^ (-2P) / (2P - 3)`   for `z > 0`, `P > 3/2`,

where `w(t) = (1+t)^2/t^2`.  Since `w(t)^2 = (1+t)^4/t^4`, on `t > 0` the integrand equals
`t ^ (2 - 2 P) / (1 + t) ^ 4`, and the estimate follows by comparing with a pure power:

* if `0 < z ≤ 1`, one has `(1+t)^(-4) ≤ 1`, so the integrand is at most `t^(2-2P)`, and
  `∫_z^∞ t^(2-2P) = z^(3-2P)/(2P-3) ≤ z^(-2P)/(2P-3)`;
* if `1 ≤ z`, one has `t^4/(1+t)^4 ≤ 1`, so the integrand is at most `t^(-2P-2)`, and
  `∫_z^∞ t^(-2P-2) = z^(-2P-1)/(2P+1) ≤ z^(-2P)/(2P-3)`.
-/

/-- Reduction of the far-field integrand to a pure power over a positive denominator:
for `t > 0`, `t^(-2P-2) / w(t)^2 = t^(2-2P) / (1+t)^4`. -/
private lemma rpow_div_w_sq_eq {P t : ℝ} (ht : 0 < t) :
    t ^ (-2 * P - 2) / (Work.Spaces.w t) ^ 2 = t ^ (2 - 2 * P) / (1 + t) ^ 4 := by
  have hinv : ((Work.Spaces.w t) ^ 2)⁻¹ = t ^ 4 / (1 + t) ^ 4 := by
    rw [Work.Spaces.w, div_pow]; field_simp
  have hpow : t ^ (-2 * P - 2) * t ^ 4 = t ^ (2 - 2 * P) := by
    rw [← Real.rpow_natCast t 4, ← Real.rpow_add ht]
    ring_nf
  calc t ^ (-2 * P - 2) / (Work.Spaces.w t) ^ 2
      = t ^ (-2 * P - 2) * ((Work.Spaces.w t) ^ 2)⁻¹ := by rw [div_eq_mul_inv]
    _ = t ^ (-2 * P - 2) * (t ^ 4 / (1 + t) ^ 4) := by rw [hinv]
    _ = t ^ (-2 * P - 2) * t ^ 4 / (1 + t) ^ 4 := by rw [mul_div_assoc]
    _ = t ^ (2 - 2 * P) / (1 + t) ^ 4 := by rw [hpow]

/-- Nonnegativity of the far-field integrand at a nonnegative point. -/
private lemma rpow_div_w_sq_nonneg {P t : ℝ} (ht : 0 ≤ t) :
    0 ≤ t ^ (-2 * P - 2) / (Work.Spaces.w t) ^ 2 :=
  div_nonneg (Real.rpow_nonneg ht _) (sq_nonneg _)

/-- Pointwise domination by the exponent `2 - 2P` (used for `z ≤ 1`). -/
private lemma rpow_div_w_sq_le_hi {P t : ℝ} (ht : 0 < t) :
    t ^ (-2 * P - 2) / (Work.Spaces.w t) ^ 2 ≤ t ^ (2 - 2 * P) := by
  rw [rpow_div_w_sq_eq ht, div_le_iff₀ (pow_pos (by linarith : (0:ℝ) < 1 + t) 4)]
  nth_rewrite 1 [← mul_one (t ^ (2 - 2 * P))]
  exact mul_le_mul_of_nonneg_left (one_le_pow₀ (n := 4) (by linarith))
    (Real.rpow_nonneg ht.le _)

/-- Pointwise domination by the exponent `-2P - 2` (used for `1 ≤ z`). -/
private lemma rpow_div_w_sq_le_lo {P t : ℝ} (ht : 0 < t) :
    t ^ (-2 * P - 2) / (Work.Spaces.w t) ^ 2 ≤ t ^ (-2 * P - 2) := by
  have hpow : t ^ (2 - 2 * P) = t ^ (-2 * P - 2) * t ^ 4 := by
    rw [← Real.rpow_natCast t 4, ← Real.rpow_add ht]
    ring_nf
  rw [rpow_div_w_sq_eq ht, hpow,
    div_le_iff₀ (pow_pos (by linarith : (0:ℝ) < 1 + t) 4)]
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ ht.le (by linarith) 4)
    (Real.rpow_nonneg ht.le _)

theorem far_weight_integral_le {z P : ℝ} (hz : 0 < z) (hP : 3 / 2 < P) :
    ∫ t in Set.Ioi z, t ^ (-2 * P - 2) / (Work.Spaces.w t) ^ 2
      ≤ z ^ (-2 * P) / (2 * P - 3) := by
  have hz0 : (0:ℝ) < 2 * P - 3 := by linarith
  rcases le_total z 1 with hz1 | hz1
  · -- Case `z ≤ 1`: compare with `t ↦ t ^ (2 - 2P)`.
    have hg : MeasureTheory.IntegrableOn (fun t : ℝ => t ^ (2 - 2 * P)) (Set.Ioi z) :=
      integrableOn_Ioi_rpow_of_lt (by linarith) hz
    have hle : (fun t : ℝ => t ^ (-2 * P - 2) / (Work.Spaces.w t) ^ 2)
        ≤ᵐ[MeasureTheory.volume.restrict (Set.Ioi z)] (fun t : ℝ => t ^ (2 - 2 * P)) := by
      filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Ioi] with t ht
      exact rpow_div_w_sq_le_hi (lt_trans hz (Set.mem_Ioi.mp ht))
    have hnn : 0 ≤ᵐ[MeasureTheory.volume.restrict (Set.Ioi z)]
        (fun t : ℝ => t ^ (-2 * P - 2) / (Work.Spaces.w t) ^ 2) := by
      filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Ioi] with t ht
      exact rpow_div_w_sq_nonneg (le_of_lt (lt_trans hz (Set.mem_Ioi.mp ht)))
    calc ∫ t in Set.Ioi z, t ^ (-2 * P - 2) / (Work.Spaces.w t) ^ 2
        ≤ ∫ t in Set.Ioi z, t ^ (2 - 2 * P) :=
          MeasureTheory.integral_mono_of_nonneg hnn hg hle
      _ = z ^ (3 - 2 * P) / (2 * P - 3) := by
          rw [integral_Ioi_rpow_of_lt (a := 2 - 2 * P) (c := z) (by linarith) hz]
          rw [show (2:ℝ) - 2 * P + 1 = 3 - 2 * P from by ring]
          rw [div_eq_div_iff (by linarith : (3:ℝ) - 2 * P ≠ 0) (ne_of_gt hz0)]
          ring
      _ ≤ z ^ (-2 * P) / (2 * P - 3) :=
          div_le_div_of_nonneg_right
            (Real.rpow_le_rpow_of_exponent_ge (x := z) (y := 3 - 2 * P) (z := -2 * P)
              hz hz1 (by linarith)) hz0.le
  · -- Case `1 ≤ z`: compare with `t ↦ t ^ (-2P-2)`.
    have hg : MeasureTheory.IntegrableOn (fun t : ℝ => t ^ (-2 * P - 2)) (Set.Ioi z) :=
      integrableOn_Ioi_rpow_of_lt (by linarith) hz
    have hle : (fun t : ℝ => t ^ (-2 * P - 2) / (Work.Spaces.w t) ^ 2)
        ≤ᵐ[MeasureTheory.volume.restrict (Set.Ioi z)] (fun t : ℝ => t ^ (-2 * P - 2)) := by
      filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Ioi] with t ht
      exact rpow_div_w_sq_le_lo (lt_trans hz (Set.mem_Ioi.mp ht))
    have hnn : 0 ≤ᵐ[MeasureTheory.volume.restrict (Set.Ioi z)]
        (fun t : ℝ => t ^ (-2 * P - 2) / (Work.Spaces.w t) ^ 2) := by
      filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Ioi] with t ht
      exact rpow_div_w_sq_nonneg (le_of_lt (lt_trans hz (Set.mem_Ioi.mp ht)))
    calc ∫ t in Set.Ioi z, t ^ (-2 * P - 2) / (Work.Spaces.w t) ^ 2
        ≤ ∫ t in Set.Ioi z, t ^ (-2 * P - 2) :=
          MeasureTheory.integral_mono_of_nonneg hnn hg hle
      _ = z ^ (-2 * P - 1) / (2 * P + 1) := by
          rw [integral_Ioi_rpow_of_lt (a := -2 * P - 2) (c := z) (by linarith) hz]
          rw [show -2 * P - 2 + 1 = -2 * P - 1 from by ring]
          rw [div_eq_div_iff (by linarith : (-2:ℝ) * P - 1 ≠ 0) (by linarith : (2:ℝ) * P + 1 ≠ 0)]
          ring
      _ ≤ z ^ (-2 * P) / (2 * P - 3) := by
          rw [div_le_div_iff₀ (by linarith : (0:ℝ) < 2 * P + 1) hz0]
          exact mul_le_mul
            (Real.rpow_le_rpow_of_exponent_le hz1 (by linarith)) (by linarith)
            (by linarith) (Real.rpow_nonneg (le_of_lt hz) _)

end Work.FTS.ClassCHon.WeightIntegrals
