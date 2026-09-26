import Mathlib
import Submission.Work.Asymptotics.ratio_second_order

/-!
# Third-order asymptotics of `θ(z/2,z)/2` at the cusp

Sharper form of `ratio_second_order`: the remainder of the series
`θ(z/2,z)/2 - 1 = ∑_{k ≥ 1} e^{πiz(k²+k)}` starts at `k = 2`, i.e. at `e^{6πiz}`,
so it is `O(‖e^{πiz}‖⁴)` (indeed `O(‖e^{πiz}‖⁶)`) rather than `O(‖e^{πiz}‖³)`.
-/

open Complex Real
open scoped Topology

namespace Work.Asymptotics

open Work.Kernels.LogLambda.ThetaLower

noncomputable section

/-- **Third order ratio estimate.**  For `z` with `1 ≤ Im z`,
`‖θ(z/2,z)/2 - 1 - exp(π i z)^2‖ ≤ 2 ‖exp(π i z)‖^4`. -/
theorem ratio_third_order (z : ℂ) (hz : 1 ≤ z.im) :
    ‖jacobiTheta₂ (z / 2) z / 2 - 1 - Complex.exp (Real.pi * Complex.I * z) ^ 2‖
      ≤ 2 * ‖Complex.exp (Real.pi * Complex.I * z)‖ ^ 4 := by
  have hzpos : 0 < z.im := lt_of_lt_of_le zero_lt_one hz
  have hjac : Summable (fun n : ℤ => jacobiTheta₂_term n (z / 2) z) :=
    (summable_jacobiTheta₂_term_iff (z / 2) z).mpr hzpos
  have hu : Summable (thetaSummand z) := hjac.congr (fun n => jacobiTheta₂_term_half z n)
  have hw : Summable (thetaPairSummand z) :=
    (hu.comp_injective Nat.cast_injective).congr (fun k => thetaSummand_ofNat z k)
  have h1 : HasSum (fun k : ℕ => thetaSummand z (k : ℤ)) (∑' k : ℕ, thetaPairSummand z k) :=
    hw.hasSum.congr_fun (fun k => thetaSummand_ofNat z k)
  have h2 : HasSum (fun m : ℕ => thetaSummand z (-((m : ℤ) + 1)))
      (∑' k : ℕ, thetaPairSummand z k) :=
    hw.hasSum.congr_fun (fun m => thetaSummand_negSucc z m)
  have hsum_u : HasSum (thetaSummand z)
      ((∑' k : ℕ, thetaPairSummand z k) + (∑' k : ℕ, thetaPairSummand z k)) :=
    HasSum.of_nat_of_neg_add_one h1 h2
  have hU : (∑' n : ℤ, thetaSummand z n)
      = (∑' k : ℕ, thetaPairSummand z k) + (∑' k : ℕ, thetaPairSummand z k) := hsum_u.tsum_eq
  have hS : jacobiTheta₂ (z / 2) z / 2 = (∑' n : ℤ, thetaSummand z n) / 2 := by
    rw [jacobiTheta₂]
    congr 1
    exact tsum_congr (fun n => jacobiTheta₂_term_half z n)
  have hS2 : jacobiTheta₂ (z / 2) z / 2 = ∑' k : ℕ, thetaPairSummand z k := by
    rw [hS, hU]; ring
  have hpair_zero : thetaPairSummand z 0 = 1 := by simp [thetaPairSummand]
  have hsplit : (∑' k : ℕ, thetaPairSummand z k) = 1 + ∑' k : ℕ, thetaPairSummand z (k + 1) := by
    rw [hw.tsum_eq_zero_add, hpair_zero]
  have hkey : jacobiTheta₂ (z / 2) z / 2 - 1 = ∑' k : ℕ, thetaPairSummand z (k + 1) := by
    rw [hS2, hsplit]; ring
  have hw1 : Summable (fun k : ℕ => thetaPairSummand z (k+1)) :=
    hw.comp_injective (fun a b h => Nat.add_right_cancel h)
  have hsplit2 : (∑' k : ℕ, thetaPairSummand z (k + 1)) =
      thetaPairSummand z 1 + ∑' k : ℕ, thetaPairSummand z (k + 2) := by
    rw [hw1.tsum_eq_zero_add]
  have hq1 : thetaPairSummand z 1 = Complex.exp (Real.pi * Complex.I * z) ^ 2 := by
    simp only [thetaPairSummand]
    rw [← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  have hkey2 : jacobiTheta₂ (z / 2) z / 2 - 1 - Complex.exp (Real.pi * Complex.I * z) ^ 2
      = ∑' k : ℕ, thetaPairSummand z (k + 2) := by
    rw [hkey, hsplit2, hq1]
    ring
  set t : ℝ := Real.exp (-(Real.pi * z.im)) with ht
  set s : ℝ := Real.exp (-(3 * Real.pi * z.im)) with hs
  have hnorm_q : ‖Complex.exp (Real.pi * Complex.I * z)‖ = t := by
    rw [Complex.norm_exp, ht]
    congr 1
    simp [Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im]
  have hst : s = t^3 := by
    rw [hs, ht, ← Real.exp_nat_mul]
    congr 1
    ring
  have ht_pos : 0 < t := by rw [ht]; positivity
  have ht_le : t ≤ (1/4:ℝ) := by
    rw [ht]
    calc Real.exp (-(Real.pi * z.im)) ≤ Real.exp (-(3:ℝ)) := by
          apply Real.exp_le_exp.mpr
          have h3 : 3 ≤ Real.pi * z.im := by nlinarith [Real.pi_gt_three, hz, Real.pi_pos]
          linarith
      _ ≤ 1/4 := by
          have h : (4:ℝ) ≤ Real.exp 3 := by
            have hh := Real.add_one_le_exp 3
            norm_num at hh
            exact hh
          rw [Real.exp_neg, show (1/4:ℝ) = (4:ℝ)⁻¹ by norm_num,
              inv_le_inv₀ (Real.exp_pos 3) (by norm_num : (0:ℝ) < 4)]
          exact h
  have hs_le : s ≤ 1/64 := by
    rw [hst]
    calc t^3 ≤ (1/4:ℝ)^3 := pow_le_pow_left₀ ht_pos.le ht_le 3
      _ = 1/64 := by norm_num
  have hs0 : 0 ≤ s := by rw [hs]; positivity
  have hs1 : s < 1 := by linarith [hs_le]
  have hw2 : Summable (fun k : ℕ => thetaPairSummand z (k+2)) :=
    hw.comp_injective (fun a b h => by omega)
  have hnorm_summ : Summable (fun k : ℕ => ‖thetaPairSummand z (k+2)‖) := hw2.norm
  have hgeom : Summable (fun k : ℕ => s^(k+2)) :=
    (summable_geometric_of_lt_one hs0 hs1).comp_injective (fun a b h => by omega)
  have hbound : ∀ k : ℕ, ‖thetaPairSummand z (k+2)‖ ≤ s^(k+2) := by
    intro k
    rw [norm_thetaPairSummand, hs, ← Real.exp_nat_mul, Real.exp_le_exp]
    push_cast
    have hk : (0:ℝ) ≤ (k:ℝ) := Nat.cast_nonneg k
    have hpi : (0:ℝ) < Real.pi * z.im := by positivity
    have hprod : (0:ℝ) ≤ (Real.pi * z.im) * ((↑k + 2) * (↑k + 2 - 2)) :=
      mul_nonneg hpi.le (mul_nonneg (by linarith) (by linarith))
    nlinarith [hprod]
  have htsum_geom : (∑' k : ℕ, s^(k+2)) = s^2/(1-s) := by
    have h1 : HasSum (fun k : ℕ => s^(k+2)) ((1-s)⁻¹ * s^2) :=
      (hasSum_geometric_of_lt_one hs0 hs1).mul_right (s^2) |>.congr_fun (fun k => by rw [pow_add])
    rw [h1.tsum_eq, div_eq_mul_inv, mul_comm]
  have hs6 : s^2/(1-s) ≤ 2 * t^6 := by
    have hpos : 0 < 1 - s := by linarith [hs1]
    rw [div_le_iff₀ hpos]
    rw [hst]
    have ht3 : t^3 ≤ 1/2 := by
      have h := pow_le_pow_left₀ ht_pos.le ht_le 3
      norm_num at h ⊢
      linarith
    nlinarith [pow_pos ht_pos 6, ht3]
  have ht6 : 2 * t^6 ≤ 2 * t^4 := by
    have h1 : t^2 ≤ 1 := by nlinarith [ht_le, ht_pos]
    nlinarith [pow_pos ht_pos 4, h1]
  calc ‖jacobiTheta₂ (z / 2) z / 2 - 1 - Complex.exp (Real.pi * Complex.I * z) ^ 2‖
      = ‖∑' k : ℕ, thetaPairSummand z (k+2)‖ := by rw [hkey2]
    _ ≤ ∑' k : ℕ, ‖thetaPairSummand z (k+2)‖ := norm_tsum_le_tsum_norm hnorm_summ
    _ ≤ ∑' k : ℕ, s^(k+2) := Summable.tsum_le_tsum hbound hnorm_summ hgeom
    _ = s^2/(1-s) := htsum_geom
    _ ≤ 2 * t^6 := hs6
    _ ≤ 2 * t^4 := ht6
    _ = 2 * ‖Complex.exp (Real.pi * Complex.I * z)‖ ^ 4 := by rw [hnorm_q]

end

end Work.Asymptotics
