import Mathlib
import Submission.Work.Kernels.Kernels
import Submission.Work.Asymptotics.cusp_L_second
import Submission.Work.Asymptotics.thetaC00_second_order
import Submission.Work.Asymptotics.ratio_second_order
import Submission.Work.Residues.ThetaEpt
import Submission.Work.Asymptotics.LogLambdaData_L_eq_Lfun
import Submission.Work.Asymptotics.KhatE1.ratio_third_order

/-!
# Fourth-order cusp expansion of `𝓛`

For every CKMRV logarithm data `ℓ` (Section 2.1.5 of the paper) the function `𝓛 = ℓ.L` has,
on `{1 ≤ Im τ}`, the fourth-order cusp expansion

  `𝓛(τ) = πiτ + 4 log 2 - 8E + 12E² - (32/3)E³ + 6E⁴ + O(‖E‖⁵)`,  `E = e^{πiτ}`.

Since `ℓ.L = Lfun` for every logarithm data (`LogLambdaData_L_eq_Lfun`) and `Lfun = LU` on
`{Im z > 1/2}`, it suffices to expand

  `LU z - πi z = 4 log 2 + 4 log r - 4 log θ`,  `r = θ₂(z/2,z)/2`, `θ = θ₀₀(z)`.

The three ingredients are the fourth-order cusp expansions of `r` (`ratio_fourth_order`),
of `θ` (`thetaC00_fourth_order`) and the Taylor bound `log(1+u) = u - u²/2 + u³/3 - u⁴/4 +
O(u⁵)` (`log_fourth_order`).
-/

open Complex Real
open scoped Topology

namespace Work.Asymptotics.KhatE1

open Work.Kernels.LogLambda.ThetaLower

noncomputable section

/-! ## The three analytic ingredients -/

/-- **Sharp ratio estimate.**  For `z` with `1 ≤ Im z`,
`‖θ(z/2,z)/2 - 1 - exp(π i z)^2‖ ≤ 2 ‖exp(π i z)‖^5`. -/
theorem ratio_fourth_order (z : ℂ) (hz : 1 ≤ z.im) :
    ‖jacobiTheta₂ (z / 2) z / 2 - 1 - Complex.exp (Real.pi * Complex.I * z) ^ 2‖
      ≤ 2 * ‖Complex.exp (Real.pi * Complex.I * z)‖ ^ 5 := by
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
  have ht6 : 2 * t^6 ≤ 2 * t^5 := by
    have h1 : t ≤ 1 := by linarith [ht_le]
    nlinarith [pow_pos ht_pos 5, h1]
  calc ‖jacobiTheta₂ (z / 2) z / 2 - 1 - Complex.exp (Real.pi * Complex.I * z) ^ 2‖
      = ‖∑' k : ℕ, thetaPairSummand z (k+2)‖ := by rw [hkey2]
    _ ≤ ∑' k : ℕ, ‖thetaPairSummand z (k+2)‖ := norm_tsum_le_tsum_norm hnorm_summ
    _ ≤ ∑' k : ℕ, s^(k+2) := Summable.tsum_le_tsum hbound hnorm_summ hgeom
    _ = s^2/(1-s) := htsum_geom
    _ ≤ 2 * t^6 := hs6
    _ ≤ 2 * t^5 := ht6
    _ = 2 * ‖Complex.exp (Real.pi * Complex.I * z)‖ ^ 5 := by rw [hnorm_q]

/-- `e^{-π} ≤ 1/2`. -/
private lemma exp_neg_pi_le_half : Real.exp (-Real.pi) ≤ 1 / 2 := by
  have h2 : (2 : ℝ) < Real.exp 1 := Real.exp_one_gt_two
  have hlt : Real.exp 1 < Real.exp Real.pi :=
    Real.exp_lt_exp.mpr (by linarith [Real.pi_gt_three])
  have hge : (2 : ℝ) ≤ Real.exp Real.pi := (h2.trans hlt).le
  calc Real.exp (-Real.pi) = (Real.exp Real.pi)⁻¹ := Real.exp_neg _
    _ ≤ (2 : ℝ)⁻¹ := inv_anti₀ (by norm_num) hge
    _ = 1 / 2 := by norm_num

/-- **Fourth-order expansion of `θ₀₀`.**  For `z` with `1 ≤ Im z`, writing `q = exp(πiz)`,
`‖θ₀₀(z) - 1 - 2q - 2q⁴‖ ≤ 4 ‖q‖⁵`. -/
theorem thetaC00_fourth_order (z : ℂ) (hz : 1 ≤ z.im) :
    ‖Work.Kernels.LogLambda.thetaC00 z - 1 - 2 * Complex.exp (Real.pi * Complex.I * z)
        - 2 * (Complex.exp (Real.pi * Complex.I * z)) ^ 4‖
      ≤ 4 * ‖Complex.exp (Real.pi * Complex.I * z)‖ ^ 5 := by
  have hy : 0 < z.im := by linarith
  set q : ℂ := Complex.exp (Real.pi * Complex.I * z) with hq
  set r : ℝ := ‖q‖ with hr
  have hr_eq : r = Real.exp (-(Real.pi * z.im)) := by
    rw [hr, hq, Complex.norm_exp]
    congr 1
    rw [show (Real.pi : ℂ) * Complex.I * z = ((Real.pi : ℝ) : ℂ) * (Complex.I * z) by ring]
    rw [Complex.re_ofReal_mul, Complex.I_mul_re]
    ring
  have hr0 : 0 ≤ r := norm_nonneg _
  have hr_half : r ≤ 1 / 2 := by
    rw [hr_eq]
    exact (Real.exp_le_exp.mpr (by nlinarith [hz, Real.pi_pos])).trans exp_neg_pi_le_half
  have hr1 : r ≤ 1 := by linarith
  set F : ℕ → ℂ := fun n => Complex.exp (Real.pi * Complex.I * ((n : ℂ) + 1) ^ 2 * z) with hFdef
  have hsum : HasSum F ((jacobiTheta z - 1) / 2) := hasSum_nat_jacobiTheta hy
  have hSsum : Summable F := hsum.summable
  have hnorm_eq : ∀ m : ℕ, ‖F m‖ = r ^ ((m + 1) ^ 2) := by
    intro m
    have h1 : ‖F m‖ = Real.exp (-(Real.pi * ((m : ℝ) + 1) ^ 2 * z.im)) := by
      rw [hFdef]
      exact Work.Residues.norm_cexp_pi_I_sq_mul' z m
    rw [h1, show ((m : ℝ) + 1) ^ 2 = (((m + 1) ^ 2 : ℕ) : ℝ) by push_cast; ring]
    rw [show -(Real.pi * (((m + 1) ^ 2 : ℕ) : ℝ) * z.im)
        = (((m + 1) ^ 2 : ℕ) : ℝ) * (-(Real.pi * z.im)) by ring]
    rw [Real.exp_nat_mul, hr_eq]
  have hF0 : F 0 = q := by
    rw [hFdef, hq]; congr 1; push_cast; ring
  have hF1 : F 1 = q ^ 4 := by
    rw [hFdef, hq]
    norm_num
    rw [show Real.pi * Complex.I * 4 * z = ((4 : ℕ) : ℂ) * (Real.pi * Complex.I * z) by
      push_cast; ring]
    rw [Complex.exp_nat_mul]
  have hth : jacobiTheta z = 1 + 2 * (∑' n : ℕ, F n) := by
    simpa [hFdef] using jacobiTheta_eq_tsum_nat hy
  have hsplit : (∑' n : ℕ, F n) = F 0 + ∑' n : ℕ, F (n + 1) := hSsum.tsum_eq_zero_add
  have hS1 : Summable (fun n : ℕ => F (n + 1)) :=
    hSsum.comp_injective (fun a b h => Nat.add_right_cancel h)
  have hsplit2 : (∑' n : ℕ, F (n + 1)) = F 1 + ∑' n : ℕ, F (n + 2) :=
    hS1.tsum_eq_zero_add
  have hmain : Work.Kernels.LogLambda.thetaC00 z - 1 - 2 * q - 2 * q ^ 4
      = 2 * (∑' n : ℕ, F (n + 2)) := by
    rw [show Work.Kernels.LogLambda.thetaC00 z = jacobiTheta z from rfl, hth, hsplit, hsplit2,
      hF0, hF1]
    ring
  have hS2 : Summable (fun n : ℕ => F (n + 2)) :=
    hSsum.comp_injective (fun a b h => by omega)
  have hnorm_summ : Summable (fun n : ℕ => ‖F (n + 2)‖) := hS2.norm
  have hr6lt : r ^ 6 < 1 := by
    have h : r ^ 6 ≤ (1 / 2 : ℝ) ^ 6 := pow_le_pow_left₀ hr0 hr_half 6
    norm_num at h ⊢
    linarith
  have hgeom : HasSum (fun n : ℕ => r ^ (6 * n + 9)) (r ^ 9 / (1 - r ^ 6)) := by
    have h := (hasSum_geometric_of_lt_one (show (0 : ℝ) ≤ r ^ 6 by positivity) hr6lt).mul_left
      (r ^ 9)
    have h' : HasSum (fun n : ℕ => r ^ 9 * (r ^ 6) ^ n) (r ^ 9 * (1 - r ^ 6)⁻¹) := h
    rw [div_eq_mul_inv]
    refine h'.congr_fun (fun n => ?_)
    rw [← pow_mul, ← pow_add, show 9 + 6 * n = 6 * n + 9 by ring]
  have hbound : ∀ n : ℕ, ‖F (n + 2)‖ ≤ r ^ (6 * n + 9) := by
    intro n
    rw [hnorm_eq (n + 2)]
    refine pow_le_pow_of_le_one hr0 hr1 ?_
    nlinarith
  have htail : ‖∑' n : ℕ, F (n + 2)‖ ≤ r ^ 9 / (1 - r ^ 6) := by
    refine le_trans (norm_tsum_le_tsum_norm hnorm_summ) ?_
    have h1 : (∑' n : ℕ, ‖F (n + 2)‖) ≤ ∑' n : ℕ, r ^ (6 * n + 9) :=
      Summable.tsum_le_tsum hbound hnorm_summ hgeom.summable
    rw [hgeom.tsum_eq] at h1
    exact h1
  have hr6half : (1 / 2 : ℝ) ≤ 1 - r ^ 6 := by
    have h : r ^ 6 ≤ (1 / 2 : ℝ) ^ 6 := pow_le_pow_left₀ hr0 hr_half 6
    norm_num at h ⊢
    linarith
  have hfin : ‖Work.Kernels.LogLambda.thetaC00 z - 1 - 2 * q - 2 * q ^ 4‖ ≤ 4 * r ^ 5 := by
    rw [hmain, norm_mul, Complex.norm_ofNat]
    have hb : 2 * ‖∑' n : ℕ, F (n + 2)‖ ≤ 2 * (r ^ 9 / (1 - r ^ 6)) := by linarith [htail]
    refine le_trans hb ?_
    rw [show 2 * (r ^ 9 / (1 - r ^ 6)) = 2 * r ^ 9 / (1 - r ^ 6) by ring]
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < 1 - r ^ 6)]
    have h9 : r ^ 9 ≤ r ^ 5 := pow_le_pow_of_le_one hr0 hr1 (by norm_num)
    nlinarith [pow_nonneg hr0 5, h9, hr6half]
  simpa [hq, hr] using hfin

/-- **Taylor bound for `log` to fourth order.**  For `‖u‖ ≤ 1/2`,
`‖log(1+u) - (u - u²/2 + u³/3 - u⁴/4)‖ ≤ ‖u‖⁵`. -/
theorem log_fourth_order (u : ℂ) (hu : ‖u‖ ≤ 1 / 2) :
    ‖Complex.log (1 + u) - (u - u ^ 2 / 2 + u ^ 3 / 3 - u ^ 4 / 4)‖ ≤ ‖u‖ ^ 5 := by
  have hu1 : ‖u‖ < 1 := by linarith
  have h1 : ‖Complex.log (1 + u) - Complex.logTaylor 5 u‖ ≤ ‖u‖ ^ 5 * (1 - ‖u‖)⁻¹ / 5 := by
    have := Complex.norm_log_sub_logTaylor_le 4 hu1
    norm_num at this ⊢
    exact this
  rw [show Complex.logTaylor 5 u = u - u ^ 2 / 2 + u ^ 3 / 3 - u ^ 4 / 4 from by
    simp only [Complex.logTaylor, Finset.sum_range_succ, Finset.sum_range_zero]
    ring] at h1
  have hinv : (1 - ‖u‖)⁻¹ ≤ 2 := by
    rw [inv_le_comm₀ (by linarith) (by norm_num)]
    linarith
  have h5 : (0 : ℝ) ≤ ‖u‖ ^ 5 := by positivity
  have h2 : ‖u‖ ^ 5 * (1 - ‖u‖)⁻¹ / 5 ≤ ‖u‖ ^ 5 := by nlinarith [hinv, h5]
  linarith [h1, h2]

/-! ## The main fourth-order expansion -/

private noncomputable def P4 (w : ℂ) : ℂ := w - w ^ 2 / 2 + w ^ 3 / 3 - w ^ 4 / 4

private noncomputable def Xfun (a b : ℂ) : ℂ :=
  1 - a ^ 2 - b / 2 + a ^ 4 + a ^ 2 * b + b ^ 2 / 3 - a ^ 6
    - (3 / 2) * a ^ 4 * b - a ^ 2 * b ^ 2 - b ^ 3 / 4

private noncomputable def Yvv (a : ℂ) : ℂ := 2 * a + 2 * a ^ 4

private noncomputable def Yfun (a b : ℂ) : ℂ :=
  1 - Yvv a - b / 2 + (Yvv a) ^ 2 + Yvv a * b + b ^ 2 / 3 - (Yvv a) ^ 3
    - (3 / 2) * (Yvv a) ^ 2 * b - Yvv a * b ^ 2 - b ^ 3 / 4

private noncomputable def Wfun (a : ℂ) : ℂ :=
  -4 + 8 * a - 16 * a ^ 2 - 2 * a ^ 3 + 8 * a ^ 4 - 24 * a ^ 5 + (8 / 3) * a ^ 7
    - 16 * a ^ 8 - 4 * a ^ 11

/-- A continuous function of two complex variables is bounded on the square `‖·‖ ≤ K`. -/
private lemma exists_bound_continuous₂ (P : ℂ → ℂ → ℂ)
    (hP : Continuous fun p : ℂ × ℂ => P p.1 p.2) {K : ℝ} (_hK : 0 ≤ K) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ a b : ℂ, ‖a‖ ≤ K → ‖b‖ ≤ K → ‖P a b‖ ≤ C := by
  obtain ⟨C, hC⟩ := (isCompact_closedBall (0 : ℂ) K).prod (isCompact_closedBall (0 : ℂ) K)
    |>.exists_bound_of_continuousOn hP.continuousOn
  refine ⟨max C 0, le_max_right _ _, fun a b ha hb => ?_⟩
  refine le_trans (hC (a, b) ?_) (le_max_left _ _)
  rw [Set.mem_prod]
  exact ⟨by rwa [Metric.mem_closedBall, dist_zero_right],
    by rwa [Metric.mem_closedBall, dist_zero_right]⟩

/-- A continuous function of one complex variable is bounded on `‖·‖ ≤ K`. -/
private lemma exists_bound_continuous₁ (P : ℂ → ℂ) (hP : Continuous P) {K : ℝ} (_hK : 0 ≤ K) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ a : ℂ, ‖a‖ ≤ K → ‖P a‖ ≤ C := by
  obtain ⟨C, hC⟩ := (isCompact_closedBall (0 : ℂ) K).exists_bound_of_continuousOn
    hP.continuousOn
  exact ⟨max C 0, le_max_right _ _, fun a ha =>
    le_trans (hC a (by rwa [Metric.mem_closedBall, dist_zero_right])) (le_max_left _ _)⟩

/-- `e^{-π} ≤ 1/8`. -/
private lemma exp_neg_pi_le_eighth : Real.exp (-Real.pi) ≤ 1 / 8 := by
  have h8 : (8 : ℝ) ≤ Real.exp 3 := by
    have h2 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp 1]
    have hexp : Real.exp 3 = (Real.exp 1) ^ 3 := by
      rw [show (3 : ℝ) = (3 : ℕ) * 1 by norm_num, Real.exp_nat_mul]
    rw [hexp]
    have h := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) h2 3
    norm_num at h
    linarith
  calc Real.exp (-Real.pi) ≤ Real.exp (-3) :=
        Real.exp_le_exp.mpr (by linarith [Real.pi_gt_three])
    _ = (Real.exp 3)⁻¹ := Real.exp_neg 3
    _ ≤ (8 : ℝ)⁻¹ := inv_anti₀ (by norm_num) h8
    _ = 1 / 8 := by norm_num

/-- **Fourth-order cusp expansion of the canonical branch `Lfun`.** -/
theorem Lfun_fourth_order :
    ∃ C : ℝ, 0 < C ∧ ∀ z : ℂ, 1 ≤ z.im →
      ‖Work.Kernels.LogLambda.Lfun z - ((Real.pi : ℂ) * Complex.I * z + 4 * (Real.log 2 : ℂ)
          - 8 * Complex.exp (Real.pi * Complex.I * z)
          + 12 * (Complex.exp (Real.pi * Complex.I * z)) ^ 2
          - (32 / 3 : ℂ) * (Complex.exp (Real.pi * Complex.I * z)) ^ 3
          + 6 * (Complex.exp (Real.pi * Complex.I * z)) ^ 4)‖
        ≤ C * ‖Complex.exp (Real.pi * Complex.I * z)‖ ^ 5 := by
  obtain ⟨CA, hCA0, hCA⟩ :=
    exists_bound_continuous₂ Xfun (by unfold Xfun; fun_prop) (K := 1 / 2) (by norm_num)
  obtain ⟨CY, hCY0, hCY⟩ :=
    exists_bound_continuous₂ Yfun (by unfold Yfun Yvv; fun_prop) (K := 1 / 2) (by norm_num)
  obtain ⟨CW, hCW0, hCW⟩ :=
    exists_bound_continuous₁ Wfun (by unfold Wfun; fun_prop) (K := 1 / 2) (by norm_num)
  refine ⟨4 * ((32 + 2 * CA + 1) + (32768 + 4 * CY + CW)), ?_, fun z hz => ?_⟩
  · linarith [hCA0, hCY0, hCW0]
  · have hzW : z ∈ Work.Kernels.LogLambda.W := by
      show (1 / 2 : ℝ) < z.im
      linarith
    set q : ℂ := Complex.exp (Real.pi * Complex.I * z) with hq
    set r : ℂ := jacobiTheta₂ (z / 2) z / 2 with hr
    set th : ℂ := Work.Kernels.LogLambda.thetaC00 z with hth
    set s : ℝ := ‖q‖ with hs
    have hs_q : s = Real.exp (-(Real.pi * z.im)) := by
      rw [hs, hq, Complex.norm_exp]
      congr 1
      rw [show (Real.pi : ℂ) * Complex.I * z = ((Real.pi : ℝ) : ℂ) * (Complex.I * z) by ring]
      rw [Complex.re_ofReal_mul, Complex.I_mul_re]
      ring
    have hs0 : 0 ≤ s := norm_nonneg _
    have hs8 : s ≤ 1 / 8 := by
      rw [hs_q]
      exact (Real.exp_le_exp.mpr (by nlinarith [Real.pi_pos, hz])).trans exp_neg_pi_le_eighth
    have hs_half : s ≤ 1 / 2 := by linarith
    have hs1 : s ≤ 1 := by linarith
    have hq_half : ‖q‖ ≤ 1 / 2 := by rw [← hs]; exact hs_half
    have hLU : Work.Kernels.LogLambda.LU z - (Real.pi : ℂ) * Complex.I * z
        = 4 * (Real.log 2 : ℂ) + 4 * Complex.log r - 4 * Complex.log th := by
      rw [Work.Kernels.LogLambda.LU, Work.Kernels.LogLambda.thetaC10_div_exp]
      simp only [hr, hth, Work.Kernels.LogLambda.thetaC00]
      ring
    set rho : ℂ := r - 1 - q ^ 2 with hrhodef
    set sig : ℂ := th - 1 - 2 * q - 2 * q ^ 4 with hsigdef
    have hrho : ‖rho‖ ≤ 2 * s ^ 5 := by
      rw [hrhodef]
      simpa [hr, hq, hs] using ratio_fourth_order z hz
    have hsig : ‖sig‖ ≤ 4 * s ^ 5 := by
      rw [hsigdef]
      simpa [hth, hq, hs] using thetaC00_fourth_order z hz
    set u1 : ℂ := q ^ 2 + rho with hu1def
    set vv : ℂ := 2 * q + 2 * q ^ 4 with hvdef
    set u2 : ℂ := vv + sig with hu2def
    have hr1 : 1 + u1 = r := by rw [hu1def, hrhodef]; ring
    have hth1 : 1 + u2 = th := by rw [hu2def, hvdef, hsigdef]; ring
    have hu1_le : ‖u1‖ ≤ 2 * s ^ 2 := by
      rw [hu1def]
      calc ‖q ^ 2 + rho‖ ≤ ‖q ^ 2‖ + ‖rho‖ := norm_add_le _ _
        _ = s ^ 2 + ‖rho‖ := by rw [norm_pow, hs]
        _ ≤ s ^ 2 + 2 * s ^ 5 := by linarith [hrho]
        _ ≤ 2 * s ^ 2 := by
            have h3 : s ^ 3 ≤ (1 / 8 : ℝ) ^ 3 := pow_le_pow_left₀ hs0 hs8 3
            have h5 : s ^ 5 = s ^ 2 * s ^ 3 := by ring
            nlinarith [h3, pow_nonneg hs0 2]
    have hu1_half : ‖u1‖ ≤ 1 / 2 := by
      have h : s ^ 2 ≤ (1 / 2 : ℝ) ^ 2 := pow_le_pow_left₀ hs0 hs_half 2
      nlinarith [hu1_le, h]
    have hu2_le : ‖u2‖ ≤ 2 * s + 2 * s ^ 4 + 4 * s ^ 5 := by
      rw [hu2def, hvdef]
      calc ‖2 * q + 2 * q ^ 4 + sig‖ ≤ ‖2 * q + 2 * q ^ 4‖ + ‖sig‖ := norm_add_le _ _
        _ ≤ (2 * s + 2 * s ^ 4) + 4 * s ^ 5 := by
            have h1 : ‖2 * q + 2 * q ^ 4‖ ≤ 2 * s + 2 * s ^ 4 := by
              calc ‖2 * q + 2 * q ^ 4‖ ≤ ‖2 * q‖ + ‖2 * q ^ 4‖ := norm_add_le _ _
                _ = 2 * s + 2 * s ^ 4 := by
                    simp only [norm_mul, Complex.norm_ofNat, norm_pow, hs]
            linarith [h1, hsig]
    have hu2_le8 : ‖u2‖ ≤ 8 * s := by
      refine le_trans hu2_le ?_
      have h4 : s ^ 4 ≤ s := by
        simpa using pow_le_pow_of_le_one hs0 hs1 (by norm_num : (1 : ℕ) ≤ 4)
      have h5 : s ^ 5 ≤ s := by
        simpa using pow_le_pow_of_le_one hs0 hs1 (by norm_num : (1 : ℕ) ≤ 5)
      linarith
    have hu2_half : ‖u2‖ ≤ 1 / 2 := by
      have h4 : s ^ 4 ≤ (1 / 8 : ℝ) ^ 4 := pow_le_pow_left₀ hs0 hs8 4
      have h5 : s ^ 5 ≤ (1 / 8 : ℝ) ^ 5 := pow_le_pow_left₀ hs0 hs8 5
      norm_num at h4 h5
      nlinarith [hu2_le, h4, h5, hs8]
    -- ## Bounding `log r`
    have hlogr := log_fourth_order u1 hu1_half
    have hlogr' : ‖Complex.log r - P4 u1‖ ≤ 32 * s ^ 5 := by
      have h5 : ‖u1‖ ^ 5 ≤ 32 * s ^ 5 := by
        have h := pow_le_pow_left₀ (norm_nonneg u1) hu1_le 5
        have h2 : (2 * s ^ 2) ^ 5 = 32 * s ^ 10 := by ring
        rw [h2] at h
        have h10 : s ^ 10 ≤ s ^ 5 :=
          pow_le_pow_of_le_one hs0 hs1 (by norm_num : (5 : ℕ) ≤ 10)
        linarith [h, h10]
      have hlogr2 : ‖Complex.log r - P4 u1‖ ≤ ‖u1‖ ^ 5 := by
        rw [show P4 u1 = u1 - u1 ^ 2 / 2 + u1 ^ 3 / 3 - u1 ^ 4 / 4 from rfl, ← hr1]
        exact hlogr
      linarith [hlogr2, h5]
    have hA : ‖Complex.log r - (q ^ 2 - q ^ 4 / 2)‖ ≤ (32 + 2 * CA + 1) * s ^ 5 := by
      have hP4q : P4 (q ^ 2) = q ^ 2 - q ^ 4 / 2 + q ^ 6 / 3 - q ^ 8 / 4 := by
        simp only [P4]; ring
      have hid : Complex.log r - (q ^ 2 - q ^ 4 / 2)
          = (Complex.log r - P4 u1) + (P4 u1 - P4 (q ^ 2)) + (q ^ 6 / 3 - q ^ 8 / 4) := by
        rw [hP4q]; ring
      rw [hid]
      have hmid : ‖P4 u1 - P4 (q ^ 2)‖ ≤ 2 * CA * s ^ 5 := by
        have hidX : P4 u1 - P4 (q ^ 2) = rho * Xfun q rho := by
          rw [hu1def]; simp only [P4, Xfun]; ring
        rw [hidX, norm_mul]
        have hrhohalf : ‖rho‖ ≤ 1 / 2 := by
          have h : s ^ 5 ≤ (1 / 8 : ℝ) ^ 5 := pow_le_pow_left₀ hs0 hs8 5
          norm_num at h
          nlinarith [hrho, h]
        calc ‖rho‖ * ‖Xfun q rho‖ ≤ (2 * s ^ 5) * CA :=
              mul_le_mul hrho (hCA q rho hq_half hrhohalf) (norm_nonneg _) (by positivity)
          _ = 2 * CA * s ^ 5 := by ring
      have hlast : ‖q ^ 6 / 3 - q ^ 8 / 4‖ ≤ s ^ 5 := by
        calc ‖q ^ 6 / 3 - q ^ 8 / 4‖ ≤ ‖q ^ 6 / 3‖ + ‖q ^ 8 / 4‖ := norm_sub_le _ _
          _ = s ^ 6 / 3 + s ^ 8 / 4 := by
              simp only [norm_div, norm_pow, Complex.norm_ofNat, hs]
          _ ≤ s ^ 5 := by
              have h6 : s ^ 6 ≤ s ^ 5 := pow_le_pow_of_le_one hs0 hs1 (by norm_num)
              have h8 : s ^ 8 ≤ s ^ 5 := pow_le_pow_of_le_one hs0 hs1 (by norm_num)
              nlinarith [h6, h8]
      calc ‖(Complex.log r - P4 u1) + (P4 u1 - P4 (q ^ 2)) + (q ^ 6 / 3 - q ^ 8 / 4)‖
          ≤ ‖Complex.log r - P4 u1‖ + ‖P4 u1 - P4 (q ^ 2)‖ + ‖q ^ 6 / 3 - q ^ 8 / 4‖ := by
            have h1 := norm_add_le ((Complex.log r - P4 u1) + (P4 u1 - P4 (q ^ 2)))
              (q ^ 6 / 3 - q ^ 8 / 4)
            have h2 := norm_add_le (Complex.log r - P4 u1) (P4 u1 - P4 (q ^ 2))
            linarith
        _ ≤ 32 * s ^ 5 + 2 * CA * s ^ 5 + s ^ 5 := by linarith [hlogr', hmid, hlast]
        _ = (32 + 2 * CA + 1) * s ^ 5 := by ring
    -- ## Bounding `log θ`
    have hlogt := log_fourth_order u2 hu2_half
    have hlogt' : ‖Complex.log th - P4 u2‖ ≤ 32768 * s ^ 5 := by
      have h8s : ‖u2‖ ^ 5 ≤ 32768 * s ^ 5 := by
        have h := pow_le_pow_left₀ (norm_nonneg u2) hu2_le8 5
        have h2 : (8 * s) ^ 5 = 32768 * s ^ 5 := by ring
        rw [h2] at h
        exact h
      have hlogt2 : ‖Complex.log th - P4 u2‖ ≤ ‖u2‖ ^ 5 := by
        rw [show P4 u2 = u2 - u2 ^ 2 / 2 + u2 ^ 3 / 3 - u2 ^ 4 / 4 from rfl, ← hth1]
        exact hlogt
      linarith [hlogt2, h8s]
    have hB : ‖Complex.log th - (2 * q - 2 * q ^ 2 + (8 / 3) * q ^ 3 - 2 * q ^ 4)‖
        ≤ (32768 + 4 * CY + CW) * s ^ 5 := by
      have hP4v : P4 vv - (2 * q - 2 * q ^ 2 + (8 / 3) * q ^ 3 - 2 * q ^ 4)
          = q ^ 5 * Wfun q := by
        rw [hvdef]; simp only [P4, Yvv, Wfun]; ring
      have hid : Complex.log th - (2 * q - 2 * q ^ 2 + (8 / 3) * q ^ 3 - 2 * q ^ 4)
          = (Complex.log th - P4 u2) + (P4 u2 - P4 vv)
            + (P4 vv - (2 * q - 2 * q ^ 2 + (8 / 3) * q ^ 3 - 2 * q ^ 4)) := by ring
      rw [hid, hP4v]
      have hmid : ‖P4 u2 - P4 vv‖ ≤ 4 * CY * s ^ 5 := by
        have hidY : P4 u2 - P4 vv = sig * Yfun q sig := by
          rw [hu2def, hvdef]; simp only [P4, Yvv, Yfun]; ring
        rw [hidY, norm_mul]
        have hsighalf : ‖sig‖ ≤ 1 / 2 := by
          have h : s ^ 5 ≤ (1 / 8 : ℝ) ^ 5 := pow_le_pow_left₀ hs0 hs8 5
          norm_num at h
          nlinarith [hsig, h]
        calc ‖sig‖ * ‖Yfun q sig‖ ≤ (4 * s ^ 5) * CY :=
              mul_le_mul hsig (hCY q sig hq_half hsighalf) (norm_nonneg _) (by positivity)
          _ = 4 * CY * s ^ 5 := by ring
      have hlast : ‖q ^ 5 * Wfun q‖ ≤ CW * s ^ 5 := by
        rw [norm_mul]
        have hq5 : ‖q ^ 5‖ = s ^ 5 := by rw [norm_pow, hs]
        calc ‖q ^ 5‖ * ‖Wfun q‖ ≤ s ^ 5 * CW :=
              mul_le_mul (le_of_eq hq5) (hCW q hq_half) (norm_nonneg _) (by positivity)
          _ = CW * s ^ 5 := by ring
      calc ‖(Complex.log th - P4 u2) + (P4 u2 - P4 vv) + (q ^ 5 * Wfun q)‖
          ≤ ‖Complex.log th - P4 u2‖ + ‖P4 u2 - P4 vv‖ + ‖q ^ 5 * Wfun q‖ := by
            have h1 := norm_add_le ((Complex.log th - P4 u2) + (P4 u2 - P4 vv))
              (q ^ 5 * Wfun q)
            have h2 := norm_add_le (Complex.log th - P4 u2) (P4 u2 - P4 vv)
            linarith
        _ ≤ 32768 * s ^ 5 + 4 * CY * s ^ 5 + CW * s ^ 5 := by linarith [hlogt', hmid, hlast]
        _ = (32768 + 4 * CY + CW) * s ^ 5 := by ring
    -- ## Assembly
    have hAB : ‖4 * Complex.log r - 4 * Complex.log th + 8 * q - 12 * q ^ 2
          + (32 / 3 : ℂ) * q ^ 3 - 6 * q ^ 4‖
        ≤ 4 * ((32 + 2 * CA + 1) * s ^ 5) + 4 * ((32768 + 4 * CY + CW) * s ^ 5) := by
      have hid2 : 4 * Complex.log r - 4 * Complex.log th + 8 * q - 12 * q ^ 2
            + (32 / 3 : ℂ) * q ^ 3 - 6 * q ^ 4
          = 4 * (Complex.log r - (q ^ 2 - q ^ 4 / 2))
            - 4 * (Complex.log th - (2 * q - 2 * q ^ 2 + (8 / 3) * q ^ 3 - 2 * q ^ 4)) := by
        ring
      rw [hid2]
      calc ‖4 * (Complex.log r - (q ^ 2 - q ^ 4 / 2))
              - 4 * (Complex.log th - (2 * q - 2 * q ^ 2 + (8 / 3) * q ^ 3 - 2 * q ^ 4))‖
          ≤ ‖4 * (Complex.log r - (q ^ 2 - q ^ 4 / 2))‖
            + ‖4 * (Complex.log th - (2 * q - 2 * q ^ 2 + (8 / 3) * q ^ 3 - 2 * q ^ 4))‖ :=
              norm_sub_le _ _
        _ = 4 * ‖Complex.log r - (q ^ 2 - q ^ 4 / 2)‖
            + 4 * ‖Complex.log th - (2 * q - 2 * q ^ 2 + (8 / 3) * q ^ 3 - 2 * q ^ 4)‖ := by
              simp only [norm_mul, Complex.norm_ofNat]
        _ ≤ 4 * ((32 + 2 * CA + 1) * s ^ 5) + 4 * ((32768 + 4 * CY + CW) * s ^ 5) := by
              linarith [hA, hB]
    have hLUeq : Work.Kernels.LogLambda.Lfun z = Work.Kernels.LogLambda.LU z :=
      Work.Kernels.LogLambda.Lfun_eq_LU_on_W z hzW
    have hkey : Work.Kernels.LogLambda.Lfun z
        - ((Real.pi : ℂ) * Complex.I * z + 4 * (Real.log 2 : ℂ)
            - 8 * q + 12 * q ^ 2 - (32 / 3 : ℂ) * q ^ 3 + 6 * q ^ 4)
        = 4 * Complex.log r - 4 * Complex.log th + 8 * q - 12 * q ^ 2
            + (32 / 3 : ℂ) * q ^ 3 - 6 * q ^ 4 := by
      have hre : Work.Kernels.LogLambda.LU z
          - ((Real.pi : ℂ) * Complex.I * z + 4 * (Real.log 2 : ℂ)
              - 8 * q + 12 * q ^ 2 - (32 / 3 : ℂ) * q ^ 3 + 6 * q ^ 4)
          = (Work.Kernels.LogLambda.LU z - (Real.pi : ℂ) * Complex.I * z)
              - 4 * (Real.log 2 : ℂ) + 8 * q - 12 * q ^ 2 + (32 / 3 : ℂ) * q ^ 3
              - 6 * q ^ 4 := by ring
      rw [hLUeq, hre, hLU]; ring
    rw [hkey]
    calc ‖4 * Complex.log r - 4 * Complex.log th + 8 * q - 12 * q ^ 2
            + (32 / 3 : ℂ) * q ^ 3 - 6 * q ^ 4‖
        ≤ 4 * ((32 + 2 * CA + 1) * s ^ 5) + 4 * ((32768 + 4 * CY + CW) * s ^ 5) := hAB
      _ = 4 * ((32 + 2 * CA + 1) + (32768 + 4 * CY + CW)) * s ^ 5 := by ring
      _ = 4 * ((32 + 2 * CA + 1) + (32768 + 4 * CY + CW))
            * ‖Complex.exp (Real.pi * Complex.I * z)‖ ^ 5 := by rw [← hq, ← hs]

/-- **The fourth-order cusp expansion of `𝓛`.** -/
theorem cusp_L_fourth (ℓ : Work.Kernels.LogLambdaData) :
    ∃ C : ℝ, 0 < C ∧ ∀ z : UpperHalfPlane, 1 ≤ z.im →
      ‖ℓ.L z - ((Real.pi : ℂ) * Complex.I * (z : ℂ) + 4 * (Real.log 2 : ℂ)
          - 8 * Work.Residues.Ept z + 12 * (Work.Residues.Ept z) ^ 2
          - (32 / 3 : ℂ) * (Work.Residues.Ept z) ^ 3
          + 6 * (Work.Residues.Ept z) ^ 4)‖
        ≤ C * ‖Work.Residues.Ept z‖ ^ 5 := by
  obtain ⟨C, hC, hb⟩ := Lfun_fourth_order
  refine ⟨C, hC, fun z hz => ?_⟩
  have h1 := hb (z : ℂ) hz
  have h2 : ℓ.L z = Work.Kernels.LogLambda.Lfun (z : ℂ) :=
    Work.Asymptotics.LogLambdaData_L_eq_Lfun ℓ z
  rw [h2]
  simpa only [Work.Residues.Ept_apply] using h1

end

end Work.Asymptotics.KhatE1
