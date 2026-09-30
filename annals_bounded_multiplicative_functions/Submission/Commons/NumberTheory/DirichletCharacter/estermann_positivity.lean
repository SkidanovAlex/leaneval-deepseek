import Mathlib.Analysis.Complex.Liouville
import Mathlib.NumberTheory.Harmonic.ZetaAsymp
import Submission.Commons.NumberTheory.Zeta.zeta_eq_emN
import Submission.Commons.NumberTheory.Zeta.emTerm_tsum_le

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

open Complex Metric Filter
open scoped Topology BigOperators
set_option maxHeartbeats 4000000
namespace Commons.NumberTheory.DirichletCharacter
noncomputable section

lemma log_natCast_nonneg (n : ℕ) : 0 ≤ Real.log (n:ℝ) := by
  rcases Nat.eq_zero_or_pos n with h | h
  · subst h; simp
  · exact Real.log_nonneg (by exact_mod_cast h)

lemma logMul_iterate_apply (g : ℕ → ℂ) (k n : ℕ) :
    (LSeries.logMul^[k] g) n = (Complex.log n)^k * g n := by
  induction k generalizing n with
  | zero => simp
  | succ k ih =>
      rw [Function.iterate_succ_apply']
      simp only [ih, LSeries.logMul]
      ring

lemma logMul_term_eq (r : ℕ → ℝ) (k n : ℕ) :
    LSeries.term (LSeries.logMul^[k] (fun n => (r n : ℂ))) 2 n =
      (((Real.log (n:ℝ))^k * r n / (n:ℝ)^2 : ℝ) : ℂ) := by
  rcases eq_or_ne n 0 with rfl | hn
  · rw [LSeries.term_def]; simp [Real.log_zero]
  · rw [LSeries.term_of_ne_zero hn, logMul_iterate_apply]
    rw [← Complex.natCast_log]
    rw [show (2:ℂ) = ((2:ℕ):ℂ) from by norm_num, Complex.cpow_natCast]
    push_cast
    ring

lemma LSeries_logMul_coe_eq (r : ℕ → ℝ) (k : ℕ) :
    LSeries (LSeries.logMul^[k] (fun n => (r n : ℂ))) 2 =
      ((∑' n : ℕ, (Real.log (n:ℝ))^k * r n / (n:ℝ)^2 : ℝ) : ℂ) := by
  rw [show LSeries (LSeries.logMul^[k] (fun n => (r n : ℂ))) 2 =
      ∑' n, LSeries.term (LSeries.logMul^[k] (fun n => (r n : ℂ))) 2 n from rfl]
  rw [tsum_congr (logMul_term_eq r k)]
  rw [← Complex.ofReal_tsum]

lemma dslope_zeta_eq (s : ℂ) (hs : s ≠ 1) :
    dslope riemannZeta₁ 1 s = riemannZeta s - (s-1)⁻¹ := by
  rw [dslope_of_ne _ hs, slope_def_module, riemannZeta_eq_inv_sub_mul hs, riemannZeta₁_one]
  simp only [smul_eq_mul]
  field_simp

lemma iteratedDeriv_inv_one_sub (k : ℕ) :
    iteratedDeriv k (fun w : ℂ => (1 - w)⁻¹) 0 = (Nat.factorial k : ℂ) := by
  have h := iter_deriv_inv_linear_sub (𝕜 := ℂ) k (-1) (-1)
  rw [iteratedDeriv_eq_iterate]
  rw [show (fun w : ℂ => (1 - w)⁻¹) = (fun x => ((-1:ℂ) * x - (-1))⁻¹) from by
    funext x; ring_nf]
  rw [h]
  simp only [Pi.zero_apply]
  rw [show (-1:ℂ)*0 - -1 = 1 by ring, one_zpow, mul_one]
  have h1 : (-1:ℂ)^k * (-1:ℂ)^k = 1 := by
    rw [← pow_two, ← pow_mul]
    exact Even.neg_one_pow ⟨k, by ring⟩
  rw [mul_assoc, mul_comm (↑k.factorial) ((-1:ℂ)^k), ← mul_assoc, h1, one_mul]

lemma H_eq_of_ne_one (f : ℂ → ℂ) {w : ℂ} (hw : w ≠ 1) :
    dslope riemannZeta₁ 1 (2 - w) * f (2 - w) + dslope f 1 (2 - w)
      = riemannZeta (2 - w) * f (2 - w) - f 1 * (1 - w)⁻¹ := by
  have h2w : (2:ℂ) - w ≠ 1 := by intro h; exact hw (by linear_combination -h)
  rw [dslope_zeta_eq (2 - w) h2w, dslope_of_ne f h2w, slope_def_module]
  simp only [smul_eq_mul]
  rw [show (2:ℂ) - w - 1 = 1 - w by ring]
  ring

lemma iteratedDeriv_aux (f : ℂ → ℂ) (hfa : AnalyticOnNhd ℂ f (Metric.closedBall 2 (3/2))) (k : ℕ) :
    iteratedDeriv k (fun w => dslope riemannZeta₁ 1 (2 - w) * f (2 - w) + dslope f 1 (2 - w)) 0
      = (-1)^k * iteratedDeriv k (fun s => riemannZeta s * f s) 2 - f 1 * (Nat.factorial k : ℂ) := by
  rw [Filter.EventuallyEq.iteratedDeriv_eq k (by
    filter_upwards [Metric.ball_mem_nhds (0:ℂ) (by norm_num : (0:ℝ) < 1/2)] with w hw
    have hw' : ‖w‖ < 1/2 := by simpa [mem_ball, dist_eq_norm, sub_zero] using hw
    have hwne : w ≠ 1 := by intro h; rw [h] at hw'; norm_num at hw'
    exact H_eq_of_ne_one f hwne)]
  change iteratedDeriv k ((fun w : ℂ => riemannZeta (2 - w) * f (2 - w)) -
      (fun w : ℂ => f 1 * (1 - w)⁻¹)) 0 = _
  have hFa : AnalyticAt ℂ (fun s => riemannZeta s * f s) 2 :=
    (analyticOn_riemannZeta 2 (by simp)).mul (hfa 2 (mem_closedBall_self (by norm_num)))
  have hcd1 : ContDiffAt ℂ (k : ℕ) (fun w => riemannZeta (2 - w) * f (2 - w)) 0 := by
    have hg : ContDiffAt ℂ (k:ℕ) (fun s => riemannZeta s * f s) ((2:ℂ) - 0) := by
      simpa using hFa.contDiffAt
    have hf : ContDiffAt ℂ (k:ℕ) (fun w : ℂ => (2:ℂ) - w) 0 := by fun_prop
    exact hg.comp 0 hf
  have hcd2 : ContDiffAt ℂ (k : ℕ) (fun w => f 1 * (1 - w)⁻¹) 0 := by
    have h1 : (1:ℂ) - 0 ≠ 0 := by norm_num
    fun_prop
  rw [iteratedDeriv_sub hcd1 hcd2]
  rw [show (fun w : ℂ => riemannZeta (2 - w) * f (2 - w)) =
        (fun w => (fun s => riemannZeta s * f s) (2 - w)) from rfl]
  rw [iteratedDeriv_comp_const_sub k (fun s => riemannZeta s * f s) 2]
  simp only [sub_zero]
  rw [iteratedDeriv_const_mul_field, iteratedDeriv_inv_one_sub]
  simp only [smul_eq_mul]

lemma norm_riemannZeta_le_ten_of_mem_sphere {z : ℂ} (hz : z ∈ Metric.sphere (2:ℂ) (3/2)) :
    ‖riemannZeta z‖ ≤ 10 := by
  have hnorm : ‖z - 2‖ = 3/2 := by simpa [mem_sphere_iff_norm] using hz
  have hre2 : |z.re - 2| ≤ 3/2 := by
    have h := Complex.abs_re_le_norm (z - 2)
    have hre : (z - 2).re = z.re - 2 := by simp
    rw [hre, hnorm] at h
    simpa using h
  have hre_ge : (1/2 : ℝ) ≤ z.re := by rw [abs_le] at hre2; linarith [hre2.1]
  have hre_pos : 0 < z.re := by linarith
  have hzne : z ≠ 1 := by intro h; rw [h] at hnorm; norm_num at hnorm
  have hnormz : ‖z‖ ≤ 7/2 := by
    have h2 : ‖(2:ℂ)‖ = 2 := by norm_num
    calc ‖z‖ = ‖(z - 2) + 2‖ := by ring_nf
      _ ≤ ‖z - 2‖ + ‖(2:ℂ)‖ := norm_add_le _ _
      _ = 7/2 := by rw [hnorm, h2]; norm_num
  have hnorm1 : (1/2 : ℝ) ≤ ‖z - 1‖ := by
    have h := abs_norm_sub_norm_le (z - 2) (-1:ℂ)
    have h1n : ‖(-1:ℂ)‖ = 1 := by norm_num
    have hz1 : (z - 2) - (-1) = z - 1 := by ring
    rw [h1n, hnorm, hz1] at h
    norm_num at h
    exact h
  obtain ⟨hsumm, htail⟩ := Commons.NumberTheory.Zeta.emTerm_tsum_le 1 (by norm_num) z hre_pos hzne
  have hem := Commons.NumberTheory.Zeta.zeta_eq_emN (s := z) hre_pos hzne 1 (by norm_num)
  have hhead : (∑ n ∈ Finset.Icc 1 1, (((n:ℕ):ℂ)^(-z))) = 1 := by simp
  have hbound_tail : ‖(∑' m : ℕ,
        ((((1 + m + 1 : ℕ) : ℂ) ^ (-z)) -
          (((((1 + m + 1 : ℕ) : ℂ) ^ (1 - z)) - (((1 + m : ℕ) : ℂ) ^ (1 - z))) / (1 - z))))‖ ≤ 7 := by
    have h1 : ‖(∑' m : ℕ,
        ((((1 + m + 1 : ℕ) : ℂ) ^ (-z)) -
          (((((1 + m + 1 : ℕ) : ℂ) ^ (1 - z)) - (((1 + m : ℕ) : ℂ) ^ (1 - z))) / (1 - z))))‖ ≤
        ∑' m : ℕ, ‖((((1 + m + 1 : ℕ) : ℂ) ^ (-z)) -
          (((((1 + m + 1 : ℕ) : ℂ) ^ (1 - z)) - (((1 + m : ℕ) : ℂ) ^ (1 - z))) / (1 - z)))‖ :=
      norm_tsum_le_tsum_norm hsumm.norm
    refine le_trans h1 ?_
    refine le_trans htail ?_
    have h2 : ((‖z‖ / z.re) * (((1:ℕ):ℝ) ^ (-z.re))) = ‖z‖ / z.re := by norm_num
    rw [h2]
    rw [div_le_iff₀ hre_pos]
    nlinarith [hnormz, hre_ge]
  have hbound_pole : ‖((((1:ℕ):ℂ) ^ (1 - z)) / (z - 1))‖ ≤ 2 := by
    have hcast : (((1:ℕ):ℂ)) = 1 := by norm_num
    rw [hcast, one_cpow, one_div, norm_inv]
    rw [inv_le_comm₀ (norm_pos_iff.mpr (by
      intro h; have := hnorm1; rw [h] at this; norm_num at this)) (by norm_num : (0:ℝ) < 2)]
    norm_num
    linarith
  have hval : ‖riemannZeta z‖ ≤ 10 := by
    rw [hem]
    have h1 : ‖(∑ n ∈ Finset.Icc 1 1, (((n:ℕ):ℂ)^(-z))) + ((((1:ℕ):ℂ) ^ (1 - z)) / (z - 1)) +
            (∑' m : ℕ, ((((1 + m + 1 : ℕ) : ℂ) ^ (-z)) -
              (((((1 + m + 1 : ℕ) : ℂ) ^ (1 - z)) - (((1 + m : ℕ) : ℂ) ^ (1 - z))) / (1 - z))))‖
        ≤ ‖(∑ n ∈ Finset.Icc 1 1, (((n:ℕ):ℂ)^(-z))) + ((((1:ℕ):ℂ) ^ (1 - z)) / (z - 1))‖ +
          ‖(∑' m : ℕ, ((((1 + m + 1 : ℕ) : ℂ) ^ (-z)) -
              (((((1 + m + 1 : ℕ) : ℂ) ^ (1 - z)) - (((1 + m : ℕ) : ℂ) ^ (1 - z))) / (1 - z))))‖ :=
      norm_add_le _ _
    have h2 : ‖(∑ n ∈ Finset.Icc 1 1, (((n:ℕ):ℂ)^(-z))) + ((((1:ℕ):ℂ) ^ (1 - z)) / (z - 1))‖ ≤ 1 + 2 := by
      refine le_trans (norm_add_le _ _) ?_
      have hh : ‖(∑ n ∈ Finset.Icc 1 1, (((n:ℕ):ℂ)^(-z)))‖ = 1 := by rw [hhead]; norm_num
      have hp : ‖((((1:ℕ):ℂ) ^ (1 - z)) / (z - 1))‖ ≤ 2 := hbound_pole
      linarith
    linarith
  exact hval

lemma three_mul_log_ten_sevenths_ge_one : 1 ≤ 3 * Real.log (10/7) := by
  have h : (1:ℝ) ≤ Real.log ((10/7)^3) := by
    rw [Real.le_log_iff_exp_le (by norm_num : (0:ℝ) < (10/7)^3)]
    exact (lt_trans Real.exp_one_lt_d9 (by norm_num)).le
  rwa [Real.log_pow] at h

lemma rpow_eighty_log_ratio_le : (80:ℝ) ^ (Real.log (21/20) / Real.log (10/7)) ≤ 40/21 := by
  set a : ℝ := Real.log (21/20) with ha
  set bl : ℝ := Real.log (10/7) with hbl
  have hbpos : 0 < bl := Real.log_pos (by norm_num)
  have hale : a ≤ bl / 7 := by
    have h1 : Real.log ((21/20)^7) ≤ Real.log (10/7) :=
      Real.log_le_log (by norm_num) (by norm_num)
    rw [Real.log_pow] at h1
    simp only [Nat.cast_ofNat] at h1
    rw [ha, hbl]
    linarith
  have hl80 : Real.log 80 ≤ 7 * Real.log (40/21) := by
    have h1 : Real.log 80 ≤ Real.log ((40/21)^7) :=
      Real.log_le_log (by norm_num) (by norm_num)
    rwa [Real.log_pow] at h1
  have key : (a / bl) * Real.log 80 ≤ Real.log (40/21) := by
    have h2 : a / bl ≤ 1/7 := by rw [div_le_iff₀ hbpos]; linarith [hale]
    have h3 : (a/bl) * Real.log 80 ≤ (1/7) * (7 * Real.log (40/21)) :=
      mul_le_mul h2 hl80 (by positivity) (by positivity)
    linarith
  rw [Real.rpow_def_of_pos (by norm_num : (0:ℝ) < 80)]
  calc Real.exp (Real.log 80 * (a/bl)) ≤ Real.exp (Real.log (40/21)) := by
        apply Real.exp_le_exp.mpr; rw [mul_comm]; exact key
    _ = 40/21 := Real.exp_log (by norm_num)

lemma Wpow_le (M σ : ℝ) (hM : 1 ≤ M) (hσ : 19/20 ≤ σ) (hσ1 : σ < 1) :
    (2-σ) ^ Nat.floor (Real.log (80*M)/Real.log (10/7)) ≤ (40/21) * M ^ (3*(1-σ)) := by
  set W : ℝ := 2 - σ with hWdef
  have hMpos : 0 < M := lt_of_lt_of_le zero_lt_one hM
  have hWgt : 1 < W := by rw [hWdef]; linarith
  have hWpos : 0 < W := lt_trans zero_lt_one hWgt
  have hWle : W ≤ 21/20 := by rw [hWdef]; linarith
  have hlog107pos : 0 < Real.log (10/7) := Real.log_pos (by norm_num)
  have hy_ge : (Nat.floor (Real.log (80*M)/Real.log (10/7)) : ℝ)
      ≤ Real.log (80*M)/Real.log (10/7) := Nat.floor_le (by
        apply div_nonneg _ hlog107pos.le
        apply Real.log_nonneg; linarith)
  have hstep1 : W ^ Nat.floor (Real.log (80*M)/Real.log (10/7))
      ≤ W ^ (Real.log (80*M)/Real.log (10/7)) := by
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le hWgt.le hy_ge
  refine le_trans ?_ (le_trans hstep1 ?_)
  · rw [hWdef]
  · have hyval : W ^ (Real.log (80*M)/Real.log (10/7))
        = (80*M) ^ (Real.log W / Real.log (10/7)) := by
      rw [Real.rpow_def_of_pos hWpos, Real.rpow_def_of_pos (by positivity : (0:ℝ) < 80*M)]
      congr 1
      field_simp
    rw [hyval, Real.mul_rpow (by norm_num) hMpos.le]
    have hlogW_le : Real.log W ≤ Real.log (21/20) := Real.log_le_log hWpos hWle
    have h80 : (80:ℝ) ^ (Real.log W / Real.log (10/7)) ≤ 40/21 := by
      refine le_trans (Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 80) ?_)
        rpow_eighty_log_ratio_le
      exact div_le_div_of_nonneg_right hlogW_le hlog107pos.le
    have hlogW2 : Real.log W ≤ 1 - σ := by
      have h := Real.log_le_sub_one_of_pos hWpos
      have hWeq : W - 1 = 1 - σ := by rw [hWdef]; ring
      linarith
    have hexp_le : Real.log W / Real.log (10/7) ≤ 3*(1-σ) := by
      rw [div_le_iff₀ hlog107pos]
      have h3 : 1 ≤ 3 * Real.log (10/7) := three_mul_log_ten_sevenths_ge_one
      have hsig : 0 ≤ 1 - σ := by linarith
      nlinarith [hlogW2, h3, hsig]
    have hMpart : M ^ (Real.log W / Real.log (10/7)) ≤ M ^ (3*(1-σ)) :=
      Real.rpow_le_rpow_of_exponent_le hM hexp_le
    exact mul_le_mul h80 hMpart (Real.rpow_nonneg hMpos.le _) (by norm_num)

lemma tail_bound (M : ℝ) (hM : 1 ≤ M) :
    40 * M * (7/10 : ℝ) ^ (Nat.floor (Real.log (80*M)/Real.log (10/7)) + 1) ≤ 1/2 := by
  have hMpos : 0 < M := lt_of_lt_of_le zero_lt_one hM
  have hlog107pos : 0 < Real.log (10/7) := Real.log_pos (by norm_num)
  have hKlt : Real.log (80*M)/Real.log (10/7)
      < (Nat.floor (Real.log (80*M)/Real.log (10/7)) : ℝ) + 1 := Nat.lt_floor_add_one _
  have hlt : (7/10:ℝ) ^ ((Nat.floor (Real.log (80*M)/Real.log (10/7)) : ℝ) + 1)
      < (7/10:ℝ) ^ (Real.log (80*M)/Real.log (10/7)) := by
    rw [Real.rpow_lt_rpow_left_iff_of_base_lt_one (by norm_num) (by norm_num)]
    exact hKlt
  have hlt2 : (7/10:ℝ) ^ (Nat.floor (Real.log (80*M)/Real.log (10/7)) + 1)
      < (7/10:ℝ) ^ (Real.log (80*M)/Real.log (10/7)) := by
    rw [show ((Nat.floor (Real.log (80*M)/Real.log (10/7)) : ℝ) + 1)
        = ((Nat.floor (Real.log (80*M)/Real.log (10/7)) + 1 : ℕ) : ℝ) by push_cast; ring] at hlt
    rw [Real.rpow_natCast] at hlt
    exact hlt
  have hyval : (7/10:ℝ) ^ (Real.log (80*M)/Real.log (10/7)) = 1/(80*M) := by
    rw [Real.rpow_def_of_pos (by norm_num : (0:ℝ) < 7/10)]
    rw [show Real.log (7/10) = - Real.log (10/7) by
      rw [show (7/10:ℝ) = (10/7)⁻¹ by norm_num, Real.log_inv]]
    rw [show -Real.log (10/7) * (Real.log (80*M)/Real.log (10/7)) = - Real.log (80*M) by
      field_simp]
    rw [Real.exp_neg, Real.exp_log (by positivity : (0:ℝ) < 80*M), one_div]
  rw [hyval] at hlt2
  have h40 : 40 * M * (1/(80*M)) = 1/2 := by field_simp; ring
  calc 40 * M * (7/10 : ℝ) ^ (Nat.floor (Real.log (80*M)/Real.log (10/7)) + 1)
      ≤ 40 * M * (1/(80*M)) := (mul_lt_mul_of_pos_left hlt2 (by positivity)).le
    _ = 1/2 := h40

lemma final_arith {M ρ σ W : ℝ} {n : ℕ} (hM : 1 ≤ M) (hW : 1 < W) (hWle : W ≤ 21/20)
    (hσ0 : 0 ≤ 1 - σ) (hK0 : W ^ n ≤ (40/21) * M ^ (3*(1-σ)))
    (hbig : (1-σ)/2 ≤ ρ * W ^ (n+1)) :
    (1/4) * (1 - σ) * M ^ (-(3*(1-σ))) ≤ ρ := by
  have hWpos : 0 < W := lt_trans zero_lt_one hW
  have hMpos : 0 < M := lt_of_lt_of_le zero_lt_one hM
  have hWpow_pos : 0 < W ^ (n+1) := pow_pos hWpos _
  have h2 : ((1-σ)/2) * (W ^ (n+1))⁻¹ ≤ ρ := by
    have := mul_le_mul_of_nonneg_right hbig (inv_nonneg.mpr hWpow_pos.le)
    rwa [mul_assoc, mul_inv_cancel₀ hWpow_pos.ne', mul_one] at this
  have hN : (W ^ (n+1))⁻¹ = W ^ (-((n:ℝ)+1)) := by
    rw [← Real.rpow_natCast W (n+1), ← Real.rpow_neg hWpos.le]
    congr 1
    push_cast; ring
  rw [hN] at h2
  have hsplit : W ^ (-((n:ℝ)+1)) = W ^ (-(n:ℝ)) * W ^ (-1 : ℝ) := by
    rw [show -((n:ℝ)+1) = (-(n:ℝ)) + (-1 : ℝ) by ring]
    exact Real.rpow_add hWpos (-(n:ℝ)) (-1 : ℝ)
  rw [hsplit] at h2
  rw [Real.rpow_neg_one] at h2
  have hWn : W ^ (-(n:ℝ)) = (W^n)⁻¹ := by
    rw [← Real.rpow_natCast W n, Real.rpow_neg hWpos.le]
  have hWinv_ge : (20/21:ℝ) ≤ W⁻¹ := by
    have h := (inv_le_inv₀ (by norm_num : (0:ℝ) < 21/20) hWpos).mpr hWle
    rw [show ((21:ℝ)/20)⁻¹ = 20/21 by norm_num] at h
    exact h
  have hWn_ge : (21/40) * M ^ (-(3*(1-σ))) ≤ W ^ (-(n:ℝ)) := by
    have hb : ((40/21) * M ^ (3*(1-σ)))⁻¹ ≤ (W^n)⁻¹ :=
      (inv_le_inv₀ (by positivity) (pow_pos hWpos n)).mpr hK0
    rw [hWn]
    have heq : ((40/21) * M ^ (3*(1-σ)))⁻¹ = (21/40) * M ^ (-(3*(1-σ))) := by
      rw [mul_inv, Real.rpow_neg hMpos.le]; norm_num
    rw [heq] at hb
    exact hb
  have hstep : ((1-σ)/2) * ((21/40) * M ^ (-(3*(1-σ)))) * (20/21) ≤
      ((1-σ)/2) * (W ^ (-(n:ℝ)) * W⁻¹) := by
    have h1 : 0 ≤ (1-σ)/2 := by linarith
    have h4 : 0 ≤ (20/21:ℝ) := by norm_num
    have hb' : 0 ≤ (1-σ)/2 * W ^ (-(n:ℝ)) := mul_nonneg h1 (Real.rpow_nonneg hWpos.le _)
    have h3 := mul_le_mul (mul_le_mul_of_nonneg_left hWn_ge h1) hWinv_ge h4 hb'
    simpa [mul_assoc] using h3
  have hfin : ((1-σ)/2) * ((21/40) * M ^ (-(3*(1-σ)))) * (20/21)
      = (1/4) * (1-σ) * M ^ (-(3*(1-σ))) := by ring
  rw [hfin] at hstep
  linarith [h2, hstep]


theorem estermann_positivity
    {f : ℂ → ℂ} {r : ℕ → ℝ} {M σ K : ℝ} (hK : 0 < K) (hM : 1 ≤ M)
    (hσ : 19 / 20 ≤ σ) (hσ1 : σ < 1)
    (hfa : AnalyticOnNhd ℂ f (Metric.closedBall 2 (3 / 2)))
    (hfb : ∀ z ∈ Metric.closedBall 2 (3 / 2), ‖f z‖ ≤ M)
    (hζ : ∀ z ∈ Metric.sphere (2 : ℂ) (3 / 2), ‖riemannZeta z‖ ≤ K)
    (hζσ : ∃ c : ℝ, c < 0 ∧ riemannZeta (σ : ℂ) = (c : ℂ))
    (hr : ∀ n : ℕ, 0 ≤ r n) (hr1 : r 1 = 1)
    (habsc : LSeries.abscissaOfAbsConv (fun n : ℕ => (r n : ℂ)) < 2)
    (hF : ∀ s : ℂ, 1 < s.re →
      riemannZeta s * f s = ∑' n : ℕ, (r n : ℂ) * (n : ℂ) ^ (-s))
    (hfσ : 0 ≤ (f σ).re) :
    (1 / 4) * (1 - σ) * M ^ (-(3 * (1 - σ))) ≤ (f 1).re := by
  have hMpos : (0:ℝ) < M := lt_of_lt_of_le zero_lt_one hM
  have hsigpos : (0:ℝ) < 1 - σ := by linarith
  have hwgt : (1:ℝ) < 2 - σ := by linarith
  have hwle : (2:ℝ) - σ ≤ 21/20 := by linarith
  obtain ⟨c, hcneg, hcval⟩ := hζσ
  set f0 : ℕ → ℂ := fun n => (r n : ℂ) with hf0def
  have habsc0 : LSeries.abscissaOfAbsConv f0 < ((2:ℂ).re : EReal) := by
    have h2 : ((2:ℂ).re : EReal) = (2 : EReal) := rfl
    rw [h2, hf0def]; exact habsc
  set H : ℂ → ℂ := (fun w => dslope riemannZeta₁ 1 (2 - w) * f (2 - w) + dslope f 1 (2 - w)) with hHdef
  -- F is eventually the L-series
  have hFF : (fun s => riemannZeta s * f s) =ᶠ[𝓝 (2:ℂ)] LSeries f0 := by
    refine Filter.eventuallyEq_iff_exists_mem.mpr ⟨{s | 1 < s.re}, ?_, ?_⟩
    · exact (isOpen_lt continuous_const Complex.continuous_re).mem_nhds
        (by norm_num : (1:ℝ) < (2:ℂ).re)
    · intro s hs
      change riemannZeta s * f s = LSeries f0 s
      rw [hF s hs, show LSeries f0 s = ∑' n, LSeries.term f0 s n from rfl]
      apply tsum_congr
      intro n
      rcases eq_or_ne n 0 with rfl | hn
      · rw [LSeries.term_def]
        have hs0 : (-(s)) ≠ 0 := by
          intro h; rw [neg_eq_zero] at h; rw [h] at hs; norm_num at hs
        simp [Complex.zero_cpow hs0]
      · rw [LSeries.term_of_ne_zero hn, hf0def, Complex.cpow_neg, div_eq_mul_inv]
  -- summability of the coefficient sequences
  have hgs : ∀ k, Summable (fun n : ℕ => (Real.log (n:ℝ))^k * r n / (n:ℝ)^2) := by
    intro k
    have hfun : (fun n : ℕ => (((Real.log (n:ℝ))^k * r n : ℝ) : ℂ)) = LSeries.logMul^[k] f0 := by
      funext n
      rw [hf0def, logMul_iterate_apply, ← Complex.natCast_log]
      push_cast; ring
    have habs : LSeries.abscissaOfAbsConv (fun n : ℕ => (((Real.log (n:ℝ))^k * r n : ℝ) : ℂ))
        < 2 := by
      rw [hfun, LSeries.absicssaOfAbsConv_logPowMul, hf0def]
      exact habsc
    have hs := LSeries.summable_real_of_abscissaOfAbsConv_lt (f := fun n => (Real.log (n:ℝ))^k * r n) (x := 2) habs
    simpa using hs
  have hLSer : ∀ k, LSeries (LSeries.logMul^[k] f0) 2
      = ((∑' n : ℕ, (Real.log (n:ℝ))^k * r n / (n:ℝ)^2 : ℝ) : ℂ) := by
    intro k
    rw [hf0def]
    exact LSeries_logMul_coe_eq r k
  have hiter : ∀ k, iteratedDeriv k (fun s => riemannZeta s * f s) 2
      = (-1)^k * LSeries (LSeries.logMul^[k] f0) 2 := by
    intro k
    rw [Filter.EventuallyEq.iteratedDeriv_eq k hFF]
    exact LSeries_iteratedDeriv k habsc0
  set bb : ℕ → ℝ := fun k => (∑' n : ℕ, (Real.log (n:ℝ))^k * r n / (n:ℝ)^2)/(Nat.factorial k) with hbbdef
  have hbb_nonneg : ∀ k, 0 ≤ bb k := by
    intro k
    rw [hbbdef]
    apply div_nonneg
    · apply tsum_nonneg
      intro n
      exact div_nonneg (mul_nonneg (pow_nonneg (log_natCast_nonneg n) _) (hr n)) (by positivity)
    · positivity
  have hbb0 : 1 ≤ bb 0 := by
    rw [hbbdef]
    simp only [Nat.factorial_zero, Nat.cast_one, div_one]
    have hsumm := hgs 0
    have hg1 : (1:ℝ) = (Real.log (1:ℝ))^0 * r 1 / (1:ℝ)^2 := by rw [hr1]; norm_num
    rw [hg1]
    simpa using hsumm.sum_le_tsum {1} (fun i _ =>
      (div_nonneg (mul_nonneg (pow_nonneg (log_natCast_nonneg i) _) (hr i)) (by positivity) : (0:ℝ) ≤ _))
  have hbb_eq : ∀ k, (bb k : ℂ)
      = (-1)^k * iteratedDeriv k (fun s => riemannZeta s * f s) 2 / (Nat.factorial k : ℂ) := by
    intro k
    rw [hbbdef, Complex.ofReal_div, Complex.ofReal_natCast, ← hLSer k]
    congr 1
    have hneg : (-1:ℂ)^k * iteratedDeriv k (fun s => riemannZeta s * f s) 2
        = LSeries (LSeries.logMul^[k] f0) 2 := by
      rw [hiter k, ← mul_assoc]
      rw [show (-1:ℂ)^k * (-1:ℂ)^k = 1 by
        rw [← pow_two, ← pow_mul]; exact Even.neg_one_pow ⟨k, by ring⟩, one_mul]
    exact hneg.symm
  -- coefficient of H
  have hHderiv : ∀ k, (Nat.factorial k : ℂ)⁻¹ * iteratedDeriv k H 0 = (bb k : ℂ) - f 1 := by
    intro k
    rw [show H = (fun w => dslope riemannZeta₁ 1 (2 - w) * f (2 - w) + dslope f 1 (2 - w)) from hHdef]
    rw [iteratedDeriv_aux f hfa k, hbb_eq k]
    have hk : (Nat.factorial k : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero k
    rw [mul_sub, div_eq_mul_inv]
    rw [show (Nat.factorial k : ℂ)⁻¹ * (f 1 * (Nat.factorial k : ℂ)) = f 1 by
      rw [mul_comm (f 1) (Nat.factorial k : ℂ), ← mul_assoc, inv_mul_cancel₀ hk, one_mul]]
    rw [mul_comm ((Nat.factorial k : ℂ)⁻¹) ((-1)^k * iteratedDeriv k (fun s => riemannZeta s * f s) 2)]

  -- differentiability / continuity / bound of H
  have hAdiff : Differentiable ℂ (fun s : ℂ => dslope riemannZeta₁ 1 s) := by
    rw [← differentiableOn_univ]
    exact (differentiableOn_dslope (s := Set.univ) (c := 1) (by simp)).mpr
      differentiable_riemannZeta₁.differentiableOn
  have hHdiff : DifferentiableOn ℂ H (Metric.ball (0:ℂ) (3/2)) := by
    rw [hHdef]
    have hft : DifferentiableOn ℂ (fun w : ℂ => f (2 - w)) (Metric.ball (0:ℂ) (3/2)) := by
      intro w hw
      have hw' : ‖w‖ < 3/2 := by simpa [mem_ball, dist_eq_norm, sub_zero] using hw
      have hmem : (2 - w) ∈ Metric.closedBall (2:ℂ) (3/2) := by
        rw [mem_closedBall, dist_eq_norm]
        have h2 : (2 - w) - 2 = -w := by ring
        rw [h2, norm_neg]; exact hw'.le
      exact (((hfa (2 - w) hmem).differentiableAt).comp w
        ((differentiableAt_const (2:ℂ)).sub differentiableAt_id)).differentiableWithinAt
    have hdslope : DifferentiableOn ℂ (dslope f 1) (Metric.ball (2:ℂ) (3/2)) := by
      have hc : Metric.ball (2:ℂ) (3/2) ∈ 𝓝 (1:ℂ) := by
        apply IsOpen.mem_nhds Metric.isOpen_ball
        rw [mem_ball, dist_eq_norm]; norm_num
      exact (differentiableOn_dslope hc).mpr (fun z hz =>
        (hfa z (ball_subset_closedBall hz)).differentiableAt.differentiableWithinAt)
    have hdslope2 : DifferentiableOn ℂ (fun w => dslope f 1 (2 - w)) (Metric.ball (0:ℂ) (3/2)) := by
      intro w hw
      have hw' : ‖w‖ < 3/2 := by simpa [mem_ball, dist_eq_norm, sub_zero] using hw
      have hmem : (2 - w) ∈ Metric.ball (2:ℂ) (3/2) := by
        rw [mem_ball, dist_eq_norm]
        have h2 : (2 - w) - 2 = -w := by ring
        rw [h2, norm_neg]; exact hw'
      exact ((hdslope.differentiableAt (Metric.isOpen_ball.mem_nhds hmem)).comp w
        ((differentiableAt_const (2:ℂ)).sub differentiableAt_id)).differentiableWithinAt
    have hA2 : DifferentiableOn ℂ (fun w => dslope riemannZeta₁ 1 (2 - w)) (Metric.ball (0:ℂ) (3/2)) := by
      intro w hw
      exact ((hAdiff.differentiableAt).comp w
        ((differentiableAt_const (2:ℂ)).sub differentiableAt_id)).differentiableWithinAt
    exact (hA2.mul hft).add hdslope2
  have hHcont : ContinuousOn H (Metric.closedBall (0:ℂ) (3/2)) := by
    rw [hHdef]
    intro w hw
    have hw' : ‖w‖ ≤ 3/2 := by simpa [mem_closedBall, dist_eq_norm, sub_zero] using hw
    have hmem : (2 - w) ∈ Metric.closedBall (2:ℂ) (3/2) := by
      rw [mem_closedBall, dist_eq_norm]
      have h2 : (2 - w) - 2 = -w := by ring
      rw [h2, norm_neg]; exact hw'
    have hlin_cont : ContinuousAt (fun w : ℂ => (2:ℂ) - w) w := by fun_prop
    have hfcont : ContinuousAt (fun w : ℂ => f (2 - w)) w :=
      ((hfa (2-w) hmem).continuousAt).comp hlin_cont
    have hAcont : ContinuousAt (fun w : ℂ => dslope riemannZeta₁ 1 (2 - w)) w :=
      (hAdiff.continuous.continuousAt).comp hlin_cont
    have hdscont : ContinuousAt (fun w : ℂ => dslope f 1 (2 - w)) w := by
      have hs_cont : ContinuousAt (dslope f 1) (2 - w) := by
        rcases eq_or_ne (2 - w) 1 with h | h
        · rw [h] at hmem ⊢
          exact continuousAt_dslope_same.mpr ((hfa 1 hmem).differentiableAt)
        · exact (continuousAt_dslope_of_ne h).mpr ((hfa (2-w) hmem).continuousAt)
      exact hs_cont.comp hlin_cont
    exact ((hAcont.mul hfcont).add hdscont).continuousWithinAt
  have hHbound : ∀ z ∈ Metric.sphere (0:ℂ) (3/2), ‖H z‖ ≤ 12*M := by
    intro z hz
    have hz' : ‖z‖ = 3/2 := by simpa [mem_sphere_iff_norm] using hz
    have hzne : z ≠ 1 := by intro h; rw [h] at hz'; norm_num at hz'
    change ‖dslope riemannZeta₁ 1 (2 - z) * f (2 - z) + dslope f 1 (2 - z)‖ ≤ 12*M
    rw [H_eq_of_ne_one f hzne]
    have h2z : (2 - z) ∈ Metric.sphere (2:ℂ) (3/2) := by
      rw [mem_sphere_iff_norm]
      have h2 : (2 - z) - 2 = -z := by ring
      rw [h2, norm_neg, hz']
    have hζb := norm_riemannZeta_le_ten_of_mem_sphere h2z
    have hfz : ‖f (2 - z)‖ ≤ M := hfb (2-z) (by
      rw [mem_closedBall, dist_eq_norm]
      have h2 : (2:ℂ) - z - 2 = -z := by ring
      rw [h2, norm_neg, hz'])
    have hf1 : ‖f 1‖ ≤ M := hfb 1 (by rw [mem_closedBall, dist_eq_norm]; norm_num)
    have hone : ‖(1 - z)⁻¹‖ ≤ 2 := by
      rw [norm_inv]
      have hge : (1/2:ℝ) ≤ ‖1 - z‖ := by
        have h := abs_norm_sub_norm_le z (1:ℂ)
        rw [hz', norm_one] at h
        norm_num at h
        rwa [norm_sub_rev z 1] at h
      rw [inv_le_comm₀ (norm_pos_iff.mpr (by intro h; rw [h] at hge; norm_num at hge))
        (by norm_num : (0:ℝ) < 2)]
      norm_num; linarith
    calc ‖riemannZeta (2 - z) * f (2 - z) - f 1 * (1 - z)⁻¹‖
        ≤ ‖riemannZeta (2 - z) * f (2 - z)‖ + ‖f 1 * (1 - z)⁻¹‖ := norm_sub_le _ _
      _ = ‖riemannZeta (2 - z)‖ * ‖f (2 - z)‖ + ‖f 1‖ * ‖(1 - z)⁻¹‖ := by rw [norm_mul, norm_mul]
      _ ≤ 10 * M + M * 2 := by gcongr
      _ = 12 * M := by ring
  have hHdccl : DiffContOnCl ℂ H (Metric.ball (0:ℂ) (3/2)) :=
    ⟨hHdiff, by rw [closure_ball (0:ℂ) (by norm_num : (3/2:ℝ) ≠ 0)]; exact hHcont⟩
  have hCauchy : ∀ k, ‖iteratedDeriv k H 0‖ ≤ (Nat.factorial k : ℝ) * (12*M) / (3/2)^k := fun k =>
    Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le k (by norm_num) hHdccl hHbound
  -- parameters
  set W : ℝ := 2 - σ with hWdef
  have hWgt' : 1 < W := by rw [hWdef]; linarith
  have hWle' : W ≤ 21/20 := by rw [hWdef]; linarith
  have hWpos : 0 < W := lt_trans zero_lt_one hWgt'
  set ρ : ℝ := (f 1).re with hρdef
  have hWmem : (W:ℂ) ∈ Metric.ball (0:ℂ) (3/2) := by
    rw [mem_ball, dist_eq_norm, sub_zero, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hWpos]
    linarith
  have hTaylor : HasSum (fun k => (Nat.factorial k : ℂ)⁻¹ • (W:ℂ)^k • iteratedDeriv k H 0)
      (H (W:ℂ)) := by
    have h := Complex.hasSum_taylorSeries_on_ball (f := H) (c := 0) (r := 3/2) hHdiff hWmem
    simpa using h
  have hRe : HasSum (fun k => (bb k - ρ) * W^k) (H (W:ℂ)).re := by
    have hm := hTaylor.map Complex.reAddGroupHom Complex.continuous_re
    have hterm : ∀ k, Complex.reAddGroupHom
        ((Nat.factorial k : ℂ)⁻¹ • (W:ℂ)^k • iteratedDeriv k H 0) = (bb k - ρ) * W^k := by
      intro k
      simp only [smul_eq_mul]
      rw [show Complex.reAddGroupHom ((Nat.factorial k : ℂ)⁻¹ * ((W:ℂ)^k * iteratedDeriv k H 0))
            = ((Nat.factorial k : ℂ)⁻¹ * ((W:ℂ)^k * iteratedDeriv k H 0)).re from rfl]
      rw [show (Nat.factorial k : ℂ)⁻¹ * ((W:ℂ)^k * iteratedDeriv k H 0)
            = ((W^k : ℝ) : ℂ) * ((Nat.factorial k : ℂ)⁻¹ * iteratedDeriv k H 0) by
          rw [Complex.ofReal_pow]; ring]
      rw [Complex.re_ofReal_mul, hHderiv k]
      simp only [Complex.sub_re, Complex.ofReal_re, hρdef]
      ring
    have hcomp : ((fun z : ℂ => Complex.reAddGroupHom z) ∘
        (fun k => (Nat.factorial k : ℂ)⁻¹ • (W:ℂ)^k • iteratedDeriv k H 0))
        = (fun k => (bb k - ρ) * W^k) := funext hterm
    rw [hcomp] at hm
    simpa using hm
  -- value of H at W
  have hWne : (W:ℂ) ≠ 1 := by
    rw [hWdef]; intro h
    have := congrArg Complex.re h; simp at this; linarith
  have hHW : H (W:ℂ) = riemannZeta (σ:ℂ) * f (σ:ℂ) + f 1 * (((1-σ):ℝ):ℂ)⁻¹ := by
    have h1 : H (W:ℂ) = riemannZeta (2 - (W:ℂ)) * f (2 - (W:ℂ)) - f 1 * (1 - (W:ℂ))⁻¹ := by
      rw [hHdef]; exact H_eq_of_ne_one f hWne
    rw [h1]
    have h2 : (2:ℂ) - (W:ℂ) = (σ:ℂ) := by rw [hWdef]; push_cast; ring
    have h3 : (1:ℂ) - (W:ℂ) = -(((1-σ):ℝ):ℂ) := by rw [hWdef]; push_cast; ring
    rw [h2, h3, inv_neg]; ring
  have hHre_le : (H (W:ℂ)).re ≤ ρ * (1-σ)⁻¹ := by
    rw [hHW]
    have h1 : (riemannZeta (σ:ℂ) * f (σ:ℂ)).re ≤ 0 := by
      rw [hcval, Complex.re_ofReal_mul]
      exact mul_nonpos_of_nonpos_of_nonneg hcneg.le hfσ
    have h2 : (f 1 * (((1-σ):ℝ):ℂ)⁻¹).re = ρ * (1-σ)⁻¹ := by
      rw [mul_comm (f 1) (((1-σ):ℝ):ℂ)⁻¹, ← Complex.ofReal_inv, Complex.re_ofReal_mul, hρdef]
      ring
    rw [Complex.add_re, h2]; linarith [h1]
  -- choose K0
  set K0 : ℕ := Nat.floor (Real.log (80*M)/Real.log (10/7)) with hK0def
  have hK0le : (K0 : ℝ) ≤ Real.log (80*M)/Real.log (10/7) := by
    rw [hK0def]
    exact Nat.floor_le (by
      apply div_nonneg _ (Real.log_pos (by norm_num)).le
      apply Real.log_nonneg; linarith)
  have hsummable : Summable (fun k => (bb k - ρ) * W^k) := hRe.summable
  have hsplit := hsummable.sum_add_tsum_nat_add (K0+1)
  rw [hRe.tsum_eq] at hsplit
  -- head bound
  have hbb_ge : (1:ℝ) ≤ ∑ i ∈ Finset.range (K0+1), bb i * W^i := by
    have h0mem : 0 ∈ Finset.range (K0+1) := Finset.mem_range.mpr (Nat.succ_pos K0)
    have hnonneg : ∀ i ∈ Finset.range (K0+1), 0 ≤ bb i * W^i :=
      fun i _ => mul_nonneg (hbb_nonneg i) (pow_nonneg hWpos.le _)
    calc (1:ℝ) ≤ bb 0 * W^0 := by rw [pow_zero, mul_one]; exact hbb0
      _ ≤ ∑ i ∈ Finset.range (K0+1), bb i * W^i := Finset.single_le_sum hnonneg h0mem
  have hhead : 1 - ρ * (∑ i ∈ Finset.range (K0+1), W^i)
      ≤ ∑ i ∈ Finset.range (K0+1), (bb i - ρ)*W^i := by
    have hsplit2 : ∑ i ∈ Finset.range (K0+1), (bb i - ρ)*W^i
        = (∑ i ∈ Finset.range (K0+1), bb i * W^i) - ρ * (∑ i ∈ Finset.range (K0+1), W^i) := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl (fun i _ => by ring)
    rw [hsplit2]; linarith [hbb_ge]
  -- tail bound
  have htail_sum : ∑' i, (bb (i+(K0+1)) - ρ) * W^(i+(K0+1)) ≥ -(1/2:ℝ) := by
    have hsumm_t : Summable (fun i => (bb (i+(K0+1)) - ρ) * W^(i+(K0+1))) :=
      (summable_nat_add_iff (K0+1)).mpr hsummable
    have hterm_le : ∀ i, |(bb (i+(K0+1)) - ρ) * W^(i+(K0+1))|
        ≤ 12*M * ((2/3)*W)^(i+(K0+1)) := by
      intro i
      have h1 : |(bb (i+(K0+1)) - ρ) * W^(i+(K0+1))|
          = |bb (i+(K0+1)) - ρ| * W^(i+(K0+1)) := by
        rw [abs_mul, abs_of_nonneg (pow_nonneg hWpos.le _)]
      have h2 : |bb (i+(K0+1)) - ρ| ≤ ‖(Nat.factorial (i+(K0+1)) : ℂ)⁻¹ * iteratedDeriv (i+(K0+1)) H 0‖ := by
        have ha := Complex.abs_re_le_norm ((bb (i+(K0+1)) : ℂ) - f 1)
        rw [Complex.sub_re, Complex.ofReal_re, ← hρdef, ← hHderiv (i+(K0+1))] at ha
        exact ha
      have h3 : ‖(Nat.factorial (i+(K0+1)) : ℂ)⁻¹ * iteratedDeriv (i+(K0+1)) H 0‖
          ≤ 12*M * (2/3)^(i+(K0+1)) := by
        rw [norm_mul, norm_inv, Complex.norm_natCast]
        have hfac : (0:ℝ) < (Nat.factorial (i+(K0+1)) : ℝ) := by positivity
        rw [inv_mul_le_iff₀ hfac]
        refine le_trans (hCauchy (i+(K0+1))) ?_
        rw [div_eq_mul_inv, ← inv_pow, show (3/2:ℝ)⁻¹ = 2/3 by norm_num]
        exact le_of_eq (mul_assoc _ _ _)
      rw [h1]
      calc |bb (i+(K0+1)) - ρ| * W^(i+(K0+1))
          ≤ (12*M * (2/3)^(i+(K0+1))) * W^(i+(K0+1)) := by
            exact mul_le_mul_of_nonneg_right (le_trans h2 h3) (pow_nonneg hWpos.le _)
        _ = 12*M * ((2/3)*W)^(i+(K0+1)) := by
            rw [mul_pow]; ring
    have hsumm_rhs : Summable (fun i => 12*M * ((2/3)*W)^(i+(K0+1))) := by
      apply Summable.mul_left
      exact (summable_nat_add_iff (K0+1)).mpr (summable_geometric_of_norm_lt_one (by
        rw [Real.norm_eq_abs, abs_of_nonneg (by positivity : (0:ℝ) ≤ (2:ℝ)/3 * W)]
        nlinarith [hWle', hWpos]))
    have hle1 : ∑' i, |(bb (i+(K0+1)) - ρ) * W^(i+(K0+1))|
        ≤ ∑' i, 12*M * ((2/3)*W)^(i+(K0+1)) :=
      Summable.tsum_le_tsum hterm_le hsumm_t.norm hsumm_rhs
    have hge : ∑' i, (bb (i+(K0+1)) - ρ) * W^(i+(K0+1))
        ≥ - ∑' i, |(bb (i+(K0+1)) - ρ) * W^(i+(K0+1))| := by
      have := Summable.tsum_le_tsum (fun i => neg_abs_le ((bb (i+(K0+1)) - ρ) * W^(i+(K0+1))))
        hsumm_t.norm.neg hsumm_t
      rwa [tsum_neg] at this
    have hval : ∑' i, 12*M * ((2/3)*W)^(i+(K0+1)) ≤ 1/2 := by
      rw [tsum_mul_left]
      have hgeo : ∑' i : ℕ, ((2/3)*W)^(i+(K0+1)) = ((2/3)*W)^(K0+1) * (1 - (2/3)*W)⁻¹ := by
        have hξ : ‖(2/3)*W‖ < 1 := by
          rw [Real.norm_eq_abs, abs_of_nonneg (by positivity : (0:ℝ) ≤ (2:ℝ)/3 * W)]
          nlinarith [hWle', hWpos]
        rw [show (fun i : ℕ => ((2/3)*W)^(i+(K0+1))) = (fun i => ((2/3)*W)^i * ((2/3)*W)^(K0+1)) from
          funext (fun i => by rw [pow_add])]
        rw [tsum_mul_right, tsum_geometric_of_norm_lt_one hξ]
        ring
      rw [hgeo]
      have hxi : (2/3)*W ≤ 7/10 := by nlinarith [hWle']
      have hx0 : (0:ℝ) ≤ (2/3)*W := by positivity
      have hx1 : ((2/3)*W)^(K0+1) ≤ (7/10)^(K0+1) :=
        pow_le_pow_left₀ hx0 hxi _
      have hpos : (0:ℝ) < 1 - (2/3)*W := by linarith
      have hinv : (1 - (2/3)*W)⁻¹ ≤ (1 - 7/10)⁻¹ :=
        (inv_le_inv₀ hpos (by norm_num : (0:ℝ) < 1 - 7/10)).mpr (by linarith [hxi])
      calc 12*M * (((2/3)*W)^(K0+1) * (1 - (2/3)*W)⁻¹)
          = 12*M * ((2/3)*W)^(K0+1) * (1 - (2/3)*W)⁻¹ := by ring
        _ ≤ 12*M * (7/10)^(K0+1) * (1 - 7/10)⁻¹ := by
            have hbc := mul_le_mul hx1 hinv (by positivity : (0:ℝ) ≤ (1 - (2/3)*W)⁻¹)
              (by positivity : (0:ℝ) ≤ (7/10)^(K0+1))
            have h2 := mul_le_mul_of_nonneg_left hbc (by positivity : (0:ℝ) ≤ 12*M)
            linarith [h2]
        _ = 40 * M * (7/10)^(K0+1) := by ring_nf
        _ ≤ 1/2 := by
            rw [hK0def]
            have := tail_bound M hM
            linarith
    linarith [hle1, hge, hval]
  -- combine
  have h5 : (1-σ)/2 ≤ ρ * W^(K0+1) := by
    have hgeom : ∑ i ∈ Finset.range (K0+1), W^i = (W^(K0+1) - 1)/(W - 1) :=
      geom_sum_eq (by intro h; linarith [hWgt'] : W ≠ 1) (K0+1)
    have hWeq : W - 1 = 1 - σ := by rw [hWdef]; ring
    rw [hgeom, hWeq] at hhead
    have h1 : ρ/(1-σ) ≥ (H (W:ℂ)).re := by
      rw [div_eq_mul_inv]; exact hHre_le
    rw [← hsplit] at h1
    have hsig : 0 < 1 - σ := hsigpos
    have h2 : 1/2 - ρ*((W^(K0+1)-1)/(1-σ)) ≤ ρ/(1-σ) := by
      linarith [h1, hhead, htail_sum]
    have hden : (1-σ) ≠ 0 := ne_of_gt hsig
    have h6 := mul_le_mul_of_nonneg_right h2 (le_of_lt hsig)
    field_simp at h6
    nlinarith [h6]
  exact final_arith hM hWgt' hWle' (le_of_lt hsigpos) (Wpow_le M σ hM hσ hσ1) h5


end
end Commons.NumberTheory.DirichletCharacter