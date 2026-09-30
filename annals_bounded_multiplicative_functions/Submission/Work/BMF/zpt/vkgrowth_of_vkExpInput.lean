import Mathlib
import Submission.Work.BMF.VKGrowthDefs
import Submission.Work.BMF.VKStripDefs
import Submission.Work.BMF.VKGrowth
import Submission.Work.BMF.HurwitzShift
import Submission.Work.BMF.vk_exp_sum
import Submission.Work.BMF.N7.vk_interface
import Submission.Work.BMF.N7.V2_zeta_strip
import Submission.Work.BMF.N7.dyadic_vk_sum_bound
import Submission.Work.BMF.VKChain.block_sum_uniform
import Submission.Work.BMF.VKChain.shift_head_bound
import Submission.Work.BMF.VKChain.shift_vk_range_bound
import Submission.Work.BMF.VKChain.kl_tail_block_bound
import Submission.Work.BMF.VKChain.shiftTerm_kl_range_le

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option maxHeartbeats 1600000

namespace Work.BMF.zpt

open Finset
open scoped BigOperators

noncomputable section

/-! ## Reindexing and splitting helpers -/

private lemma Ioc_eq_Ico_succ (K N : ℕ) : Finset.Ioc K N = Finset.Ico (K + 1) (N + 1) := by
  ext x
  simp only [Finset.mem_Ioc, Finset.mem_Ico]
  omega

private lemma sum_Ioc_eq_Ico_sum (f : ℕ → ℂ) (K N : ℕ) :
    ∑ m ∈ Finset.Ioc K N, f m = ∑ m ∈ Finset.Ico (K + 1) (N + 1), f m := by
  rw [Ioc_eq_Ico_succ]

private lemma tsum_split_Ico {f : ℕ → ℂ} (hf : Summable f) {K N : ℕ} (h : K ≤ N) :
    ∑' m : ℕ, f (K + m) = (∑ m ∈ Finset.Ico K N, f m) + ∑' m : ℕ, f (N + m) := by
  have hg : Summable (fun m : ℕ => f (K + m)) := by
    simpa [Nat.add_comm] using (summable_nat_add_iff K).mpr hf
  have h1 : (∑' m : ℕ, f (K + m)) =
      (∑ m ∈ Finset.range (N - K), f (K + m)) + ∑' m : ℕ, f (K + (m + (N - K))) :=
    (hg.sum_add_tsum_nat_add (N - K)).symm
  rw [h1, ← Finset.sum_Ico_eq_sum_range f K N]
  congr 1
  refine tsum_congr (fun m => ?_)
  rw [show K + (m + (N - K)) = N + m by omega]

/-! ## Arithmetic for the far range and the tail -/

private lemma kl_piece_arith {Nt M : ℕ} {t : ℝ} (hNt1 : 1 ≤ Nt) (hNtge : |t| ≤ (Nt : ℝ))
    (hNtle : (Nt : ℝ) ≤ |t| + 1) (ht3 : 3 ≤ |t|)
    (hM : (M : ℝ) = (Nt : ℝ) * (Nt : ℝ)) :
    (Real.log (M : ℝ) / Real.log 2 + 2) *
      (24 * Real.pi * (M : ℝ) ^ (1 / 3 : ℝ) / |t|) ≤ 4000 := by
  set v : ℝ := |t| ^ (1 / 3 : ℝ) with hvdef
  have ht1 : (1 : ℝ) ≤ |t| := by linarith
  have htpos : (0 : ℝ) < |t| := by linarith
  have hv1 : 1 ≤ v := by
    rw [hvdef]; exact Real.one_le_rpow ht1 (by norm_num)
  have hvpos : 0 < v := lt_of_lt_of_le zero_lt_one hv1
  have hlog2 : (1 / 2 : ℝ) ≤ Real.log 2 := by have := Real.log_two_gt_d9; linarith
  have hlog2pos : 0 < Real.log 2 := by linarith
  have hM1 : (1:ℝ) ≤ (M:ℝ) := by
    have : (1:ℕ) ≤ Nt * Nt := by simpa using Nat.mul_le_mul hNt1 hNt1
    rw [hM]; exact_mod_cast this
  have hMle : (M : ℝ) ≤ (2 * |t|) ^ 2 := by
    rw [hM]
    have hNt2 : (Nt : ℝ) ≤ 2 * |t| := by linarith
    have h1 : (Nt : ℝ) * (Nt : ℝ) ≤ (2 * |t|) * (2 * |t|) :=
      mul_le_mul hNt2 hNt2 (by linarith) (by linarith)
    calc (Nt : ℝ) * (Nt : ℝ) ≤ (2 * |t|) * (2 * |t|) := h1
      _ = (2 * |t|) ^ 2 := by ring
  have hMpos : (0 : ℝ) < (M : ℝ) := by linarith
  have hlogM : Real.log (M : ℝ) ≤ 2 + 6 * v := by
    have h1 : Real.log (M : ℝ) ≤ Real.log ((2 * |t|) ^ 2) := Real.log_le_log hMpos hMle
    rw [Real.log_pow] at h1
    have h2 : Real.log (2 * |t|) = Real.log 2 + Real.log |t| :=
      Real.log_mul (by norm_num) (ne_of_gt htpos)
    push_cast at h1
    rw [h2] at h1
    have h3 : Real.log |t| ≤ 3 * v := by
      have h4 := Real.log_le_rpow_div (abs_nonneg t) (by norm_num : (0:ℝ) < 1/3)
      have h5 : |t| ^ (1 / 3 : ℝ) / (1 / 3) = 3 * v := by rw [hvdef]; ring
      linarith [h4, h5.le, h5.ge]
    have h6 : Real.log 2 ≤ 1 := by
      have := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 2); linarith
    linarith
  have hA : Real.log (M : ℝ) / Real.log 2 + 2 ≤ 6 + 12 * v := by
    have h1 : Real.log (M : ℝ) / Real.log 2 ≤ (2 + 6 * v) / Real.log 2 :=
      div_le_div_of_nonneg_right hlogM hlog2pos.le
    have h2 : (2 + 6 * v) / Real.log 2 ≤ 2 * (2 + 6 * v) := by
      rw [div_le_iff₀ hlog2pos]; nlinarith [hlog2, hvpos]
    linarith
  have hthird : |t| ^ (2 / 3 : ℝ) = |t| * |t| ^ (-(1 / 3) : ℝ) := by
    have h := Real.rpow_add htpos (1:ℝ) (-(1/3:ℝ))
    rw [Real.rpow_one, show (1:ℝ) + -(1/3) = 2/3 by norm_num] at h
    exact h
  have hvsplit : |t| ^ (-(1 / 3) : ℝ) = 1 / v := by
    have h : |t| ^ (-(1/3):ℝ) = (|t| ^ (1/3:ℝ))⁻¹ := Real.rpow_neg (le_of_lt htpos) (1/3)
    rw [h, ← hvdef, inv_eq_one_div]
  have hB : 24 * Real.pi * (M : ℝ) ^ (1 / 3 : ℝ) / |t| ≤ 48 * Real.pi / v := by
    have hroot : (M : ℝ) ^ (1 / 3 : ℝ) ≤ 2 * |t| ^ (2/3:ℝ) := by
      have h1 : (M : ℝ) ^ (1 / 3 : ℝ) ≤ ((2 * |t|) ^ 2) ^ (1 / 3 : ℝ) :=
        Real.rpow_le_rpow hMpos.le hMle (by norm_num)
      have h2 : ((2 * |t|) ^ 2) ^ (1 / 3 : ℝ) = (2 * |t|) ^ (2 / 3 : ℝ) := by
        rw [← Real.rpow_natCast (2 * |t|) 2, ← Real.rpow_mul (by positivity : (0:ℝ) ≤ 2 * |t|)]
        norm_num
      rw [h2] at h1
      have h3 : (2 * |t|) ^ (2 / 3 : ℝ) = 2 ^ (2 / 3 : ℝ) * |t| ^ (2 / 3 : ℝ) :=
        Real.mul_rpow (by norm_num) htpos.le
      rw [h3] at h1
      have h4 : (2 : ℝ) ^ (2 / 3 : ℝ) ≤ 2 := by
        calc (2 : ℝ) ^ (2 / 3 : ℝ) ≤ (2 : ℝ) ^ (1 : ℝ) :=
              Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
          _ = 2 := Real.rpow_one 2
      nlinarith [h1, h4, Real.rpow_nonneg htpos.le (2/3:ℝ)]
    have h1 : 24 * Real.pi * (M : ℝ) ^ (1 / 3 : ℝ) / |t| ≤
        24 * Real.pi * (2 * |t| ^ (2 / 3 : ℝ)) / |t| := by gcongr
    rw [show 24 * Real.pi * (2 * |t| ^ (2/3:ℝ)) / |t| =
      48 * Real.pi * (|t| ^ (2/3:ℝ) / |t|) by ring, hthird] at h1
    rw [hvsplit] at h1
    have h5 : (|t| * (1 / v)) / |t| = 1 / v := by field_simp
    have h6 : 48 * Real.pi * (|t| * (1/v) / |t|) = 48 * Real.pi / v := by
      rw [h5]; ring
    linarith [h1, h6.le, h6.ge]
  have hAnn : 0 ≤ 6 + 12 * v := by linarith
  have hBnn : 0 ≤ 24 * Real.pi * (M : ℝ) ^ (1 / 3 : ℝ) / |t| := by positivity
  have hfin : (6 + 12 * v) * (48 * Real.pi / v) ≤ 4000 := by
    have h1 : (6 + 12 * v) / v = 6 / v + 12 := by field_simp
    have h2 : 6 / v + 12 ≤ 18 := by
      have h3 : 1 / v ≤ 1 := by rw [div_le_one hvpos]; linarith
      have h4 : 6 / v = 6 * (1 / v) := by ring
      linarith
    have h5 : (6 + 12 * v) * (48 * Real.pi / v) = 48 * Real.pi * ((6 + 12 * v) / v) := by ring
    rw [h5, h1]
    nlinarith [h2, Real.pi_lt_four, Real.pi_pos]
  exact le_trans (mul_le_mul hA hB hBnn hAnn) hfin

/-! ## The shift-difference series in the VK strip -/

/-- The constant dominating the shift-difference series. -/
private noncomputable def seriesConst (Cvk cvk Ab : ℝ) : ℝ :=
  10 * Real.exp 4 * (3 + cvk ^ (-(6 / 7 : ℝ))) +
    (2 + 2 * Cvk * Real.exp (1 / 2) * Ab + 4000 + 200)

private lemma seriesConst_apply (Cvk cvk Ab : ℝ) :
    seriesConst Cvk cvk Ab =
      10 * Real.exp 4 * (3 + cvk ^ (-(6 / 7 : ℝ))) +
        (2 + 2 * Cvk * Real.exp (1 / 2) * Ab + 4000 + 200) := rfl

/-- Arithmetic: the head and the bounded pieces are dominated by `seriesConst`. -/
private lemma seriesConst_ge {Cvk cvk Ab a σ κ L : ℝ} (hCvk0 : 0 ≤ Cvk) (hcvk0 : 0 < cvk)
    (hAb0 : 0 ≤ Ab) (hL1 : 1 ≤ L) (hκ : κ = cvk ^ (-(6 / 7 : ℝ)) * L ^ (6 / 7 : ℝ))
    (ha : 0 ≤ a ^ (-σ)) :
    a ^ (-σ) + 10 * Real.exp 4 * (3 + κ) + (2 + 2 * Cvk * Real.exp (1 / 2) * Ab + 4000 + 4)
      ≤ seriesConst Cvk cvk Ab * (a ^ (-σ) + L ^ (6 / 7 : ℝ)) := by
  set X : ℝ := 10 * Real.exp 4 * (3 + cvk ^ (-(6 / 7 : ℝ))) with hXdef
  set Y : ℝ := 2 + 2 * Cvk * Real.exp (1 / 2) * Ab + 4000 + 200 with hYdef
  have hL67 : (1 : ℝ) ≤ L ^ (6 / 7 : ℝ) := Real.one_le_rpow hL1 (by norm_num)
  have he4 : (1 : ℝ) ≤ Real.exp 4 := Real.one_le_exp (by norm_num)
  have hcv : 0 < cvk ^ (-(6 / 7 : ℝ)) := Real.rpow_pos_of_pos hcvk0 _
  have hX1 : (1 : ℝ) ≤ X := by
    rw [hXdef]
    nlinarith [he4, hcv]
  have hYnn : 0 ≤ Y := by
    rw [hYdef]
    have h1 : 0 ≤ Real.exp (1 / 2 : ℝ) := (Real.exp_pos _).le
    have h2 : 0 ≤ 2 * Cvk * Real.exp (1 / 2 : ℝ) * Ab := by positivity
    linarith
  have key1 : a ^ (-σ) ≤ X * a ^ (-σ) := by
    rw [hXdef]
    exact le_mul_of_one_le_left ha hX1
  have key2 : 10 * Real.exp 4 * (3 + κ) ≤ X * L ^ (6 / 7 : ℝ) := by
    rw [hXdef, hκ]
    nlinarith [hL67, he4, hcv]
  have key3 : 2 + 2 * Cvk * Real.exp (1 / 2) * Ab + 4000 + 4 ≤
      Y * (a ^ (-σ) + L ^ (6 / 7 : ℝ)) := by
    have h1 : 2 + 2 * Cvk * Real.exp (1 / 2) * Ab + 4000 + 4 ≤ Y := by
      rw [hYdef]; linarith
    have h2 : Y * 1 ≤ Y * (a ^ (-σ) + L ^ (6 / 7 : ℝ)) := by
      refine mul_le_mul_of_nonneg_left ?_ hYnn
      linarith
    linarith
  have hrhs : (X + Y) * (a ^ (-σ) + L ^ (6 / 7 : ℝ)) =
      X * a ^ (-σ) + X * L ^ (6 / 7 : ℝ) + Y * (a ^ (-σ) + L ^ (6 / 7 : ℝ)) := by ring
  rw [seriesConst_apply]
  rw [show (10 * Real.exp 4 * (3 + cvk ^ (-(6 / 7 : ℝ))) +
      (2 + 2 * Cvk * Real.exp (1 / 2) * Ab + 4000 + 200)) =
      X + Y from by rw [hXdef, hYdef], hrhs]
  linarith [key1, key2, key3]

/-- The far tail of the shift-difference series is `O(1)` (case `K₀ ≤ Nt`). -/
private lemma shiftTerm_tsum_tail_le_far {a σ t : ℝ} (ha : 0 < a) (ha1 : a ≤ 1)
    (hσ0 : 0 < σ) (hσ23 : (2:ℝ)/3 ≤ σ) (ht3 : 3 ≤ |t|) {M : ℕ}
    (hM : |t| ^ 2 ≤ (M : ℝ)) :
    ‖∑' m : ℕ, Work.BMF.shiftTerm a (M + 1 + m) ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤ 4 := by
  set s : ℂ := (σ : ℂ) + (t : ℂ) * Complex.I with hsdef
  have hsre : s.re = σ := by simp [hsdef]
  have htpos : (0 : ℝ) < |t| := by linarith
  have ht1' : (1 : ℝ) ≤ |t| := by linarith
  have hMpos : (0 : ℝ) < (M : ℝ) := by
    have : (0:ℝ) < |t| ^ 2 := by positivity
    linarith
  have h := Work.BMF.norm_tsum_shiftTerm_tail_le ha ha1 (by rw [hsre]; exact hσ0) (M + 1)
  rw [hsre] at h
  have hnorm : ‖s‖ ≤ σ + |t| := by
    rw [hsdef]
    have h1 := norm_add_le (σ : ℂ) ((t : ℂ) * Complex.I)
    have h2 : ‖(σ : ℂ)‖ = σ := by simp [abs_of_pos hσ0]
    have h3 : ‖(t : ℂ) * Complex.I‖ = |t| := by simp
    rw [h2, h3] at h1
    exact h1
  have h1 : (((M + 1 : ℕ) : ℝ) + a) ^ (-σ) ≤ (|t| ^ 2) ^ (-σ) := by
    refine Real.rpow_le_rpow_of_nonpos (by positivity) ?_ (by linarith)
    push_cast
    linarith
  have h2 : (|t| ^ 2) ^ (-σ) ≤ (|t| ^ 2) ^ (-(2 / 3 : ℝ)) := by
    refine Real.rpow_le_rpow_of_exponent_le ?_ ?_
    · have : (1 : ℝ) ≤ |t| ^ 2 := by nlinarith [ht1']
      linarith
    · linarith
  have h3 : (|t| ^ 2) ^ (-(2 / 3 : ℝ)) = |t| ^ (-(1 / 3 : ℝ)) / |t| := by
    rw [← Real.rpow_natCast |t| 2, ← Real.rpow_mul (le_of_lt htpos),
      show (↑(2:ℕ) : ℝ) * (-(2 / 3 : ℝ)) = (-(1 / 3 : ℝ)) - 1 by norm_num,
      Real.rpow_sub htpos, Real.rpow_one]
  have h4 : |t| ^ (-(1 / 3 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos ht1' (by norm_num)
  have h5 : (‖s‖ / σ) ≤ 4 * |t| := by
    rw [div_le_iff₀ hσ0]
    nlinarith [hnorm, hσ0, hσ23, ht1']
  have hb : (‖s‖ / σ) * ((((M + 1 : ℕ) : ℝ) + a) ^ (-σ)) ≤ 4 := by
    calc (‖s‖ / σ) * ((((M + 1 : ℕ) : ℝ) + a) ^ (-σ))
        ≤ (4 * |t|) * ((|t| ^ 2) ^ (-(2 / 3 : ℝ))) :=
          mul_le_mul h5 (le_trans h1 h2) (by positivity) (by positivity)
      _ = 4 * (|t| ^ (-(1 / 3 : ℝ))) := by rw [h3]; field_simp
      _ ≤ 4 * 1 := by linarith [h4]
      _ = 4 := by ring
  linarith [h, hb]

/-- The tail of the shift-difference series beyond `K₀` is `O(1)` when `K₀ ≳ |t|`. -/
private lemma shiftTerm_tsum_tail_le_near {a σ t κ : ℝ} {K₀ : ℕ} (ha : 0 < a) (ha1 : a ≤ 1)
    (hσ0 : 0 < σ) (hσ12 : (1:ℝ)/2 ≤ σ) (hσ2 : σ ≤ 2) (hσκ : κ - 1 / 2 ≤ σ * κ)
    (ht3 : 3 ≤ |t|) (hK₀low : Real.exp (κ + 1) / 2 ≤ (K₀ : ℝ))
    (hgt : |t| ≤ Real.exp (κ + 1)) :
    ‖∑' m : ℕ, Work.BMF.shiftTerm a (K₀ + m) ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤ 200 := by
  set s : ℂ := (σ : ℂ) + (t : ℂ) * Complex.I with hsdef
  have hsre : s.re = σ := by simp [hsdef]
  have htpos : (0 : ℝ) < |t| := by linarith
  have ht1' : (1 : ℝ) ≤ |t| := by linarith
  have hexpκ : (0:ℝ) < Real.exp (κ + 1) := Real.exp_pos _
  have h := Work.BMF.norm_tsum_shiftTerm_tail_le ha ha1 (by rw [hsre]; exact hσ0) K₀
  rw [hsre] at h
  have hnorm : ‖s‖ ≤ σ + |t| := by
    rw [hsdef]
    have h1 := norm_add_le (σ : ℂ) ((t : ℂ) * Complex.I)
    have h2 : ‖(σ : ℂ)‖ = σ := by simp [abs_of_pos hσ0]
    have h3 : ‖(t : ℂ) * Complex.I‖ = |t| := by simp
    rw [h2, h3] at h1
    exact h1
  have h1 : (((K₀ : ℝ) + a) ^ (-σ)) ≤ (Real.exp (κ + 1) / 2) ^ (-σ) := by
    refine Real.rpow_le_rpow_of_nonpos (by positivity) ?_ (by linarith)
    linarith
  have h3 : (Real.exp (κ + 1) / 2) ^ (-σ) = Real.exp (-(σ * (κ + 1))) * 2 ^ σ := by
    rw [Real.div_rpow hexpκ.le (by norm_num : (0:ℝ) ≤ 2),
      Real.rpow_def_of_pos hexpκ, Real.log_exp,
      Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2), div_inv_eq_mul]
    congr 1
    ring_nf
  have h4 : (2:ℝ) ^ σ ≤ 4 := by
    have h5 : (2:ℝ) ^ σ ≤ (2:ℝ) ^ (2:ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) hσ2
    have h6 : (2:ℝ) ^ (2:ℝ) = 4 := by norm_num
    linarith [h5, h6.le, h6.ge]
  have h5' : Real.exp (-(σ * (κ + 1))) ≤ Real.exp ((1/2:ℝ) - κ) := by
    rw [Real.exp_le_exp]
    nlinarith [hσκ, hσ0]
  have h2 : (Real.exp (κ + 1) / 2) ^ (-σ) ≤ 4 * Real.exp ((1/2:ℝ) - κ) := by
    rw [h3]
    calc Real.exp (-(σ * (κ + 1))) * 2 ^ σ ≤ Real.exp ((1/2:ℝ) - κ) * 4 :=
          mul_le_mul h5' h4 (by positivity) (Real.exp_pos _).le
      _ = 4 * Real.exp ((1/2:ℝ) - κ) := by ring
  have h5 : (‖s‖ / σ) ≤ 4 * |t| := by
    rw [div_le_iff₀ hσ0]
    nlinarith [hnorm, hσ0, hσ12, ht1']
  have h10 : Real.exp (3/2 : ℝ) ≤ 12 := by
    refine (Real.le_log_iff_exp_le (by norm_num : (0:ℝ) < 12)).mp ?_
    have h1 : Real.log 8 ≤ Real.log 12 := Real.log_le_log (by norm_num) (by norm_num)
    have h2 : Real.log 8 = 3 * Real.log 2 := by
      rw [show (8:ℝ) = 2^3 by norm_num, Real.log_pow]; norm_num
    have h3 : (1/2:ℝ) ≤ Real.log 2 := by have := Real.log_two_gt_d9; linarith
    linarith
  have h6 : (4 * |t|) * (4 * Real.exp ((1/2:ℝ) - κ)) ≤ 200 := by
    have h7 : (4 * |t|) * (4 * Real.exp ((1/2:ℝ) - κ)) ≤
        (4 * Real.exp (κ + 1)) * (4 * Real.exp ((1/2:ℝ) - κ)) := by
      refine mul_le_mul_of_nonneg_right ?_ (by positivity)
      nlinarith [hgt]
    have h9 : (4 * Real.exp (κ + 1)) * (4 * Real.exp ((1/2:ℝ) - κ)) =
        16 * Real.exp (3/2 : ℝ) := by
      rw [show (4 * Real.exp (κ + 1)) * (4 * Real.exp ((1/2:ℝ) - κ)) =
          16 * (Real.exp (κ + 1) * Real.exp ((1/2:ℝ) - κ)) by ring,
        ← Real.exp_add, show κ + 1 + ((1/2:ℝ) - κ) = 3/2 by ring]
    rw [h9] at h7
    linarith [h7, h10]
  have hb : (‖s‖ / σ) * (((K₀ : ℝ) + a) ^ (-σ)) ≤ 200 := by
    calc (‖s‖ / σ) * (((K₀ : ℝ) + a) ^ (-σ))
        ≤ (4 * |t|) * (4 * Real.exp ((1/2:ℝ) - κ)) :=
          mul_le_mul h5 (le_trans h1 h2) (by positivity) (by positivity)
      _ ≤ 200 := h6
  linarith [h, hb]

/-- `VKExpInput` is monotone in the saving parameter (a smaller `c` gives a weaker hypothesis
and a weaker conclusion). -/
private lemma VKExpInput_mono_c {C c c' : ℝ} (h : VKExpInput C c) (hc0 : 0 < c)
    (hc'0 : 0 < c') (hc' : c' ≤ c) : VKExpInput C c' := by
  obtain ⟨hC, _hc, hb⟩ := h
  refine ⟨hC, hc'0, fun N t hN hNt hlog u hu hu1 R hNR hR2N => ?_⟩
  have hN1 : (1:ℝ) ≤ N := by linarith
  have hlog' : Real.log t ≤ c * Real.log N ^ (7 / 6 : ℝ) :=
    le_trans hlog (mul_le_mul_of_nonneg_right hc'
      (Real.rpow_nonneg (Real.log_nonneg (by linarith : (1:ℝ) ≤ N)) _))
  refine le_trans (hb N t hN hNt hlog' u hu hu1 R hNR hR2N) ?_
  set A : ℝ := (Real.log N / Real.log t) ^ 2 with hAdef
  set D : ℝ := Real.log (Real.log t / Real.log N + 2) with hDdef
  have hAn : 0 ≤ A := by rw [hAdef]; exact sq_nonneg _
  have hDn : 0 < D := by
    rw [hDdef]
    apply Real.log_pos
    have h3 : Real.log N ≤ Real.log t := Real.log_le_log (by linarith) hNt
    have h4 : 0 < Real.log N := Real.log_pos (by linarith)
    have h5 : 1 ≤ Real.log t / Real.log N := (le_div_iff₀ h4).mpr (by linarith)
    linarith
  have hexp : 1 - c * A / D ≤ 1 - c' * A / D := by
    have h1 : c' * A ≤ c * A := mul_le_mul_of_nonneg_right hc' hAn
    have h2 : c' * A / D ≤ c * A / D := div_le_div_of_nonneg_right h1 hDn.le
    linarith
  exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hN1 hexp) hC.le

/-! ## The series bound -/

private lemma shift_series_sum_bound {Cvk cvk Ab ch : ℝ} (hVK : VKExpInput Cvk cvk)
    (hcvk0 : 0 < cvk) (hcvk1 : cvk ≤ 1) (hAb0 : 0 < Ab)
    (hAbb : ∀ L : ℝ, 1 ≤ L → (1 + L / Real.log 2) * Real.exp
      (-(cvk * ((L / cvk) ^ (6 / 7 : ℝ)) ^ 3 /
        (L ^ 2 * Real.log (cvk ^ (6 / 7 : ℝ) * L ^ (1 / 7 : ℝ) + 2)))) ≤ Ab)
    (hch1 : ch ≤ 1 / 4) (hch2 : ch ≤ cvk ^ (6 / 7 : ℝ) / 2)
    {a σ t : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) (ht3 : 3 ≤ |t|)
    (hσlo : 1 - ch * Real.log (|t| + 3) ^ (-(6 / 7 : ℝ)) ≤ σ) (hσhi : σ ≤ 2) :
    ‖∑' m : ℕ, Work.BMF.shiftTerm a m ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤
      seriesConst Cvk cvk Ab * (a ^ (-σ) + Real.log (|t| + 3) ^ (6 / 7 : ℝ)) := by
  set L : ℝ := Real.log (|t| + 3) with hLdef
  set s : ℂ := (σ : ℂ) + (t : ℂ) * Complex.I with hsdef
  have hL1 : 1 ≤ L := by
    rw [hLdef]
    have h1 : (1:ℝ) < Real.log 3 := by
      rw [Real.lt_log_iff_exp_lt (by norm_num)]
      exact Real.exp_one_lt_three
    have h2 : Real.log 3 ≤ Real.log (|t| + 3) :=
      Real.log_le_log (by norm_num) (by linarith [abs_nonneg t])
    linarith
  have hLpos : 0 < L := lt_of_lt_of_le zero_lt_one hL1
  have hLnn : 0 ≤ L := hLpos.le
  have hsre : s.re = σ := by simp [hsdef]
  have hLpow : L ^ (-(6 / 7 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hL1 (by norm_num)
  have h1σ : 1 - σ ≤ ch * L ^ (-(6 / 7 : ℝ)) := by linarith [hσlo]
  have h1σ4 : 1 - σ ≤ 1 / 4 := by
    have h : ch * L ^ (-(6/7:ℝ)) ≤ (1/4) * 1 :=
      mul_le_mul hch1 hLpow (Real.rpow_nonneg hLpos.le _) (by norm_num)
    linarith
  have hσ0 : 0 < σ := by linarith
  have hσ23 : (2:ℝ)/3 ≤ σ := by linarith
  have hs0 : 0 < s.re := by rw [hsre]; exact hσ0
  have hs1 : s ≠ 1 := by
    intro hcon
    have h2 : t = 0 := by
      have := congrArg Complex.im hcon
      simpa [hsdef] using this
    rw [h2] at ht3
    have h3 : (3:ℝ) ≤ 0 := by simpa using ht3
    norm_num at h3
  have hsumm : Summable (fun m : ℕ => Work.BMF.shiftTerm a m s) := by
    have h := Work.BMF.summable_norm_shiftTerm ha ha1 hs0 0
    exact (by simpa using h : Summable (fun m : ℕ => ‖Work.BMF.shiftTerm a m s‖)).of_norm
  set κ : ℝ := (L / cvk) ^ (6 / 7 : ℝ) with hκdef
  have hκ0 : 0 ≤ κ := Real.rpow_nonneg (div_nonneg hLnn hcvk0.le) _
  have hκneg : κ = cvk ^ (-(6 / 7 : ℝ)) * L ^ (6 / 7 : ℝ) := by
    rw [hκdef, Real.div_rpow hLnn hcvk0.le, div_eq_mul_inv, ← Real.rpow_neg hcvk0.le]
    ring
  have h1σκ : (1 - σ) * κ ≤ 1 / 2 := by
    have h1 : (1 - σ) * κ ≤ (ch * L ^ (-(6/7:ℝ))) * κ :=
      mul_le_mul_of_nonneg_right h1σ hκ0
    have hLmul : L ^ (-(6/7:ℝ)) * L ^ (6/7:ℝ) = 1 := by
      rw [← Real.rpow_add hLpos, show (-(6/7:ℝ) + 6/7) = 0 by norm_num, Real.rpow_zero]
    have h2 : ch * L ^ (-(6/7:ℝ)) * κ = ch * cvk ^ (-(6/7:ℝ)) := by
      rw [hκneg]
      calc ch * L ^ (-(6/7:ℝ)) * (cvk ^ (-(6/7:ℝ)) * L ^ (6/7:ℝ))
          = ch * cvk ^ (-(6/7:ℝ)) * (L ^ (-(6/7:ℝ)) * L ^ (6/7:ℝ)) := by ring
        _ = ch * cvk ^ (-(6/7:ℝ)) * 1 := by rw [hLmul]
        _ = ch * cvk ^ (-(6/7:ℝ)) := by ring
    have h3 : ch * cvk ^ (-(6/7:ℝ)) ≤ (cvk^(6/7:ℝ)/2) * cvk^ (-(6/7:ℝ)) :=
      mul_le_mul_of_nonneg_right hch2 (Real.rpow_nonneg hcvk0.le _)
    have h4 : (cvk^(6/7:ℝ)/2) * cvk^(-(6/7:ℝ)) = 1/2 := by
      rw [div_mul_eq_mul_div, ← Real.rpow_add hcvk0, show (6/7:ℝ) + -(6/7) = 0 by norm_num,
        Real.rpow_zero]
      try norm_num
    linarith [h1, h2.le, h2.ge, h3, h4.le, h4.ge]
  set K₀ : ℕ := ⌊Real.exp (κ + 1)⌋₊ with hK₀def
  have hee2 : (2:ℝ) ≤ Real.exp (κ + 1) := by
    have h1 : (1:ℝ) ≤ κ + 1 := by linarith
    calc (2:ℝ) = 1 + 1 := by norm_num
      _ ≤ Real.exp 1 := by have := Real.add_one_le_exp 1; linarith
      _ ≤ Real.exp (κ + 1) := Real.exp_le_exp.mpr h1
  have hK₀2 : 2 ≤ K₀ := by
    rw [hK₀def]
    exact Nat.le_floor (by exact_mod_cast hee2)
  have hK₀low : Real.exp (κ + 1) / 2 ≤ (K₀ : ℝ) := by
    have h : Real.exp (κ + 1) < (K₀ : ℝ) + 1 := by
      rw [hK₀def]; exact Nat.lt_floor_add_one _
    linarith
  have hK₀le : (K₀ : ℝ) ≤ Real.exp (κ + 1) + 2 := by
    have h : (K₀ : ℝ) ≤ Real.exp (κ + 1) := by
      rw [hK₀def]; exact Nat.floor_le (Real.exp_pos _).le
    linarith
  have hlogK₀ : κ ≤ Real.log (K₀ : ℝ) := by
    have h2 : 0 < Real.exp (κ + 1) / 2 := by positivity
    have h3 : Real.log (Real.exp (κ + 1) / 2) ≤ Real.log (K₀ : ℝ) :=
      Real.log_le_log h2 hK₀low
    rw [Real.log_div (Real.exp_ne_zero _) (by norm_num), Real.log_exp] at h3
    have hlog2 : Real.log 2 ≤ 1 := by
      have := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 2); linarith
    linarith
  -- head bound
  have h1σκ' : (1 - σ) * (κ + 1) ≤ 1 := by nlinarith [h1σκ, h1σ4]
  have hhead : ‖∑ m ∈ Finset.range K₀, Work.BMF.shiftTerm a m s‖ ≤
      a ^ (-σ) + 10 * Real.exp 4 * (3 + κ) := by
    have hb := Work.BMF.VKChain.shift_head_bound (K₀ := K₀) (a := a) (σ := σ) (t := t)
      (κ := κ + 1) ha hσ0 hσhi (by linarith) h1σκ' (by linarith [hK₀le])
    calc ‖∑ m ∈ Finset.range K₀, Work.BMF.shiftTerm a m s‖
        ≤ a ^ (-σ) + 2 * ((Real.exp 4 * 5) * (2 + (κ + 1))) := hb
      _ = a ^ (-σ) + 10 * Real.exp 4 * (3 + κ) := by ring
  -- single term
  have hsingle : ‖Work.BMF.shiftTerm a K₀ s‖ ≤ 2 := by
    have h1 : ‖((((K₀ : ℝ) + a : ℝ)) : ℂ) ^ (-s)‖ ≤ 1 := by
      rw [Complex.norm_cpow_eq_rpow_re_of_pos (by positivity : (0:ℝ) < (K₀ : ℝ) + a)]
      have h2 : (-s).re = -σ := by rw [Complex.neg_re, hsre]
      rw [h2]
      exact Real.rpow_le_one_of_one_le_of_nonpos (by linarith) (by linarith)
    have h2 : ‖((((K₀ + 1 : ℕ) : ℝ)) : ℂ) ^ (-s)‖ ≤ 1 := by
      rw [Complex.norm_cpow_eq_rpow_re_of_pos (by positivity : (0:ℝ) < ((K₀ + 1 : ℕ) : ℝ))]
      have h3 : (-s).re = -σ := by rw [Complex.neg_re, hsre]
      rw [h3]
      exact Real.rpow_le_one_of_one_le_of_nonpos (by push_cast; linarith) (by linarith)
    simp only [Work.BMF.shiftTerm]
    exact le_trans (norm_sub_le _ _) (by linarith)
  set Nt : ℕ := ⌊|t|⌋₊ + 1 with hNtdef
  have hNt1 : 1 ≤ Nt := by simp [hNtdef]
  have hNtge : |t| ≤ (Nt : ℝ) := by
    have := Nat.lt_floor_add_one |t|
    rw [hNtdef]; push_cast; linarith
  have hNtle : (Nt : ℝ) ≤ |t| + 1 := by
    have := Nat.floor_le (abs_nonneg t)
    rw [hNtdef]; push_cast; linarith
  have hNtpos : (0:ℝ) < (Nt : ℝ) := by exact_mod_cast (by omega : 0 < Nt)
  have hCvknn : (0:ℝ) ≤ Cvk := hVK.1.le
  have hsumnn : 0 ≤ a ^ (-σ) := Real.rpow_nonneg ha.le _
  by_cases hcase : K₀ ≤ Nt
  · -- Case A: `K₀ ≤ Nt`
    set M : ℕ := Nt * Nt with hMdef
    have hNtM : Nt ≤ M := by
      rw [hMdef]
      exact Nat.le_mul_of_pos_right Nt (by omega : 0 < Nt)
    have hMcast : (M : ℝ) = (Nt : ℝ) * (Nt : ℝ) := by rw [hMdef]; push_cast; ring
    have hMge : |t| ^ 2 ≤ (M : ℝ) := by
      rw [pow_two, hMcast]
      exact mul_le_mul hNtge hNtge (abs_nonneg t) (le_of_lt hNtpos)
    -- VK piece
    have hVKmid : ‖∑ m ∈ Finset.Ioc K₀ Nt, Work.BMF.shiftTerm a m s‖
        ≤ 2 * Cvk * Real.exp (1 / 2) * Ab := by
      have hσδ : 1 - σ ≤ cvk ^ (6 / 7 : ℝ) / 2 * L ^ (-(6 / 7 : ℝ)) := by
        have h2 : ch * L ^ (-(6 / 7 : ℝ)) ≤ cvk ^ (6 / 7 : ℝ) / 2 * L ^ (-(6 / 7 : ℝ)) :=
          mul_le_mul_of_nonneg_right hch2 (Real.rpow_nonneg hLnn _)
        linarith [h1σ, h2]
      exact Work.BMF.VKChain.shift_vk_range_bound (Cvk := Cvk) (cvk := cvk) (Ab := Ab)
        (a := a) (σ := σ) (t := t) (K₀ := K₀) (Nt := Nt)
        hVK hcvk0 hcvk1 ha ha1 ht3 hσ0 hσhi hσδ hK₀2 hNtle hcase hlogK₀ (hAbb L hL1)
    -- KL piece
    have hKL : ‖∑ m ∈ Finset.Ioc Nt M, Work.BMF.shiftTerm a m s‖ ≤ 4000 := by
      have hb := Work.BMF.VKChain.shiftTerm_kl_range_le
        (hkl := by
          intro u σ' t' hu hu1 hσ' ht'
          exact Work.BMF.VKChain.kl_tail_block_bound hu hu1 hσ' ht')
        (a := a) (σ := σ) (t := t) (Nt := Nt) (M := M)
        ha ha1 hσ0 ht3 hσ23 hNtge hNt1 hNtM
      exact le_trans hb (kl_piece_arith hNt1 hNtge hNtle ht3 hMcast)
    have htail := shiftTerm_tsum_tail_le_far ha ha1 hσ0 hσ23 ht3 hMge
    have hsplit1 : (∑' m : ℕ, Work.BMF.shiftTerm a m s) =
        (∑ m ∈ Finset.range (K₀ + 1), Work.BMF.shiftTerm a m s)
          + ∑' m : ℕ, Work.BMF.shiftTerm a ((K₀ + 1) + m) s := by
      have h := hsumm.sum_add_tsum_nat_add (K₀ + 1)
      rw [← h]
      congr 1
      exact tsum_congr (fun m => by rw [Nat.add_comm])
    have hsplit2 := tsum_split_Ico hsumm (K := K₀ + 1) (N := Nt + 1) (by omega)
    have hsplit3 := tsum_split_Ico hsumm (K := Nt + 1) (N := M + 1) (by omega)
    have hIco2 : (∑ m ∈ Finset.Ico (K₀ + 1) (Nt + 1), Work.BMF.shiftTerm a m s)
        = ∑ m ∈ Finset.Ioc K₀ Nt, Work.BMF.shiftTerm a m s :=
      (sum_Ioc_eq_Ico_sum _ _ _).symm
    have hIco3 : (∑ m ∈ Finset.Ico (Nt + 1) (M + 1), Work.BMF.shiftTerm a m s)
        = ∑ m ∈ Finset.Ioc Nt M, Work.BMF.shiftTerm a m s :=
      (sum_Ioc_eq_Ico_sum _ _ _).symm
    set A1 : ℂ := ∑ m ∈ Finset.range K₀, Work.BMF.shiftTerm a m s with hA1def
    set b1 : ℂ := Work.BMF.shiftTerm a K₀ s with hb1def
    set C1 : ℂ := ∑ m ∈ Finset.Ico (K₀ + 1) (Nt + 1), Work.BMF.shiftTerm a m s with hC1def
    set D1 : ℂ := ∑ m ∈ Finset.Ico (Nt + 1) (M + 1), Work.BMF.shiftTerm a m s with hD1def
    set E1 : ℂ := ∑' m : ℕ, Work.BMF.shiftTerm a (M + 1 + m) s with hE1def
    have hA1b : ‖A1‖ ≤ a ^ (-σ) + 10 * Real.exp 4 * (3 + κ) := hhead
    have hb1b : ‖b1‖ ≤ 2 := hsingle
    have hC1b : ‖C1‖ ≤ 2 * Cvk * Real.exp (1 / 2) * Ab := by
      rw [hIco2]
      exact hVKmid
    have hD1b : ‖D1‖ ≤ 4000 := by
      rw [hIco3]
      exact hKL
    have hE1b : ‖E1‖ ≤ 4 := htail
    have hsum_eq : (∑' m : ℕ, Work.BMF.shiftTerm a m s) = A1 + (b1 + (C1 + (D1 + E1))) := by
      rw [hA1def, hb1def, hC1def, hD1def, hE1def]
      rw [hsplit1, Finset.sum_range_succ, hsplit2, hsplit3]
      ring
    have hstep1 : ‖∑' m : ℕ, Work.BMF.shiftTerm a m s‖ ≤
        ‖A1‖ + ‖b1‖ + (‖C1‖ + (‖D1‖ + ‖E1‖)) := by
      rw [hsum_eq]
      have h1 := norm_add_le A1 (b1 + (C1 + (D1 + E1)))
      have h2 := norm_add_le b1 (C1 + (D1 + E1))
      have h3 := norm_add_le C1 (D1 + E1)
      have h4 := norm_add_le D1 E1
      linarith
    have hstep2 : ‖A1‖ + ‖b1‖ + (‖C1‖ + (‖D1‖ + ‖E1‖)) ≤
        a ^ (-σ) + 10 * Real.exp 4 * (3 + κ) +
          (2 + 2 * Cvk * Real.exp (1 / 2) * Ab + 4000 + 4) := by
      linarith [hA1b, hb1b, hC1b, hD1b, hE1b]
    have hstep3 := seriesConst_ge (Cvk := Cvk) (cvk := cvk) (Ab := Ab) (a := a) (σ := σ)
      (κ := κ) (L := L) hCvknn hcvk0 hAb0.le hL1 hκneg hsumnn
    linarith [hstep1, hstep2, hstep3]
  · -- Case B: `Nt < K₀`
    have hK₀gt : (Nt : ℝ) < (K₀ : ℝ) := by
      exact_mod_cast (lt_of_not_ge hcase)
    have hgt : |t| ≤ Real.exp (κ + 1) := by
      have h2 : (K₀ : ℝ) ≤ Real.exp (κ + 1) := by
        rw [hK₀def]; exact Nat.floor_le (Real.exp_pos _).le
      linarith [hNtge]
    have hσκ : κ - 1 / 2 ≤ σ * κ := by nlinarith [h1σκ]
    have hsplitB : (∑' m : ℕ, Work.BMF.shiftTerm a m s) =
        (∑ m ∈ Finset.range K₀, Work.BMF.shiftTerm a m s)
          + ∑' m : ℕ, Work.BMF.shiftTerm a (K₀ + m) s := by
      have h := hsumm.sum_add_tsum_nat_add K₀
      rw [← h]
      congr 1
      exact tsum_congr (fun m => by rw [Nat.add_comm])
    have hσ12 : (1:ℝ)/2 ≤ σ := by linarith
    have htailB := shiftTerm_tsum_tail_le_near (κ := κ) (K₀ := K₀) ha ha1 hσ0 hσ12 hσhi hσκ ht3
      hK₀low hgt
    have hstep1 : ‖∑' m : ℕ, Work.BMF.shiftTerm a m s‖ ≤
        ‖∑ m ∈ Finset.range K₀, Work.BMF.shiftTerm a m s‖
          + ‖∑' m : ℕ, Work.BMF.shiftTerm a (K₀ + m) s‖ := by
      rw [hsplitB]; exact norm_add_le _ _
    have hstep2 : ‖∑ m ∈ Finset.range K₀, Work.BMF.shiftTerm a m s‖
          + ‖∑' m : ℕ, Work.BMF.shiftTerm a (K₀ + m) s‖ ≤
        a ^ (-σ) + 10 * Real.exp 4 * (3 + κ) + 200 := by
      linarith [hhead, htailB]
    have h200 : a ^ (-σ) + 10 * Real.exp 4 * (3 + κ) + 200 ≤
        a ^ (-σ) + 10 * Real.exp 4 * (3 + κ) +
          (2 + 2 * Cvk * Real.exp (1 / 2) * Ab + 4000 + 4) := by
      have h1 : (200:ℝ) ≤ 2 + 2 * Cvk * Real.exp (1 / 2) * Ab + 4000 + 4 := by
        have h2 : 0 ≤ 2 * Cvk * Real.exp (1 / 2) * Ab := by positivity
        linarith
      linarith
    have hstep3 := seriesConst_ge (Cvk := Cvk) (cvk := cvk) (Ab := Ab) (a := a) (σ := σ)
      (κ := κ) (L := L) hCvknn hcvk0 hAb0.le hL1 hκneg hsumnn
    linarith [hstep1, hstep2, h200, hstep3]

/-! ## The Hurwitz-zeta growth bound -/

theorem hurwitz_growth_local (hVK : ∃ C c : ℝ, VKExpInput C c) :
    ∃ A c : ℝ, 0 < A ∧ 0 < c ∧ c ≤ 1 / 4 ∧
      ∀ (a σ t : ℝ), 0 ≤ a → a ≤ 1 → 3 ≤ |t| →
        1 - c * Real.log (|t| + 3) ^ (-(6 / 7 : ℝ)) ≤ σ → σ ≤ 2 →
        ‖HurwitzZeta.hurwitzZeta (a : UnitAddCircle) ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤
          A * (a ^ (-σ) + Real.log (|t| + 3) ^ (6 / 7 : ℝ)) := by
  obtain ⟨Cvk0, cvk0, hCvk0, hcvk0, hbody⟩ := hVK
  set Cvk : ℝ := Cvk0 with hCvkdef
  set cvk : ℝ := min cvk0 1 with hcvkdef
  have hCvk : 0 < Cvk := hCvk0
  have hcvk0' : 0 < cvk := lt_min hcvk0 zero_lt_one
  have hcvk1 : cvk ≤ 1 := min_le_right _ _
  have hVK' : VKExpInput Cvk cvk :=
    VKExpInput_mono_c ⟨hCvk, hcvk0, hbody⟩ hcvk0 hcvk0' (min_le_left _ _)
  have hRaw : Work.BMF.N7.VKExpSumRaw := ⟨Cvk, cvk, hVK'.1, hVK'.2.1, hVK'.2.2⟩
  obtain ⟨Az, cz, hAz, hcz, hZ⟩ := Work.BMF.N7.zeta_strip_bound_of_vk_aux hRaw
    (fun c₀ cζ h₀ hζ => Work.BMF.N7.dyadic_vk_sum_bound c₀ cζ h₀ hζ)
  obtain ⟨Ab, hAb0, hAbb⟩ := Work.BMF.VKChain.block_sum_uniform cvk hcvk0' hcvk1
  set ch : ℝ := min (min cz (1 / 4)) (cvk ^ (6 / 7 : ℝ) / 2) with hchdef
  have hch0 : 0 < ch := lt_min (lt_min hcz (by norm_num)) (by positivity)
  have hch1 : ch ≤ 1 / 4 := le_trans (min_le_left _ _) (min_le_right _ _)
  have hch2 : ch ≤ cvk ^ (6 / 7 : ℝ) / 2 := min_le_right _ _
  have hchcz : ch ≤ cz := le_trans (min_le_left _ _) (min_le_left _ _)
  have hSC0 : 0 ≤ seriesConst Cvk cvk Ab := by
    rw [seriesConst_apply]
    have h2 : 0 ≤ 2 * Cvk * Real.exp (1 / 2) * Ab := by positivity
    have h4 : 0 ≤ 10 * Real.exp 4 * (3 + cvk ^ (-(6 / 7 : ℝ))) := by positivity
    linarith
  refine ⟨Az + seriesConst Cvk cvk Ab, ch, by linarith, hch0, hch1, ?_⟩
  intro a σ t ha0 ha1 ht3 hσlo hσhi
  set s : ℂ := (σ : ℂ) + (t : ℂ) * Complex.I with hsdef
  set L : ℝ := Real.log (|t| + 3) with hLdef
  have hL1 : 1 ≤ L := by
    rw [hLdef]
    have h1 : (1:ℝ) < Real.log 3 := by
      rw [Real.lt_log_iff_exp_lt (by norm_num)]
      exact Real.exp_one_lt_three
    have h2 : Real.log 3 ≤ Real.log (|t| + 3) :=
      Real.log_le_log (by norm_num) (by linarith [abs_nonneg t])
    linarith
  have hLpos : 0 < L := lt_of_lt_of_le zero_lt_one hL1
  have hLpow : L ^ (-(6 / 7 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hL1 (by norm_num)
  have hσ0 : 0 < σ := by
    have h2 : ch * L ^ (-(6 / 7 : ℝ)) ≤ (1 / 4) * 1 :=
      mul_le_mul hch1 hLpow (Real.rpow_nonneg hLpos.le _) (by norm_num)
    linarith [hσlo, h2]
  have hsre : s.re = σ := by simp [hsdef]
  have hs0 : 0 < s.re := by rw [hsre]; exact hσ0
  have hL67 : (1 : ℝ) ≤ L ^ (6 / 7 : ℝ) := Real.one_le_rpow hL1 (by norm_num)
  have hZ' : ‖riemannZeta s‖ ≤ Az * L ^ (6 / 7 : ℝ) := by
    have h2 : 1 - cz * L ^ (-(6 / 7 : ℝ)) ≤ σ := by
      have h3 : ch * L ^ (-(6 / 7 : ℝ)) ≤ cz * L ^ (-(6 / 7 : ℝ)) :=
        mul_le_mul_of_nonneg_right hchcz (Real.rpow_nonneg hLpos.le _)
      linarith [hσlo, h3]
    have h := hZ σ t ht3 h2 hσhi
    simpa [hsdef, hLdef] using h
  rcases eq_or_lt_of_le ha0 with ha | ha
  · -- `a = 0`
    subst ha
    have hza : (0 : ℝ) ^ (-σ) = 0 := Real.zero_rpow (by linarith : -σ ≠ 0)
    have hzero : ‖HurwitzZeta.hurwitzZeta ((0 : ℝ) : UnitAddCircle) s‖ = ‖riemannZeta s‖ := by
      rw [show ((0 : ℝ) : UnitAddCircle) = 0 from rfl, HurwitzZeta.hurwitzZeta_zero]
    rw [hzero, hza, zero_add]
    nlinarith [hZ', hL67, hSC0, hAz]
  · -- `0 < a ≤ 1`
    have hs1 : s ≠ 1 := by
      intro hcon
      have h2 : t = 0 := by
        have := congrArg Complex.im hcon
        simpa [hsdef] using this
      rw [h2] at ht3
      have h3 : (3:ℝ) ≤ 0 := by simpa using ht3
      norm_num at h3
    have hseries := shift_series_sum_bound (Cvk := Cvk) (cvk := cvk) (Ab := Ab) (ch := ch)
      hVK' hcvk0' hcvk1 hAb0 hAbb hch1 hch2 ha ha1 ht3 hσlo hσhi
    have hdiff := Work.BMF.hurwitzZeta_sub_riemannZeta_eq_tsum ha ha1 hs0 hs1
    have hmain : ‖HurwitzZeta.hurwitzZeta (a : UnitAddCircle) s‖ ≤
        seriesConst Cvk cvk Ab * (a ^ (-σ) + L ^ (6 / 7 : ℝ)) + Az * L ^ (6 / 7 : ℝ) := by
      calc ‖HurwitzZeta.hurwitzZeta (a : UnitAddCircle) s‖
          = ‖(HurwitzZeta.hurwitzZeta (a : UnitAddCircle) s - riemannZeta s) + riemannZeta s‖ := by
            ring_nf
        _ ≤ ‖HurwitzZeta.hurwitzZeta (a : UnitAddCircle) s - riemannZeta s‖ + ‖riemannZeta s‖ :=
            norm_add_le _ _
        _ = ‖∑' m : ℕ, Work.BMF.shiftTerm a m s‖ + ‖riemannZeta s‖ := by rw [hdiff]
        _ ≤ seriesConst Cvk cvk Ab * (a ^ (-σ) + L ^ (6 / 7 : ℝ)) + Az * L ^ (6 / 7 : ℝ) :=
            add_le_add hseries hZ'
    have hann : 0 ≤ a ^ (-σ) := Real.rpow_nonneg ha0 _
    have hfin : seriesConst Cvk cvk Ab * (a ^ (-σ) + L ^ (6 / 7 : ℝ)) + Az * L ^ (6 / 7 : ℝ) ≤
        (Az + seriesConst Cvk cvk Ab) * (a ^ (-σ) + L ^ (6 / 7 : ℝ)) := by
      nlinarith [hSC0, hAz, hann, hL67]
    linarith [hmain, hfin]

/-! ## Assembly -/

/-- **V2 (node `Work.BMF.L_growth_VK`) from the Vinogradov–Korobov exponential-sum input (V1).**

From the restricted-range VK exponential-sum estimate `Work.BMF.VKExpInput` (which is exactly the
body of the proved, `sorry`-free `Work.BMF.vk_exp_sum`), produce constants `A, c > 0` with
`Work.BMF.VKGrowth A c`, i.e. for every modulus `N ≥ 1` and every character `χ` mod `N`,
`‖L(σ+it,χ)‖ ≤ A · N · (log(|t|+3))^{6/7}` whenever `3 ≤ |t|`,
`1 - c (log(|t|+3))^{-6/7} ≤ σ` and `σ ≤ 2`. -/
theorem vkgrowth_of_vkExpInput (hVK : ∃ C c : ℝ, VKExpInput C c) :
    ∃ A c : ℝ, VKGrowth A c := by
  obtain ⟨Ah, ch, hAh, hch, _hch4, hHur⟩ := hurwitz_growth_local hVK
  refine ⟨2 * Ah, ch, by linarith, hch, ?_⟩
  exact LFunction_growth_of_hurwitz hAh hch (by linarith) hHur

end

end Work.BMF.zpt
