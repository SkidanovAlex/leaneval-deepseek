import Mathlib
import Submission.Work.BMF.zpt.vk_pre
import Submission.Work.BMF.zpt.vkbn_defs
import Submission.Work.BMF.liouville.vkbl_defs
import Submission.Work.BMF.liouville.vkbl_shift
import Submission.Work.BMF.liouville.vkbl_taylor
import Submission.Work.BMF.liouville.vkbl_weyl
import Submission.Work.BMF.liouville.vkbl_num

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option maxHeartbeats 4000000

namespace Work.BMF.liouville

open Finset

noncomputable section

theorem vk_bounded_lambda : ∃ C D : ℝ, 0 < C ∧ 0 < D ∧
    ∀ (N : ℕ) (t u R : ℝ), 2 ≤ N → (N : ℝ) ≤ t → Real.log t ≤ 88 * Real.log (N : ℝ) →
      0 < u → u ≤ 1 → (N : ℝ) < R → R ≤ 2 * (N : ℝ) →
      ‖Work.BMF.zpt.ESb (N : ℝ) R u t‖ ≤
        C * (N : ℝ) ^ (1 - (1 / D) * (Real.log (N : ℝ) / Real.log t) ^ 2) := by
  obtain ⟨Cw, hCw, hWeyl⟩ := TrelP_weyl 89 (by norm_num) epsw (by norm_num [epsw])
  have hepspos : 0 < epsw := by rw [epsw]; positivity
  set Ct : ℝ := 2 ^ 89 * (2 * Real.pi * 89) * 3 ^ 89 * 4 + 4 with hCt
  have hCtpos : 0 < Ct := by rw [hCt]; positivity
  set hh : ℝ := (2 : ℝ) ^ (1 - ((89 : ℕ) : ℝ)) with hhh
  have hhpos : 0 < hh := by rw [hhh]; positivity
  set D : ℝ := (2 : ℝ) ^ 96 with hDdef
  have hDpos : 0 < D := by rw [hDdef]; positivity
  have hD1 : (1 : ℝ) ≤ D := by rw [hDdef]; norm_num
  have hDinv_pos : 0 < 1 / D := by positivity
  have hDinv180 : 1 / D ≤ 1 / 180 := by
    rw [hDdef, div_le_div_iff₀ (by positivity) (by norm_num)]; norm_num
  have hDinv178 : 1 / D ≤ 1 / 178 := by
    rw [hDdef, div_le_div_iff₀ (by positivity) (by norm_num)]; norm_num
  set C : ℝ := max (2 * Cw * Ct ^ hh + 6) (2 * (2 : ℝ) ^ 90) with hCdef
  have hCpos : 0 < C := lt_of_lt_of_le (by positivity) (le_max_left _ _)
  have hCmain : 2 * Cw * Ct ^ hh + 6 ≤ C := by rw [hCdef]; exact le_max_left _ _
  have hCbig : (2 : ℝ) * (2 : ℝ) ^ 90 ≤ C := by rw [hCdef]; exact le_max_right _ _
  refine ⟨C, D, hCpos, hDpos, ?_⟩
  intro N t u R hN hNt hlogt hu0 hu1 hR hR2
  have hNpos : (0 : ℝ) < (N : ℝ) := by positivity
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast (by omega : 1 ≤ N)
  have hN2 : 2 ≤ N := by omega
  have hN2R : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN2
  have htpos : 0 < t := lt_of_lt_of_le hNpos hNt
  have hlogN : 0 < Real.log (N : ℝ) := log_N_pos N hN2
  have hlogtpos : 0 < Real.log t := Real.log_pos (by linarith)
  have hq0 : 0 ≤ (Real.log (N : ℝ) / Real.log t) ^ 2 := sq_nonneg _
  have hq1 : (Real.log (N : ℝ) / Real.log t) ^ 2 ≤ 1 := by
    rw [sq_le_one_iff_abs_le_one, abs_of_nonneg (div_nonneg hlogN.le hlogtpos.le), div_le_one hlogtpos]
    exact Real.log_le_log hNpos hNt
  have hqD : (1 / D) * (Real.log (N : ℝ) / Real.log t) ^ 2 ≤ 1 / D := by
    nlinarith [hq0, hq1, hDinv_pos]
  by_cases hsmall : N < 2 ^ 90
  · have hcard : ‖Work.BMF.zpt.ESb (N : ℝ) R u t‖ ≤ 2 * (N : ℝ) := by
      refine le_trans (norm_ESb_le_card (N : ℝ) R u t hu0) ?_
      rw [Nat.card_Ioc]
      have h2 : (⌊R⌋₊ : ℝ) ≤ R := Nat.floor_le (by linarith)
      have h5 : ⌊R⌋₊ ≤ 2 * N := by
        have h6 : (⌊R⌋₊ : ℝ) ≤ 2 * (N : ℝ) := le_trans h2 hR2
        exact_mod_cast h6
      have h7 : ⌊R⌋₊ - ⌊(N:ℝ)⌋₊ ≤ 2 * N := le_trans (Nat.sub_le _ _) h5
      exact_mod_cast h7
    have hNlt : (N : ℝ) < (2 : ℝ) ^ 90 := by exact_mod_cast hsmall
    have hexp : 0 ≤ 1 - (1 / D) * (Real.log (N : ℝ) / Real.log t) ^ 2 := by
      have : 1 / D ≤ 1 := by rw [div_le_one hDpos]; exact hD1
      linarith
    calc ‖Work.BMF.zpt.ESb (N : ℝ) R u t‖ ≤ 2 * (N : ℝ) := hcard
      _ ≤ 2 * (2 : ℝ) ^ 90 := by linarith
      _ ≤ C * (N : ℝ) ^ (1 - (1 / D) * (Real.log (N : ℝ) / Real.log t) ^ 2) := by
          have hge1 : (1 : ℝ) ≤ (N : ℝ) ^ (1 - (1 / D) * (Real.log (N : ℝ) / Real.log t) ^ 2) :=
            Real.one_le_rpow hN1 hexp
          nlinarith [hCbig, hge1, hCpos]
  · rw [not_lt] at hsmall
    have hNbig : (2 : ℝ) ^ 90 ≤ (N : ℝ) := by exact_mod_cast hsmall
    have hp2 : (2 : ℝ) ≤ (N : ℝ) ^ ((1 : ℝ) / 90) := by
      have h9 : (2 : ℝ) ≤ ((2 : ℝ) ^ 90) ^ ((1 : ℝ) / 90) := by
        rw [show ((2 : ℝ) ^ 90) = (2 : ℝ) ^ ((90 : ℕ) : ℝ) by rw [Real.rpow_natCast],
          ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2),
          show (((90 : ℕ) : ℝ)) * (1 / 90) = 1 by push_cast; ring, Real.rpow_one]
      exact le_trans h9 (Real.rpow_le_rpow (by positivity) hNbig (by norm_num))
    set Mv : ℝ := (N : ℝ) ^ (vmu (N : ℝ) t) with hMvdef
    set M : ℕ := ⌊Mv⌋₊ with hMdef
    have hmu0 : 0 ≤ vmu (N : ℝ) t := vmu_nonneg N t hN2 hlogt
    have hmu1 : vmu (N : ℝ) t ≤ 1 := by
      rw [vmu, vd2]; have h2 := vlam_ge_one N t hN2 hNt; linarith
    have hvmu90 : (1 : ℝ) / 90 ≤ vmu (N : ℝ) t := by
      rw [vmu, vd2]
      have h5 := vlam_le_88 N t hN2 hlogt
      have h6 := vlam_ge_one N t hN2 hNt
      linarith
    have hMv1 : 1 ≤ Mv := by rw [hMvdef]; exact Real.one_le_rpow hN1 hmu0
    have hMvN : Mv ≤ (N : ℝ) := by
      rw [hMvdef]
      simpa using Real.rpow_le_rpow_of_exponent_le hN1 hmu1
    have hMv2 : 2 ≤ Mv := by
      rw [hMvdef]
      exact le_trans hp2 (Real.rpow_le_rpow_of_exponent_le hN1 hvmu90)
    have hM1 : 1 ≤ M := by rw [hMdef]; exact Nat.le_floor (by simpa using hMv1)
    have hMlo : Mv / 2 ≤ (M : ℝ) := by
      rw [hMdef]
      have h4 : Mv - 1 ≤ ((⌊Mv⌋₊ : ℕ) : ℝ) := by
        have := Nat.lt_floor_add_one Mv; linarith
      linarith
    have hMhi : (M : ℝ) ≤ Mv := by rw [hMdef]; exact Nat.floor_le (by linarith)
    have hMpos : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hM1
    have hMv_lt : Mv ≤ (N : ℝ) / 2 := by
      have hA : (N : ℝ) ^ (vmu (N : ℝ) t - 1) ≤ 1 / 2 := by
        have h4 : vmu (N : ℝ) t - 1 ≤ (-1 : ℝ) / 90 := by
          rw [vmu, vd2]; have h5 := vlam_ge_one N t hN2 hNt; linarith
        refine le_trans (Real.rpow_le_rpow_of_exponent_le hN1 h4) ?_
        rw [show (-1 : ℝ) / 90 = -((1 : ℝ) / 90) by ring, Real.rpow_neg hNpos.le,
          show (1 : ℝ) / 2 = (2 : ℝ)⁻¹ by norm_num]
        exact (inv_le_inv₀ (by positivity) (by norm_num)).mpr hp2
      calc Mv = (N : ℝ) ^ (vmu (N : ℝ) t - 1) * (N : ℝ) := by
            rw [hMvdef, Real.rpow_sub hNpos, Real.rpow_one, div_mul_cancel₀ _ (ne_of_gt hNpos)]
        _ ≤ (1 / 2) * (N : ℝ) := mul_le_mul_of_nonneg_right hA hNpos.le
        _ = (N : ℝ) / 2 := by ring
    set S : ℝ := ∑ n ∈ Finset.Ioc ⌊(N : ℝ)⌋₊ ⌊R⌋₊, ‖Trel M n u t‖ with hSdef
    have hshift := ESb_shift M hM1 (N : ℝ) R u t hu0
    rw [← hSdef] at hshift
    have hθ180 : (1 : ℝ) / 180 ≤ vtv (N : ℝ) t := by
      refine le_min ?_ ?_
      · have := vlam_ge_one N t hN2 hNt; linarith
      · rw [vmu, vd2]
        have h5 := vlam_le_88 N t hN2 hlogt
        have h6 := vlam_ge_one N t hN2 hNt
        linarith
    have hhh2 : hh = ((2 : ℝ) ^ 88)⁻¹ := by
      rw [hhh, show (1 : ℝ) - ((89 : ℕ) : ℝ) = -((88 : ℕ) : ℝ) by norm_num,
        Real.rpow_neg (by norm_num), Real.rpow_natCast]
    have hDθ : 1 / D ≤ vtv (N : ℝ) t * hh - epsw := by
      rw [hDdef, hhh2, epsw]
      have h1 : 1 / (2 : ℝ) ^ 96 ≤ (1 / 180 : ℝ) * ((2 : ℝ) ^ 88)⁻¹ - (1 / 2 : ℝ) ^ 200 := by
        have h4 : 1 / (2 : ℝ) ^ 96 = (1 / 256 : ℝ) * ((2 : ℝ) ^ 88)⁻¹ := by
          rw [show ((2 : ℝ) ^ 96) = (2 : ℝ) ^ 88 * 256 by norm_num, one_div, mul_inv, mul_comm]
          ring
        rw [h4]
        have h5 : (1 / 256 : ℝ) ≤ 1 / 180 - (1 / 2 : ℝ) ^ 200 * 2 ^ 88 := by norm_num
        have h6 := mul_le_mul_of_nonneg_right h5 (by positivity : (0 : ℝ) ≤ ((2 : ℝ) ^ 88)⁻¹)
        have h7 : (1 / 180 - (1 / 2 : ℝ) ^ 200 * 2 ^ 88) * ((2 : ℝ) ^ 88)⁻¹
            = 1 / 180 * ((2 : ℝ) ^ 88)⁻¹ - (1 / 2 : ℝ) ^ 200 := by
          rw [sub_mul, mul_assoc, mul_inv_cancel₀ (by positivity : (((2 : ℝ) ^ 88 : ℝ)) ≠ 0), mul_one]
        linarith [h6, h7 ▸ h6]
      have h2 : (1 / 180 : ℝ) * ((2 : ℝ) ^ 88)⁻¹ ≤ vtv (N : ℝ) t * ((2 : ℝ) ^ 88)⁻¹ :=
        mul_le_mul_of_nonneg_right hθ180 (by positivity)
      linarith
    have hθexp : (1 / D) * (Real.log (N : ℝ) / Real.log t) ^ 2 ≤ vtv (N : ℝ) t * hh - epsw :=
      le_trans hqD hDθ
    have hδexp : (1 / D) * (Real.log (N : ℝ) / Real.log t) ^ 2 ≤ vd2 (N : ℝ) t := by
      refine le_trans hqD (le_trans hDinv178 ?_)
      have h2 := vlam_ge_one N t hN2 hNt
      rw [vd2]; linarith
    have hμexp : (1 / D) * (Real.log (N : ℝ) / Real.log t) ^ 2 ≤ 1 - vmu (N : ℝ) t := by
      refine le_trans hqD (le_trans hDinv180 ?_)
      have h2 := vlam_ge_one N t hN2 hNt
      rw [vmu, vd2]; linarith
    set Xt : ℝ := Ct * (N : ℝ) ^ (-(vtv (N : ℝ) t)) with hXtdef
    have hXtpos : 0 < Xt := by rw [hXtdef]; positivity
    set K : ℝ := Cw * (M : ℝ) ^ (1 + epsw) * Xt ^ hh + (M : ℝ) * (2 * (N : ℝ) ^ (-(vd2 (N : ℝ) t))) with hKdef
    have hpoint : ∀ n ∈ Finset.Ioc ⌊(N : ℝ)⌋₊ ⌊R⌋₊, ‖Trel M n u t‖ ≤ K := by
      intro n hn
      obtain ⟨hnlo, hnhi⟩ := Finset.mem_Ioc.mp hn
      have hn1 : 1 ≤ n := by omega
      have hnN : (N : ℝ) ≤ (n : ℝ) := by
        have h4 : ⌊(N : ℝ)⌋₊ + 1 ≤ n := hnlo
        have h5 : (N : ℝ) < (⌊(N : ℝ)⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one _
        have h6 : (((⌊(N : ℝ)⌋₊ + 1 : ℕ)) : ℝ) ≤ (n : ℝ) := by exact_mod_cast h4
        push_cast at h6
        linarith
      have hn2N : (n : ℝ) ≤ 2 * (N : ℝ) + 1 := by
        have h2 : (n : ℝ) ≤ (⌊R⌋₊ : ℝ) := by exact_mod_cast hnhi
        have h3 : (⌊R⌋₊ : ℝ) ≤ R := Nat.floor_le (by linarith)
        linarith
      have hden : 0 < (n : ℝ) + u := by positivity
      have hMn : (M : ℝ) ≤ ((n : ℝ) + u) / 2 := by
        have h1 : Mv ≤ (n : ℝ) + u := by linarith [hMv_lt, hnN]
        linarith [hMhi]
      obtain ⟨hgam1, hgamub, hgamlb⟩ := gam_abs_bounds N t u n hN2 hNt hlogt hu0 hu1 hnN hn2N
      have hgam0 : 0 < |Work.BMF.zpt.gam 89 t (n : ℝ) u| := lt_of_lt_of_le (by positivity) hgamlb
      have hweyl := hWeyl M n u t hM1 htpos hu0 hn1 hgam0 hgam1
      have hbr := bracket_le N t u n M hN2 hNt hlogt hu0 hu1 hnN hn2N hMlo hMhi hM1
      have hter := taylor_err_le N t u n M hsmall hNt hlogt hu0 hnN hMhi
      have hbr'' : (1 / ((⌊1 / |Work.BMF.zpt.gam 89 t (n : ℝ) u|⌋₊ : ℝ)) + 1 / (M : ℝ)
            + 1 / (M : ℝ) ^ 88 + ((⌊1 / |Work.BMF.zpt.gam 89 t (n : ℝ) u|⌋₊ : ℝ)) / (M : ℝ) ^ 89)
          ≤ Xt := by
        rw [hXtdef, hCt]; exact hbr
      have hbr' : (1 / ((⌊1 / |Work.BMF.zpt.gam 89 t (n : ℝ) u|⌋₊ : ℝ)) + 1 / (M : ℝ)
            + 1 / (M : ℝ) ^ 88 + ((⌊1 / |Work.BMF.zpt.gam 89 t (n : ℝ) u|⌋₊ : ℝ)) / (M : ℝ) ^ 89) ^ hh
          ≤ Xt ^ hh := Real.rpow_le_rpow (by positivity) hbr'' hhpos.le
      have hbrP : (1 / ((⌊1 / |Work.BMF.zpt.gam 89 t (n : ℝ) u|⌋₊ : ℝ)) + 1 / (M : ℝ)
            + 1 / (M : ℝ) ^ 88 + ((⌊1 / |Work.BMF.zpt.gam 89 t (n : ℝ) u|⌋₊ : ℝ)) / (M : ℝ) ^ 89) ^ ((2 : ℝ) ^ (1 - ((89:ℕ):ℝ)))
          ≤ Xt ^ hh := by
        conv_lhs => rw [← hhh]
        exact hbr'
      have h1 : ‖TrelP 89 M n u t‖ ≤ Cw * (M : ℝ) ^ (1 + epsw) * Xt ^ hh :=
        le_trans hweyl (mul_le_mul_of_nonneg_left hbrP (by positivity))
      have h2 : ‖Trel M n u t - TrelP 89 M n u t‖ ≤ (M : ℝ) * (2 * (N : ℝ) ^ (-(vd2 (N : ℝ) t))) :=
        le_trans (Trel_sub_TrelP 89 M n u t hn1 hu0 htpos.le hMn) (mul_le_mul_of_nonneg_left hter hMpos.le)
      rw [hKdef]
      calc ‖Trel M n u t‖ = ‖TrelP 89 M n u t + (Trel M n u t - TrelP 89 M n u t)‖ := by ring_nf
        _ ≤ ‖TrelP 89 M n u t‖ + ‖Trel M n u t - TrelP 89 M n u t‖ := norm_add_le _ _
        _ ≤ Cw * (M : ℝ) ^ (1 + epsw) * Xt ^ hh + (M : ℝ) * (2 * (N : ℝ) ^ (-(vd2 (N : ℝ) t))) := by
            linarith [h1, h2]
    have hcardN : ((Finset.Ioc ⌊(N : ℝ)⌋₊ ⌊R⌋₊).card : ℝ) ≤ 2 * (N : ℝ) := by
      rw [Nat.card_Ioc]
      have h2 : (⌊R⌋₊ : ℝ) ≤ R := Nat.floor_le (by linarith)
      have h5 : ⌊R⌋₊ ≤ 2 * N := by
        have h6 : (⌊R⌋₊ : ℝ) ≤ 2 * (N : ℝ) := le_trans h2 hR2
        exact_mod_cast h6
      have h7 : ⌊R⌋₊ - ⌊(N:ℝ)⌋₊ ≤ 2 * N := le_trans (Nat.sub_le _ _) h5
      exact_mod_cast h7
    have hSbound : S ≤ (2 * (N : ℝ)) * K := by
      rw [hSdef, hKdef]
      calc ∑ n ∈ Finset.Ioc ⌊(N : ℝ)⌋₊ ⌊R⌋₊, ‖Trel M n u t‖
          ≤ ∑ _n ∈ Finset.Ioc ⌊(N : ℝ)⌋₊ ⌊R⌋₊, K := Finset.sum_le_sum hpoint
        _ = ((Finset.Ioc ⌊(N : ℝ)⌋₊ ⌊R⌋₊).card : ℝ) * K := by rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ (2 * (N : ℝ)) * K := mul_le_mul_of_nonneg_right hcardN (by positivity)
    have hfinalA : (1 / (M : ℝ)) * ((2 * (N : ℝ)) * (Cw * (M : ℝ) ^ (1 + epsw) * Xt ^ hh))
        ≤ 2 * Cw * Ct ^ hh * (N : ℝ) ^ (1 + epsw - vtv (N : ℝ) t * hh) := by
      have hXt : Xt ^ hh = Ct ^ hh * (N : ℝ) ^ (-(vtv (N : ℝ) t) * hh) := by
        rw [hXtdef, Real.mul_rpow hCtpos.le (Real.rpow_nonneg hNpos.le _), Real.rpow_mul hNpos.le]
      rw [hXt]
      have hkey : (1 / (M : ℝ)) * ((2 * (N : ℝ)) * (Cw * (M : ℝ) ^ (1 + epsw)
            * (Ct ^ hh * (N : ℝ) ^ (-(vtv (N : ℝ) t) * hh))))
          = 2 * Cw * (N : ℝ) * ((M : ℝ) ^ epsw) * (Ct ^ hh * (N : ℝ) ^ (-(vtv (N : ℝ) t) * hh)) := by
        rw [Real.rpow_add hMpos, Real.rpow_one]
        field_simp
      rw [hkey]
      have hMeps : (M : ℝ) ^ epsw ≤ (N : ℝ) ^ epsw :=
        Real.rpow_le_rpow hMpos.le (le_trans hMhi hMvN) hepspos.le
      have hstep : 2 * Cw * (N : ℝ) * ((M : ℝ) ^ epsw) * (Ct ^ hh * (N : ℝ) ^ (-(vtv (N : ℝ) t) * hh))
          ≤ 2 * Cw * (N : ℝ) * ((N : ℝ) ^ epsw) * (Ct ^ hh * (N : ℝ) ^ (-(vtv (N : ℝ) t) * hh)) := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        apply mul_le_mul_of_nonneg_left hMeps (by positivity)
      refine le_trans hstep ?_
      rw [show 2 * Cw * (N : ℝ) * (N : ℝ) ^ epsw * (Ct ^ hh * (N : ℝ) ^ (-(vtv (N : ℝ) t) * hh))
            = 2 * Cw * ((N : ℝ) * (N : ℝ) ^ epsw)
              * (Ct ^ hh * (N : ℝ) ^ (-(vtv (N : ℝ) t) * hh)) by ring,
          mul_rpow_one (N : ℝ) hNpos epsw,
          show 2 * Cw * (N : ℝ) ^ (1 + epsw) * (Ct ^ hh * (N : ℝ) ^ (-(vtv (N : ℝ) t) * hh))
            = 2 * Cw * Ct ^ hh * ((N : ℝ) ^ (1 + epsw) * (N : ℝ) ^ (-(vtv (N : ℝ) t) * hh)) by ring,
          ← Real.rpow_add hNpos,
          show (1 + epsw) + (-(vtv (N : ℝ) t) * hh) = 1 + epsw - vtv (N : ℝ) t * hh by ring]
    have hfinalB : (1 / (M : ℝ)) * ((2 * (N : ℝ)) * ((M : ℝ) * (2 * (N : ℝ) ^ (-(vd2 (N : ℝ) t)))))
        = 4 * (N : ℝ) ^ (1 - vd2 (N : ℝ) t) := by
      rw [show (1 / (M : ℝ)) * ((2 * (N : ℝ)) * ((M : ℝ) * (2 * (N : ℝ) ^ (-(vd2 (N : ℝ) t)))))
            = 4 * ((N : ℝ) * (N : ℝ) ^ (-(vd2 (N : ℝ) t))) by field_simp; ring,
          mul_rpow_one (N : ℝ) hNpos (-(vd2 (N : ℝ) t)),
          show 1 + (-(vd2 (N : ℝ) t)) = 1 - vd2 (N : ℝ) t by ring]
    have hfinal : (1 / (M : ℝ)) * S ≤ 2 * Cw * Ct ^ hh * (N : ℝ) ^ (1 + epsw - vtv (N : ℝ) t * hh)
        + 4 * (N : ℝ) ^ (1 - vd2 (N : ℝ) t) := by
      have h1 : (1 / (M : ℝ)) * S ≤ (1 / (M : ℝ)) * ((2 * (N : ℝ)) * K) :=
        mul_le_mul_of_nonneg_left hSbound (by positivity)
      rw [hKdef] at h1
      have hsplit : (1 / (M : ℝ)) * ((2 * (N : ℝ)) * (Cw * (M : ℝ) ^ (1 + epsw) * Xt ^ hh
            + (M : ℝ) * (2 * (N : ℝ) ^ (-(vd2 (N : ℝ) t)))))
          = (1 / (M : ℝ)) * ((2 * (N : ℝ)) * (Cw * (M : ℝ) ^ (1 + epsw) * Xt ^ hh))
            + (1 / (M : ℝ)) * ((2 * (N : ℝ)) * ((M : ℝ) * (2 * (N : ℝ) ^ (-(vd2 (N : ℝ) t))))) := by
        ring
      rw [hsplit] at h1
      linarith [h1, hfinalA, hfinalB]
    have hT1 : (N : ℝ) ^ (1 + epsw - vtv (N : ℝ) t * hh)
        ≤ (N : ℝ) ^ (1 - (1 / D) * (Real.log (N : ℝ) / Real.log t) ^ 2) :=
      Real.rpow_le_rpow_of_exponent_le hN1 (by linarith [hθexp])
    have hT2 : (N : ℝ) ^ (1 - vd2 (N : ℝ) t)
        ≤ (N : ℝ) ^ (1 - (1 / D) * (Real.log (N : ℝ) / Real.log t) ^ 2) :=
      Real.rpow_le_rpow_of_exponent_le hN1 (by linarith [hδexp])
    have hT3 : Mv ≤ (N : ℝ) ^ (1 - (1 / D) * (Real.log (N : ℝ) / Real.log t) ^ 2) := by
      rw [hMvdef]
      exact Real.rpow_le_rpow_of_exponent_le hN1 (by linarith [hμexp])
    have hfin : 2 * Cw * Ct ^ hh * (N : ℝ) ^ (1 + epsw - vtv (N : ℝ) t * hh)
        + 4 * (N : ℝ) ^ (1 - vd2 (N : ℝ) t) + 2 * (M : ℝ)
        ≤ C * (N : ℝ) ^ (1 - (1 / D) * (Real.log (N : ℝ) / Real.log t) ^ 2) := by
      have hA : 2 * Cw * Ct ^ hh * (N : ℝ) ^ (1 + epsw - vtv (N : ℝ) t * hh)
          ≤ 2 * Cw * Ct ^ hh * (N : ℝ) ^ (1 - (1 / D) * (Real.log (N : ℝ) / Real.log t) ^ 2) :=
        mul_le_mul_of_nonneg_left hT1 (by positivity)
      have hB : 4 * (N : ℝ) ^ (1 - vd2 (N : ℝ) t)
          ≤ 4 * (N : ℝ) ^ (1 - (1 / D) * (Real.log (N : ℝ) / Real.log t) ^ 2) :=
        mul_le_mul_of_nonneg_left hT2 (by norm_num)
      have hD3 : 2 * (M : ℝ) ≤ 2 * (N : ℝ) ^ (1 - (1 / D) * (Real.log (N : ℝ) / Real.log t) ^ 2) := by
        calc 2 * (M : ℝ) ≤ 2 * Mv := by linarith [hMhi]
          _ ≤ 2 * (N : ℝ) ^ (1 - (1 / D) * (Real.log (N : ℝ) / Real.log t) ^ 2) :=
              mul_le_mul_of_nonneg_left hT3 (by norm_num)
      have hp : (0 : ℝ) ≤ (N : ℝ) ^ (1 - (1 / D) * (Real.log (N : ℝ) / Real.log t) ^ 2) :=
        Real.rpow_nonneg hNpos.le _
      have hCP : (2 * Cw * Ct ^ hh + 6) * (N : ℝ) ^ (1 - (1 / D) * (Real.log (N : ℝ) / Real.log t) ^ 2)
          ≤ C * (N : ℝ) ^ (1 - (1 / D) * (Real.log (N : ℝ) / Real.log t) ^ 2) :=
        mul_le_mul_of_nonneg_right hCmain hp
      nlinarith [hA, hB, hD3, hCP]
    calc ‖Work.BMF.zpt.ESb (N : ℝ) R u t‖ ≤ (1 / (M : ℝ)) * S + 2 * (M : ℝ) := hshift
      _ ≤ (2 * Cw * Ct ^ hh * (N : ℝ) ^ (1 + epsw - vtv (N : ℝ) t * hh)
            + 4 * (N : ℝ) ^ (1 - vd2 (N : ℝ) t)) + 2 * (M : ℝ) := by linarith [hfinal]
      _ ≤ C * (N : ℝ) ^ (1 - (1 / D) * (Real.log (N : ℝ) / Real.log t) ^ 2) := hfin


end

end Work.BMF.liouville
