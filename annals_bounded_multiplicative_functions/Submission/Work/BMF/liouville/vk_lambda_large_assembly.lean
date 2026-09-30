import Mathlib
import Submission.Work.BMF.liouville.vk_large_defs
import Submission.Work.BMF.liouville.vk_large_pprod
import Submission.Work.BMF.liouville.vk_large_lam_bounds
import Submission.Work.BMF.liouville.vk_large_M_bounds
import Submission.Work.BMF.liouville.vk_large_delta_bound
import Submission.Work.BMF.liouville.vk_large_const_bound
import Submission.Work.BMF.liouville.vk_large_easy_terms2
import Submission.Work.BMF.vkford_lemma51
import Submission.Work.BMF.vkford_H_lower2
import Submission.Work.BMF.liouville.vmvt_stechkin_defs
import Submission.Work.BMF.vmvt_setup

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Ford §5 Vinogradov extraction for `λ ≥ 13/5` (the large-`λ` half of Ford's Theorem 2)

With `λ = log t / log N`, `M = ⌈N^{2/5}⌉` and the Ford parameters
`h = ⌈λ⌉`, `g = ⌈5λ⌉`, `k = g+1`, `r' = ⌈300λ²/k⌉`, `r = k r'`, `s' = ⌈200λ²/g⌉`, `s = g s'`, the
extraction `Work.BMF.vkford_lemma51` is combined with the two Stechkin inputs
(`Work.BMF.liouville.main_sharp`), Ford's crude incomplete-system bound
(`Work.BMF.vkford_incomplete_crude`) and the `W`-product bound (`Work.BMF.vkford_Wproduct_self`)
to give `‖Ssum N u t R‖ ≤ C N^{1-1/(Dλ²)}`.

The exponent bookkeeping is in `Work.BMF.liouville.vk_large_pprod` (`Pprod_le_C0`,
`Pprod_rpow_bound`); the parameter arithmetic is in `Work.BMF.liouville.vk_large_lam_bounds`,
`vk_large_M_bounds`, `vk_large_delta_bound`, `vk_large_const_bound` and `vk_large_easy_terms2`.
-/

namespace Work.BMF.liouville

open Finset
open scoped BigOperators

noncomputable section

set_option maxHeartbeats 2000000

/-- The trivial bound `‖Ssum N u t R‖ ≤ N + 1`. -/
lemma Ssum_norm_le (N t u R : ℝ) (hN : 0 ≤ N) (hu : 0 < u) (hR2 : R ≤ 2 * N) :
    ‖Work.BMF.Ssum N u t R‖ ≤ N + 1 := by
  rw [Work.BMF.Ssum]
  have hterm : ∀ n ∈ Finset.Ioc ⌊N⌋₊ ⌊R⌋₊,
      ‖((((n : ℝ) + u : ℝ)) : ℂ) ^ (-(Complex.I * (t : ℂ)))‖ ≤ (1 : ℝ) := by
    intro n hn
    have hn1 : 1 ≤ n := by
      have := (Finset.mem_Ioc.mp hn).1
      omega
    have hpos : (0 : ℝ) < (n : ℝ) + u := by
      have : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn1
      linarith
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hpos]
    simp
  calc ‖∑ n ∈ Finset.Ioc ⌊N⌋₊ ⌊R⌋₊,
        ((((n : ℝ) + u : ℝ)) : ℂ) ^ (-(Complex.I * (t : ℂ)))‖
      ≤ ∑ n ∈ Finset.Ioc ⌊N⌋₊ ⌊R⌋₊,
          ‖((((n : ℝ) + u : ℝ)) : ℂ) ^ (-(Complex.I * (t : ℂ)))‖ := norm_sum_le _ _
    _ ≤ ∑ _n ∈ Finset.Ioc ⌊N⌋₊ ⌊R⌋₊, (1 : ℝ) := Finset.sum_le_sum hterm
    _ = ((Finset.Ioc ⌊N⌋₊ ⌊R⌋₊).card : ℝ) := by simp
    _ ≤ N + 1 := by
      rw [Nat.card_Ioc]
      have hRle : (⌊R⌋₊ : ℝ) ≤ 2 * N := by
        have h1 : ⌊R⌋₊ ≤ ⌊2 * N⌋₊ := Nat.floor_mono hR2
        have h2 : (⌊2 * N⌋₊ : ℝ) ≤ 2 * N := Nat.floor_le (by linarith)
        exact le_trans (by exact_mod_cast h1) h2
      have hNlt : N < (⌊N⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one N
      rcases le_or_gt ⌊R⌋₊ ⌊N⌋₊ with h | h
      · have hz : ⌊R⌋₊ - ⌊N⌋₊ = 0 := Nat.sub_eq_zero_of_le h
        rw [hz]; simp; linarith
      · have hcast : ((⌊R⌋₊ - ⌊N⌋₊ : ℕ) : ℝ) = (⌊R⌋₊ : ℝ) - (⌊N⌋₊ : ℝ) := by
          rw [Nat.cast_sub (le_of_lt h)]
        rw [hcast]; linarith

/-- Ford §5 Vinogradov extraction for `λ ≥ 13/5`. -/
theorem vk_lambda_large_assembly :
    ∃ C D : ℝ, 0 < C ∧ 0 < D ∧
      ∀ N t u R : ℝ, 2 ≤ N → N ≤ t → (13 / 5 : ℝ) * Real.log N ≤ Real.log t →
        0 < u → u ≤ 1 → N < R → R ≤ 2 * N →
        ‖Work.BMF.Ssum N u t R‖ ≤
          C * N ^ (1 - 1 / (D * (Real.log t / Real.log N) ^ 2)) := by
  refine ⟨dC, dD, dC_pos, dD_pos, ?_⟩
  intro N t u R hN hNt hlogt hu hu1 hR hR2
  have hN1 : (1 : ℝ) ≤ N := by linarith
  have hNpos : (0 : ℝ) < N := by linarith
  have hlogNpos : 0 < Real.log N := Real.log_pos (by linarith)
  have ht0 : 0 < t := by linarith
  have ht1 : (1 : ℝ) ≤ t := by linarith
  have hsK : 0 < stechK := stechK_pos
  have hldC : Real.log dC ≥ 100 := by
    rw [dC_log]; nlinarith
  set lam : ℝ := dLam N t with hlamdef
  have hlamge : (13 / 5 : ℝ) ≤ lam := by
    rw [hlamdef, dLam, le_div_iff₀ hlogNpos]
    linarith
  have hlmdD : 0 < dD * lam ^ 2 :=
    mul_pos dD_pos (pow_pos (by linarith) 2)
  by_cases hA : Real.log N ≤ (1 / 3) * dD * lam ^ 2 * Real.log dC
  · -- ## Region A : trivial bound
    have hsum := Ssum_norm_le N t u R (by linarith) hu hR2
    have h1 : Real.log N / (dD * lam ^ 2) ≤ (1 / 3 : ℝ) * Real.log dC := by
      rw [div_le_iff₀ hlmdD]; nlinarith [hA]
    have h2 : Real.log N * (1 / (dD * lam ^ 2)) ≤ Real.log dC - 1 := by
      rw [mul_one_div]
      nlinarith [h1, hldC]
    have hexp : N ^ (1 / (dD * lam ^ 2)) ≤ dC / 2 := by
      rw [Real.rpow_def_of_pos hNpos]
      calc Real.exp (Real.log N * (1 / (dD * lam ^ 2)))
          ≤ Real.exp (Real.log dC - 1) := Real.exp_le_exp.mpr h2
        _ = dC / Real.exp 1 := by rw [Real.exp_sub, Real.exp_log dC_pos]
        _ ≤ dC / 2 := by
            apply div_le_div_of_nonneg_left dC_pos.le (by norm_num)
            have := Real.exp_one_gt_d9; linarith
    have h3 : N ≤ (dC / 2) * N ^ (1 - 1 / (dD * lam ^ 2)) := by
      have hsplit : (N : ℝ) = N ^ (1 / (dD * lam ^ 2)) * N ^ (1 - 1 / (dD * lam ^ 2)) := by
        rw [← Real.rpow_add hNpos,
          show (1 / (dD * lam ^ 2)) + (1 - 1 / (dD * lam ^ 2)) = 1 by ring, Real.rpow_one]
      calc (N : ℝ) = N ^ (1 / (dD * lam ^ 2)) * N ^ (1 - 1 / (dD * lam ^ 2)) := hsplit
        _ ≤ (dC / 2) * N ^ (1 - 1 / (dD * lam ^ 2)) :=
            mul_le_mul_of_nonneg_right hexp (Real.rpow_nonneg hNpos.le _)
    calc ‖Work.BMF.Ssum N u t R‖ ≤ N + 1 := hsum
      _ ≤ 2 * N := by linarith
      _ ≤ 2 * ((dC / 2) * N ^ (1 - 1 / (dD * lam ^ 2))) := by linarith [h3]
      _ = dC * N ^ (1 - 1 / (dD * lam ^ 2)) := by ring
  · -- ## Region B : the extraction
    push_neg at hA
    have hlm1 : (1 : ℝ) ≤ lam := by linarith
    have hlm2 : (1 : ℝ) ≤ lam ^ 2 := by nlinarith
    have hlogN10 : 10 ≤ Real.log N := by
      have hkey : (10 : ℝ) ≤ (1 / 3) * dD * lam ^ 2 * Real.log dC := by
        rw [dD]; nlinarith [hldC, hlm2]
      linarith [hA]
    have hlogN1000 : 1000 * lam ^ 2 ≤ Real.log N := by
      have hkey : 1000 * lam ^ 2 ≤ (1 / 3) * dD * lam ^ 2 * Real.log dC := by
        rw [dD]
        have h0 : 100 * lam ^ 2 ≤ Real.log dC * lam ^ 2 :=
          mul_le_mul_of_nonneg_right hldC (sq_nonneg lam)
        nlinarith [h0]
      linarith [hA]
    obtain ⟨hlam1, hlamH, hHlam1, hg2l1, hgl6, hkg, hk2, hkl5, hg5l, hH1, hHg, hgK,
            hdR2, hS1, h13g, hS2g, hSr, hrplo, hrphi, hsplo, hsphi, hrslo, hrshi⟩ :=
      vk_large_lam_bounds lam hlamge
    have hrp1 : 1 ≤ dRp lam := by
      have h300 : (1 : ℝ) ≤ 300 * lam ^ 2 / (dK lam : ℝ) := by
        rw [le_div_iff₀ (by exact_mod_cast (show 0 < dK lam by omega))]
        nlinarith [hkl5, hlm1, sq_nonneg lam]
      have : (1 : ℝ) ≤ (dRp lam : ℝ) := le_trans h300 (Nat.le_ceil _)
      exact_mod_cast this
    have hsp1 : 1 ≤ dSp lam := by
      have h200 : (1 : ℝ) ≤ 200 * lam ^ 2 / (dG lam : ℝ) := by
        rw [le_div_iff₀ (by exact_mod_cast (show 0 < dG lam by omega))]
        nlinarith [hgl6, hlm1, sq_nonneg lam]
      have : (1 : ℝ) ≤ (dSp lam : ℝ) := le_trans h200 (Nat.le_ceil _)
      exact_mod_cast this
    have hg2 : 2 ≤ dG lam := by
      have : (2 : ℝ) ≤ (dG lam : ℝ) := by linarith [hg5l, hlamge]
      exact_mod_cast this
    obtain ⟨hMge1, hMsq, hmu_ge, hmu_le⟩ := vk_large_M_bounds N hN hlogN10
    have hMpos' : 0 < (dM N : ℝ) := by
      have : (1 : ℝ) ≤ (dM N : ℝ) := by exact_mod_cast hMge1
      linarith
    have hMle : (dM N : ℝ) ≤ 2 * N ^ ((2 : ℝ) / 5) := by
      have h1 : (dM N : ℝ) < N ^ ((2 : ℝ) / 5) + 1 := by
        rw [dM]; exact Nat.ceil_lt_add_one (by positivity)
      have h2 : (1 : ℝ) ≤ N ^ ((2 : ℝ) / 5) := Real.one_le_rpow hN1 (by norm_num)
      linarith
    have hrs_pos : 0 < 2 * (dR lam : ℝ) * (dS lam : ℝ) := by
      have hl4 : 0 < lam ^ 4 := pow_pos (by linarith) 4
      linarith [hrslo, hl4]
    have hdelta : dDelta lam ≤ lam ^ 2 / 40 := vk_large_delta_bound lam hlamge
    have hconst := vk_large_const_bound lam hlamge
    have hC0pos : 0 < dC0 lam := by
      have hSF1 : 0 < stechF (dK lam) (dRp lam) := stechF_pos _ _
      have hSF2 : 0 < stechF (dG lam) (dSp lam) := stechF_pos _ _
      have hs5 : 0 < 5 * (dR lam : ℝ) := by
        have : (1 : ℝ) ≤ (dR lam : ℝ) := by exact_mod_cast (by omega : 1 ≤ dR lam)
        linarith
      have hds : 0 < (dS lam : ℝ) := by
        have : (1 : ℝ) ≤ (dS lam : ℝ) := by exact_mod_cast hS1
        linarith
      rw [dC0]
      exact mul_pos (mul_pos (mul_pos (mul_pos (pow_pos hs5 _) (pow_pos hds _)) hSF1) hSF2)
        (pow_pos (by norm_num) _)
    have hDnn : 0 ≤ dDelta lam := by
      have hk1 : (1 : ℝ) ≤ (dK lam : ℝ) := by exact_mod_cast (by omega : 1 ≤ dK lam)
      have hg1' : (1 : ℝ) ≤ (dG lam : ℝ) := by exact_mod_cast (by omega : 1 ≤ dG lam)
      have hbk : 0 ≤ 1 - 1 / (dK lam : ℝ) := by
        rw [sub_nonneg, div_le_one (by linarith)]; linarith
      have hbg : 0 ≤ 1 - 1 / (dG lam : ℝ) := by
        rw [sub_nonneg, div_le_one (by linarith)]; linarith
      rw [dDelta]
      exact add_nonneg (mul_nonneg (by positivity) (pow_nonneg hbk _))
        (mul_nonneg (by positivity) (pow_nonneg hbg _))
    have hDle : dDelta lam ≤ 2 * (dR lam : ℝ) * (dS lam : ℝ) := by
      nlinarith [hdelta, hrslo, hlm2, sq_nonneg lam]
    -- apply Ford's Lemma 5.1
    have h51 := Work.BMF.vkford_lemma51 (dK lam) (dR lam) (dS lam) (dH lam) (dG lam)
      hdR2 hS1 hH1 hHg hgK N t u R (dM N) (dM N) hN1 hMge1 hMge1
      (by rw [← sq]; exact hMsq) ht0 hu hu1 hR hR2
    have h51' : ‖Work.BMF.Ssum N u t R‖
        ≤ 2 * (dM N : ℝ) * (dM N : ℝ)
          + t * ((dM N : ℝ) * (dM N : ℝ)) ^ (dK lam + 1) / ((dK lam : ℝ) * N ^ (dK lam))
          + N * (Work.BMF.Pprod (dK lam) (dR lam) (dS lam) (dH lam) (dG lam) N t (dM N) (dM N))
              ^ (1 / (2 * (dR lam : ℝ) * (dS lam : ℝ))) := by
      have h := h51
      rw [← Work.BMF.Pprod] at h
      simpa only [Work.BMF.Ssum] using h
    have hPprod := Pprod_le_C0 lam N t (by linarith) ht1 hMpos' hMge1
      (by rw [hlamdef]; rfl) (by linarith) hk2 hrp1 hg2 hsp1 hH1 hHg
      (by exact_mod_cast hS1) h13g hS2g hSr
    have hPpow := Pprod_rpow_bound lam N t hNpos hMpos' hMge1 hMle
      (by omega) hS1 hH1 ht0 hDnn hDle hrs_pos hC0pos hconst hPprod
    have hHlow : lam ^ 2 / 10 ≤ dHsum (dH lam) (dG lam) (dMu N) (dMu N) lam :=
      Work.BMF.vkford_H_lower2 (dH lam) (dG lam) (dMu N) (dMu N) lam
        hlam1 hlamH hHlam1 hg2l1 hgl6 hmu_ge hmu_ge (by linarith [hmu_le])
    have hsave : (9 / 100) * lam ^ 2
        ≤ dHsum (dH lam) (dG lam) (dMu N) (dMu N) lam - (2 / 5) * dDelta lam := by
      nlinarith [hHlow, hdelta]
    have hexp_le : -((dHsum (dH lam) (dG lam) (dMu N) (dMu N) lam - (2 / 5) * dDelta lam)
          / (2 * (dR lam : ℝ) * (dS lam : ℝ))) ≤ -(1 / (dD * lam ^ 2)) := by
      have hl2pos : 0 < lam ^ 2 := by positivity
      have hA1 : 1 / (dD * lam ^ 2) ≤ (9 / (100 * 127 * 10 ^ 3)) / lam ^ 2 := by
        rw [div_le_div_iff₀ (by positivity) hl2pos, dD]
        nlinarith [hl2pos]
      have hA2 : (9 / (100 * 127 * 10 ^ 3)) / lam ^ 2
          ≤ (9 / 100) * lam ^ 2 / (2 * (dR lam : ℝ) * (dS lam : ℝ)) := by
        have hc : 2 * (dR lam : ℝ) * (dS lam : ℝ) ≤ 127 * 10 ^ 3 * lam ^ 4 := hrshi
        have h1 : lam ^ 2 / (127 * 10 ^ 3 * lam ^ 4)
            ≤ lam ^ 2 / (2 * (dR lam : ℝ) * (dS lam : ℝ)) :=
          div_le_div_of_nonneg_left (sq_nonneg lam) hrs_pos hc
        have heq : lam ^ 2 / (127 * 10 ^ 3 * lam ^ 4) = (1 / (127 * 10 ^ 3)) / lam ^ 2 := by
          field_simp
        rw [heq] at h1
        calc (9 / (100 * 127 * 10 ^ 3)) / lam ^ 2
            = (9 / 100) * ((1 / (127 * 10 ^ 3)) / lam ^ 2) := by ring
          _ ≤ (9 / 100) * (lam ^ 2 / (2 * (dR lam : ℝ) * (dS lam : ℝ))) :=
              mul_le_mul_of_nonneg_left h1 (by norm_num)
          _ = (9 / 100) * lam ^ 2 / (2 * (dR lam : ℝ) * (dS lam : ℝ)) := by ring
      have h4 : (9 / 100) * lam ^ 2 / (2 * (dR lam : ℝ) * (dS lam : ℝ))
          ≤ (dHsum (dH lam) (dG lam) (dMu N) (dMu N) lam - (2 / 5) * dDelta lam)
              / (2 * (dR lam : ℝ) * (dS lam : ℝ)) :=
        div_le_div_of_nonneg_right hsave hrs_pos.le
      have h1 : 1 / (dD * lam ^ 2)
          ≤ (dHsum (dH lam) (dG lam) (dMu N) (dMu N) lam - (2 / 5) * dDelta lam)
              / (2 * (dR lam : ℝ) * (dS lam : ℝ)) := le_trans hA1 (le_trans hA2 h4)
      linarith [h1]
    have hthird_le : N * (Work.BMF.Pprod (dK lam) (dR lam) (dS lam) (dH lam) (dG lam)
            N t (dM N) (dM N)) ^ (1 / (2 * (dR lam : ℝ) * (dS lam : ℝ)))
        ≤ 2 * Real.exp (10 ^ 33 * (1 + stechK)) * N ^ (1 - 1 / (dD * lam ^ 2)) := by
      have h1 := mul_le_mul_of_nonneg_left hPpow hNpos.le
      calc N * (Work.BMF.Pprod (dK lam) (dR lam) (dS lam) (dH lam) (dG lam)
              N t (dM N) (dM N)) ^ (1 / (2 * (dR lam : ℝ) * (dS lam : ℝ)))
          ≤ N * (2 * Real.exp (10 ^ 33 * (1 + stechK))
              * N ^ (-((dHsum (dH lam) (dG lam) (dMu N) (dMu N) lam - (2 / 5) * dDelta lam)
                  / (2 * (dR lam : ℝ) * (dS lam : ℝ))))) := h1
        _ ≤ N * (2 * Real.exp (10 ^ 33 * (1 + stechK)) * N ^ (-(1 / (dD * lam ^ 2)))) := by
            apply mul_le_mul_of_nonneg_left _ hNpos.le
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            exact Real.rpow_le_rpow_of_exponent_le hN1 (by linarith [hexp_le])
        _ = 2 * Real.exp (10 ^ 33 * (1 + stechK)) * (N * N ^ (-(1 / (dD * lam ^ 2)))) := by
            ring
        _ = 2 * Real.exp (10 ^ 33 * (1 + stechK)) * N ^ (1 - 1 / (dD * lam ^ 2)) := by
            have hmerge : (N : ℝ) * N ^ (-(1 / (dD * lam ^ 2)))
                = N ^ (1 - 1 / (dD * lam ^ 2)) := by
              nth_rewrite 1 [← Real.rpow_one N]
              rw [← Real.rpow_add hNpos]
              ring_nf
            rw [hmerge]
    obtain ⟨heasy1, heasy2⟩ := vk_large_easy_terms2 N t hN hNt lam hlamdef hlamge hlogN1000
    have h10 : 10 * N ^ ((4:ℝ) / 5) ≤ 10 * N ^ (1 - 1 / (dD * lam ^ 2)) := by
      have h45 : (4 / 5 : ℝ) ≤ 1 - 1 / (dD * lam ^ 2) := by
        have h15 : 1 / (dD * lam ^ 2) ≤ 1 / 5 := by
          rw [div_le_div_iff₀ (by positivity) (by norm_num : (0 : ℝ) < 5), dD]
          nlinarith [hlm2]
        linarith
      exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hN1 h45) (by norm_num)
    have hconst_le : 10 + 2 * Real.exp (10 ^ 33 * (1 + stechK))
        ≤ Real.exp (10 ^ 33 * (1 + stechK) + 100) := by
      rw [Real.exp_add]
      have h1 : (1 : ℝ) ≤ Real.exp (10 ^ 33 * (1 + stechK)) := by
        have h0 : (0 : ℝ) ≤ 10 ^ 33 * (1 + stechK) := by positivity
        have h := Real.add_one_le_exp (10 ^ 33 * (1 + stechK)); linarith
      have h2 : (12 : ℝ) ≤ Real.exp 100 := by
        have h := Real.add_one_le_exp (100 : ℝ); linarith
      nlinarith [h1, h2, Real.exp_pos (10 ^ 33 * (1 + stechK))]
    calc ‖Work.BMF.Ssum N u t R‖
        ≤ 2 * (dM N : ℝ) * (dM N : ℝ)
          + t * ((dM N : ℝ) * (dM N : ℝ)) ^ (dK lam + 1) / ((dK lam : ℝ) * N ^ (dK lam))
          + N * (Work.BMF.Pprod (dK lam) (dR lam) (dS lam) (dH lam) (dG lam) N t (dM N) (dM N))
              ^ (1 / (2 * (dR lam : ℝ) * (dS lam : ℝ))) := h51'
      _ ≤ 8 * N ^ ((4:ℝ) / 5) + 2 * N ^ ((4:ℝ) / 5)
          + 2 * Real.exp (10 ^ 33 * (1 + stechK)) * N ^ (1 - 1 / (dD * lam ^ 2)) := by
          linarith [heasy1, heasy2, hthird_le]
      _ ≤ dC * N ^ (1 - 1 / (dD * lam ^ 2)) := by
          rw [dC]
          have htot : 8 * N ^ ((4:ℝ) / 5) + 2 * N ^ ((4:ℝ) / 5)
              + 2 * Real.exp (10 ^ 33 * (1 + stechK)) * N ^ (1 - 1 / (dD * lam ^ 2))
              ≤ (10 + 2 * Real.exp (10 ^ 33 * (1 + stechK)))
                  * N ^ (1 - 1 / (dD * lam ^ 2)) := by
            linarith [h10]
          calc 8 * N ^ ((4:ℝ) / 5) + 2 * N ^ ((4:ℝ) / 5)
              + 2 * Real.exp (10 ^ 33 * (1 + stechK)) * N ^ (1 - 1 / (dD * lam ^ 2))
              ≤ (10 + 2 * Real.exp (10 ^ 33 * (1 + stechK)))
                  * N ^ (1 - 1 / (dD * lam ^ 2)) := htot
            _ ≤ Real.exp (10 ^ 33 * (1 + stechK) + 100) * N ^ (1 - 1 / (dD * lam ^ 2)) :=
                mul_le_mul_of_nonneg_right hconst_le (Real.rpow_nonneg hNpos.le _)

end

end Work.BMF.liouville
