import Mathlib
import Submission.Work.BMF.VKF.defs
import Submission.Work.BMF.VKF.bracket
import Submission.Work.BMF.VKF.vkf_params
import Submission.Work.BMF.VKF.vkf_delta
import Submission.Work.BMF.VKF.vkf_kappa
import Submission.Work.BMF.VKF.vkf_T2
import Submission.Work.BMF.VKF.vkf_index
import Submission.Work.BMF.VKExpSum.ford51_Mfacts
import Submission.Work.BMF.vkford_lemma51

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The deep regime of the Ford §5 estimate

`Work.BMF.VKF.vkf_deep` is the exploitation of Ford's Lemma 5.1
(`Work.BMF.vkford_lemma51`) plus `Work.BMF.VKF.vkf_bracket` for `λ = log t/log N ≥ 13/5` and
`log N ≥ dK0·λ²`:

`‖Σ_{N<n≤R}(n+u)^{-it}‖ ≤ 3·dC·N^{1-1/(dD λ²)}`.

The three terms of Lemma 5.1 are bounded by `dC·N^{1-1/(dDλ²)}` each:

* `2M² ≤ 8N^{4/5}` and `1-1/(dDλ²) ≥ 4/5` (the `M`-factor `M = ⌈N^{2/5}⌉ ≤ 2N^{2/5}`),
* the Taylor term (`Work.BMF.VKF.vkf_T2`), and
* the extraction term `N·bracket^{1/(2rs)}`, where the bracket is at most
  `κ·M^{Δ₁+Δ₂}·N^{-H}` (`Work.BMF.VKF.vkf_bracket`), so the extraction term is
  `κ^{1/(2rs)}·N^{1-(H-(Δ₁+Δ₂)μ)/(2rs)}`; now `κ^{1/(2rs)} ≤ dC` (`Work.BMF.VKF.vkf_kappa`)
  and `(H-(Δ₁+Δ₂)μ)/(2rs) ≥ 1/(dDλ²)` (`Work.BMF.VKF.vkf_index`).
-/

namespace Work.BMF.VKF

open Finset
open scoped BigOperators
open LeanEval.NumberTheory.VinogradovMeanValue

noncomputable section

set_option maxHeartbeats 4000000

theorem vkf_deep :
    ∀ N t u R : ℝ, 2 ≤ N → N ≤ t → (13 / 5) * Real.log N ≤ Real.log t →
      dK0 * (Real.log t / Real.log N) ^ 2 ≤ Real.log N →
      0 < u → u ≤ 1 → N < R → R ≤ 2 * N →
      ‖Work.BMF.Ssum N u t R‖
        ≤ 3 * dC * N ^ (1 - 1 / (dD * (Real.log t / Real.log N) ^ 2)) := by
  intro N t u R hN2 hNt hlam13 hreg hu hu1 hR hR2
  have hN1 : 1 < N := by linarith
  have hNpos : (0 : ℝ) < N := by linarith
  have ht1 : 1 ≤ t := by linarith
  have hlogN : 0 < Real.log N := Real.log_pos hN1
  set lam : ℝ := Real.log t / Real.log N with hlamdef
  have hlam : 13 / 5 ≤ lam := by
    rw [hlamdef, le_div_iff₀ hlogN]; linarith
  have hsK0 : 0 ≤ sK := sK_nonneg
  have hlog70 : 70 ≤ Real.log N := by
    have hA : (300 : ℝ) ≤ dK0 := by
      have h : (0 : ℝ) ≤ sK := sK_nonneg
      rw [dK0]; linarith
    have hB : ((13 : ℝ) / 5) ^ 2 ≤ lam ^ 2 := by nlinarith [hlam]
    have h1 : (300 : ℝ) * (13 / 5) ^ 2 ≤ dK0 * lam ^ 2 :=
      mul_le_mul hA hB (by norm_num) (by linarith)
    have h2 : (300 : ℝ) * (13 / 5) ^ 2 = 2028 := by norm_num
    linarith [h1, hreg, h2]
  -- Ford's parameters
  have hpar := vkf_params lam hlam
  obtain ⟨hph1, hph2, hphg, hpg1, hpk_eq, hpg2, hpg3, hpk_ge, hpk_le, hprpmul, hprp_le,
      hspmul, hsp_le, hr_ge, hr_le, hs_ge, hs_le, h13g, hsr, hs2g, hr2, hs1n⟩ := hpar
  -- `M`-facts
  obtain ⟨hM1ge, hMpowV, hmu_geV, hmu_leV, hM2leNV, hMle2NV⟩ :=
    (Work.BMF.VKExpSum.ford51_Mfacts N hN2 hlog70)
  have hdMc : ((dM N : ℕ) : ℝ) = ((Work.BMF.VKExpSum.dM N : ℕ) : ℝ) := rfl
  have hdMuc : dMu N = Work.BMF.VKExpSum.dMu N := rfl
  have hMpow : ((dM N : ℕ) : ℝ) = N ^ (dMu N) := by rw [hdMc, hdMuc]; exact hMpowV
  have hM2leN : ((dM N : ℕ) : ℝ) ^ 2 ≤ N := by rw [hdMc]; exact hM2leNV
  have hMle2N : ((dM N : ℕ) : ℝ) ≤ 2 * N ^ ((2 : ℝ) / 5) := by rw [hdMc]; exact hMle2NV
  have hmu_ge : (2 : ℝ) / 5 ≤ dMu N := by rw [hdMuc]; exact hmu_geV
  have hmu_le : dMu N ≤ 41 / 100 := by rw [hdMuc]; exact hmu_leV
  have hMnn : (0 : ℝ) ≤ ((dM N : ℕ) : ℝ) := by
    have h : (1 : ℝ) ≤ ((dM N : ℕ) : ℝ) := by exact_mod_cast hM1ge
    linarith
  have hMpos : (0 : ℝ) < ((dM N : ℕ) : ℝ) := by
    have h : (1 : ℝ) ≤ ((dM N : ℕ) : ℝ) := by exact_mod_cast hM1ge
    linarith
  have hMprod : ((dM N : ℕ) : ℝ) * ((dM N : ℕ) : ℝ) ≤ N := by
    have h := hM2leN
    nlinarith [h]
  have hg2 : 2 ≤ dG lam := by
    have h := hpg2
    have h1 : (2 : ℝ) ≤ (dG lam : ℝ) := by linarith
    exact_mod_cast h1
  have hk2 : 2 ≤ dK lam := by
    have h := hpk_ge
    have h1 : (2 : ℝ) ≤ (dK lam : ℝ) := by linarith
    exact_mod_cast h1
  have hh1 : 1 ≤ dH lam := by
    have h1 : (1 : ℝ) ≤ (dH lam : ℝ) := by linarith
    exact_mod_cast h1
  have hgk : dG lam ≤ dK lam := by rw [dK]; omega
  have hmu0 : 0 ≤ dMu N := by linarith [hmu_ge]
  have hmusum : dMu N + dMu N < 1 := by linarith [hmu_le]
  have hrp1 : 1 ≤ dRp lam := by
    by_contra h
    have h0 : dRp lam = 0 := by omega
    rw [h0] at hprpmul
    push_cast at hprpmul
    nlinarith [hlam]
  have hsp1 : 1 ≤ dSp lam := by
    by_contra h
    have h0 : dSp lam = 0 := by omega
    rw [h0] at hspmul
    push_cast at hspmul
    nlinarith [hlam]
  have hs1R : (1 : ℝ) ≤ ((dS lam : ℕ) : ℝ) := by exact_mod_cast hs1n
  -- the delta, index and kappa inputs
  obtain ⟨hD1, hD2⟩ := vkf_delta lam hlam hpk_le hprpmul hpg1 hspmul
  have hidx := vkf_index N lam hN2 hlog70 hlam hph1 hph2 hpg2 hpg3 hmu_ge hmu_le hD1 hD2
    hr_ge hs_ge hr_le hs_le
  have hrd : ((dR lam : ℕ) : ℝ) = ((dK lam : ℕ) : ℝ) * ((dRp lam : ℕ) : ℝ) := by
    rw [dR]; push_cast; ring
  have hsd : ((dS lam : ℕ) : ℝ) = ((dG lam : ℕ) : ℝ) * ((dSp lam : ℕ) : ℝ) := by
    rw [dS]; push_cast; ring
  have hkap := vkf_kappa lam hlam hr_ge hs_ge hpk_le hpg1 hpk_eq hrd hsd hprp_le hsp_le hph1
  -- the bracket
  set BR : ℝ := (5 * ((dR lam : ℕ) : ℝ)) ^ (dK lam) * ((dM N : ℕ) : ℝ) ^ (-(2 * ((dS lam : ℕ) : ℝ)))
      * ((dM N : ℕ) : ℝ) ^ (-(2 * ((dR lam : ℕ) : ℝ)) + (dK lam : ℝ) * ((dK lam : ℝ) + 1) / 2)
      * J (dR lam) (dK lam) (dM N)
      * Work.BMF.Jincom (dS lam) (dG lam) (dH lam) (Finset.Icc 1 (dM N))
      * ∏ j ∈ Finset.Icc (dH lam) (dG lam),
          Work.BMF.fordW ((dR lam : ℕ) : ℝ) ((dS lam : ℕ) : ℝ) t N ((dM N : ℕ) : ℝ)
            ((dM N : ℕ) : ℝ) j with hBRdef
  have hBR0 : 0 ≤ BR := by
    rw [hBRdef]
    have h5R : (0 : ℝ) ≤ 5 * ((dR lam : ℕ) : ℝ) := by
      have h : (0 : ℝ) < ((dR lam : ℕ) : ℝ) := lt_of_lt_of_le (by nlinarith [hlam]) hr_ge
      linarith
    have hJ0 : 0 ≤ J (dR lam) (dK lam) (dM N) := by
      rw [LeanEval.NumberTheory.VinogradovMeanValue.J]; positivity
    have hI0 : 0 ≤ Work.BMF.Jincom (dS lam) (dG lam) (dH lam) (Finset.Icc 1 (dM N)) := by
      rw [Work.BMF.Jincom]; positivity
    have hW0 : 0 ≤ ∏ j ∈ Finset.Icc (dH lam) (dG lam),
        Work.BMF.fordW ((dR lam : ℕ) : ℝ) ((dS lam : ℕ) : ℝ) t N ((dM N : ℕ) : ℝ)
          ((dM N : ℕ) : ℝ) j :=
      Finset.prod_nonneg fun j hj => Work.BMF.fordW_nonneg _ _ _ _ _ _ j
        (le_of_lt (lt_of_lt_of_le (by nlinarith [hlam]) hr_ge))
        (le_of_lt (lt_of_lt_of_le (by nlinarith [hlam]) hs_ge)) hMnn hMnn (by linarith) hNpos
        (le_trans hh1 (Finset.mem_Icc.mp hj).1)
    exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg
      (pow_nonneg h5R _) (Real.rpow_nonneg hMnn _)) (Real.rpow_nonneg hMnn _)) hJ0) hI0) hW0
  have hbr := vkf_bracket N t (dH lam) (dG lam) (dK lam) (dRp lam) (dSp lam) (dM N)
    (dMu N) lam ((dR lam : ℕ) : ℝ) ((dS lam : ℕ) : ℝ) rfl rfl hN1 ht1 hMpos hMpow
    hk2 hrp1 hsp1 hM1ge hh1 hphg hgk hg2 hmu0 hmusum hlamdef h13g hs2g hsr hs1R
  -- Ford's Lemma 5.1
  have h51 := Work.BMF.vkford_lemma51 (dK lam) (dR lam) (dS lam) (dH lam) (dG lam)
    hr2 hs1n hh1 hphg hgk N t u R (dM N) (dM N) (le_of_lt hN1) hM1ge hM1ge hMprod
    (by linarith) hu hu1 hR hR2
  -- fold the bracket bound into the vocabulary of the `kappa`/`delta`/`index` inputs
  have hKAPeq : (5 * ((dR lam : ℕ) : ℝ)) ^ (dK lam) * ((dS lam : ℕ) : ℝ) ^ (dH lam - 1)
      * 2 ^ ((dG lam + 3) * (dG lam - dH lam + 1))
      * Work.BMF.liouville.stechF (dK lam) (dRp lam)
      * Work.BMF.liouville.stechF (dG lam) (dSp lam) = dKappa lam := rfl
  have hD1eq : (dK lam : ℝ) ^ 2 / 2 * (1 - 1 / (dK lam : ℝ)) ^ (dRp lam) = dDelta1 lam := rfl
  have hD2eq : (dG lam : ℝ) ^ 2 / 2 * (1 - 1 / (dG lam : ℝ)) ^ (dSp lam) = dDelta2 lam := rfl
  have hHeq : (∑ j ∈ Finset.Icc (dH lam) (dG lam),
      min ((j : ℝ) * dMu N) (min ((j : ℝ) - lam) (lam - (j : ℝ) * (1 - dMu N - dMu N))))
      = dHidx N lam := rfl
  have hbrf : BR ≤ dKappa lam * ((dM N : ℕ) : ℝ) ^ (dDelta1 lam + dDelta2 lam)
      * N ^ (-(dHidx N lam)) := by
    rw [hKAPeq, hD1eq, hD2eq, hHeq] at hbr
    exact hbr
  -- the first two terms
  have hT1 : 2 * ((dM N : ℕ) : ℝ) * ((dM N : ℕ) : ℝ)
      ≤ dC * N ^ (1 - 1 / (dD * lam ^ 2)) := by
    have hM2 : ((dM N : ℕ) : ℝ) ^ 2 ≤ 4 * N ^ ((4 : ℝ) / 5) := by
      have h := pow_le_pow_left₀ hMnn hMle2N 2
      calc ((dM N : ℕ) : ℝ) ^ 2 ≤ (2 * N ^ ((2 : ℝ) / 5)) ^ 2 := h
        _ = 4 * N ^ ((4 : ℝ) / 5) := by
            rw [mul_pow, ← Real.rpow_natCast (N ^ ((2 : ℝ) / 5)) 2, ← Real.rpow_mul hNpos.le]
            norm_num
    have hexp1 : (4 : ℝ) / 5 ≤ 1 - 1 / (dD * lam ^ 2) := by
      have hdD5 : (5 : ℝ) ≤ dD := by norm_num [dD]
      have hl2 : (1 : ℝ) ≤ lam ^ 2 := by nlinarith [hlam]
      have h5 : (5 : ℝ) ≤ dD * lam ^ 2 :=
        le_trans (by norm_num : (5 : ℝ) ≤ 5 * 1)
          (mul_le_mul hdD5 hl2 (by norm_num) (by linarith))
      have h6 : 1 / (dD * lam ^ 2) ≤ (1 : ℝ) / 5 := by
        rw [div_le_div_iff₀ (by linarith) (by norm_num)]
        linarith
      linarith
    have h8dC : (8 : ℝ) ≤ dC := by
      have h2 : (1000 : ℝ) ≤ 1000 + 100 * sK := by linarith [sK_nonneg]
      have h4 : (1001 : ℝ) ≤ Real.exp (1000 + 100 * sK) := by
        have h3 := Real.add_one_le_exp (1000 + 100 * sK)
        linarith
      rw [dC]
      linarith
    have hN4 : N ^ ((4 : ℝ) / 5) ≤ N ^ (1 - 1 / (dD * lam ^ 2)) :=
      Real.rpow_le_rpow_of_exponent_le (le_of_lt hN1) hexp1
    calc 2 * ((dM N : ℕ) : ℝ) * ((dM N : ℕ) : ℝ) = 2 * ((dM N : ℕ) : ℝ) ^ 2 := by ring
      _ ≤ 2 * (4 * N ^ ((4 : ℝ) / 5)) := by linarith [hM2]
      _ = 8 * N ^ ((4 : ℝ) / 5) := by ring
      _ ≤ 8 * N ^ (1 - 1 / (dD * lam ^ 2)) :=
          mul_le_mul_of_nonneg_left hN4 (by norm_num)
      _ ≤ dC * N ^ (1 - 1 / (dD * lam ^ 2)) :=
          mul_le_mul_of_nonneg_right h8dC (Real.rpow_nonneg hNpos.le _)
  have hT2 := vkf_T2 N t ((dM N : ℕ) : ℝ) lam (dK lam) hN2 hNt hlamdef hlam
    (by have := dG_ge lam; rw [dK_eq]; linarith) hpk_le hMnn hMle2N hreg
  -- the extraction term
  have hT3 : N * BR ^ (1 / (2 * ((dR lam : ℕ) : ℝ) * ((dS lam : ℕ) : ℝ)))
      ≤ dC * N ^ (1 - 1 / (dD * lam ^ 2)) := by
    set e : ℝ := 1 / (2 * ((dR lam : ℕ) : ℝ) * ((dS lam : ℕ) : ℝ)) with hedef
    have hrpos : 0 < ((dR lam : ℕ) : ℝ) := lt_of_lt_of_le (by nlinarith [hlam]) hr_ge
    have hspos : 0 < ((dS lam : ℕ) : ℝ) := lt_of_lt_of_le (by nlinarith [hlam]) hs_ge
    have hepos : 0 < e := by rw [hedef]; exact one_div_pos.mpr (by positivity)
    have hk0 : 0 < dKappa lam := dKappa_pos lam hlam
    have hkape : (dKappa lam) ^ e ≤ dC := by rw [hedef]; exact hkap
    have hidx2 : 1 / (dD * lam ^ 2)
        ≤ (dHidx N lam - (dDelta1 lam + dDelta2 lam) * dMu N) * e := by
      have h := hidx
      have h' : (dHidx N lam - (dDelta1 lam + dDelta2 lam) * dMu N)
            / (2 * ((dR lam : ℕ) : ℝ) * ((dS lam : ℕ) : ℝ))
          = (dHidx N lam - (dDelta1 lam + dDelta2 lam) * dMu N) * e := by
        rw [hedef]; ring
      rwa [h'] at h
    have hexp3 : dMu N * ((dDelta1 lam + dDelta2 lam) * e) + -(dHidx N lam) * e
        ≤ -(1 / (dD * lam ^ 2)) := by nlinarith [hidx2]
    have hstep1 : BR ^ e
        ≤ (dKappa lam * ((dM N : ℕ) : ℝ) ^ (dDelta1 lam + dDelta2 lam)
            * N ^ (-(dHidx N lam))) ^ e := by
      rw [hedef]
      exact Real.rpow_le_rpow hBR0 hbrf (le_of_lt hepos)
    have hsplit : (dKappa lam * ((dM N : ℕ) : ℝ) ^ (dDelta1 lam + dDelta2 lam)
          * N ^ (-(dHidx N lam))) ^ e
        = (dKappa lam) ^ e * (((dM N : ℕ) : ℝ) ^ (dDelta1 lam + dDelta2 lam)) ^ e
          * (N ^ (-(dHidx N lam))) ^ e := by
      rw [Real.mul_rpow (mul_nonneg (le_of_lt hk0) (Real.rpow_nonneg hMpos.le _))
            (Real.rpow_nonneg hNpos.le _),
        Real.mul_rpow (le_of_lt hk0) (Real.rpow_nonneg hMpos.le _)]
    have hMpp : (((dM N : ℕ) : ℝ) ^ (dDelta1 lam + dDelta2 lam)) ^ e
        = ((dM N : ℕ) : ℝ) ^ ((dDelta1 lam + dDelta2 lam) * e) :=
      (Real.rpow_mul hMnn _ _).symm
    have hNpp : (N ^ (-(dHidx N lam))) ^ e = N ^ (-(dHidx N lam) * e) :=
      (Real.rpow_mul hNpos.le _ _).symm
    have hMtoN : ((dM N : ℕ) : ℝ) ^ ((dDelta1 lam + dDelta2 lam) * e)
        = N ^ (dMu N * ((dDelta1 lam + dDelta2 lam) * e)) := by
      rw [hMpow, ← Real.rpow_mul hNpos.le]
    have hB : N ^ (dMu N * ((dDelta1 lam + dDelta2 lam) * e)) * N ^ (-(dHidx N lam) * e)
        ≤ N ^ (-(1 / (dD * lam ^ 2))) := by
      rw [← Real.rpow_add hNpos]
      exact Real.rpow_le_rpow_of_exponent_le (le_of_lt hN1) hexp3
    have hb2 : BR ^ e ≤ dC * N ^ (-(1 / (dD * lam ^ 2))) := by
      refine hstep1.trans ?_
      rw [hsplit, hMpp, hNpp, hMtoN, mul_assoc]
      exact mul_le_mul hkape hB
        (mul_nonneg (Real.rpow_nonneg hNpos.le _) (Real.rpow_nonneg hNpos.le _))
        (le_of_lt dC_pos)
    have hNN : N ^ (1 - 1 / (dD * lam ^ 2)) = N * N ^ (-(1 / (dD * lam ^ 2))) := by
      have h := Real.rpow_add hNpos (1 : ℝ) (-(1 / (dD * lam ^ 2)))
      rw [Real.rpow_one] at h
      simpa [sub_eq_add_neg] using h
    calc N * BR ^ e
        ≤ N * (dC * N ^ (-(1 / (dD * lam ^ 2)))) := mul_le_mul_of_nonneg_left hb2 hNpos.le
      _ = dC * (N * N ^ (-(1 / (dD * lam ^ 2)))) := by ring
      _ = dC * N ^ (1 - 1 / (dD * lam ^ 2)) := by rw [← hNN]

  -- conclude
  have hmain := h51
  calc ‖Work.BMF.Ssum N u t R‖
      ≤ 2 * ((dM N : ℕ) : ℝ) * ((dM N : ℕ) : ℝ)
        + t * (((dM N : ℕ) : ℝ) * ((dM N : ℕ) : ℝ)) ^ (dK lam + 1)
            / ((dK lam : ℝ) * N ^ (dK lam))
        + N * BR ^ (1 / (2 * ((dR lam : ℕ) : ℝ) * ((dS lam : ℕ) : ℝ))) := hmain
    _ ≤ dC * N ^ (1 - 1 / (dD * lam ^ 2)) + dC * N ^ (1 - 1 / (dD * lam ^ 2))
        + dC * N ^ (1 - 1 / (dD * lam ^ 2)) := by linarith [hT1, hT2, hT3]
    _ = 3 * dC * N ^ (1 - 1 / (dD * lam ^ 2)) := by ring

end

end Work.BMF.VKF
