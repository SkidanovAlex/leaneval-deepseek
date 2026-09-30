import Mathlib
import Submission.Work.BMF.VKGrowth
import Submission.Work.BMF.VKGrowthDefs
import Submission.Work.BMF.HurwitzShift
import Submission.Work.BMF.N7.V2_zeta_strip
import Submission.Work.BMF.N7.dyadic_vk_sum_bound
import Submission.Work.BMF.VKChain.block_sum_uniform
import Submission.Work.BMF.VKChain.shift_head_bound
import Submission.Work.BMF.VKChain.shift_vk_range_bound
import Submission.Work.BMF.VKChain.kl_tail_block_bound
import Submission.Work.BMF.VKChain.shiftTerm_kl_range_le
import Submission.Work.BMF.VKChain.shift_series_tsum_bound

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The Hurwitz-zeta growth bound in the Vinogradov–Korobov strip

Main result (`Work.BMF.VKChain.hurwitz_growth_abs_vk`): from the Vinogradov–Korobov
exponential-sum input `Work.BMF.VKExpInput` there are `A, c > 0` (with `c ≤ 1/4`) such that

`‖ζ(σ + i t, a)‖ ≤ A (a^{-σ} + (log (|t| + 3))^{6/7})`

for all `0 ≤ a ≤ 1`, `3 ≤ |t|`, `σ ≤ 2` and `σ ≥ 1 - c (log (|t| + 3))^{-6/7}`.

The proof assembles two inputs.

* The Riemann-zeta growth in the same strip, `Work.BMF.N7.zeta_strip_bound_of_vk_aux` applied to
  the arithmetic input `Work.BMF.N7.dyadic_vk_sum_bound` (the Euler–Maclaurin + VK-block +
  van-der-Corput chain of the `N7`/`VKChain` development).
* The shift-difference series `∑_m ((m+a)^{-s} - (m+1)^{-s})` bounded in the same strip
  (`Work.BMF.VKChain.shift_series_tsum_bound`, proven from the already-available pieces
  `shift_head_bound`, `shift_vk_range_bound`, `block_sum_uniform`, `shiftTerm_kl_range_le`,
  `kl_tail_block_bound`, `shiftTerm_tail_le`).

The identity `ζ(s,a) - ζ(s) = ∑_m ((m+a)^{-s} - (m+1)^{-s})` (`Work.BMF.HurwitzShift`) then gives
`‖ζ(s,a)‖ ≤ ‖ζ(s)‖ + ‖∑_m shiftTerm‖` and the result.  For `a = 0` one has `ζ(s,0) = ζ(s)`
(`HurwitzZeta.hurwitzZeta_zero`) and `0^{-σ} = 0`, and for `|t|` below the threshold that makes the
VK treatment of the shift series applicable, the crude telescoping bound
`‖∑_m shiftTerm‖ ≤ (‖s‖/σ) a^{-σ}` (`Work.BMF.norm_tsum_shiftTerm_tail_le`) suffices.
-/

namespace Work.BMF.VKChain

open scoped BigOperators

noncomputable section

/-- **The Riemann-zeta growth bound in the VK strip**, obtained from
`Work.BMF.N7.zeta_strip_bound_of_vk_aux` (the `N7` chain) and the exponential-sum input. -/
theorem zeta_growth_vk_abs {Cvk cvk : ℝ} (hVK : Work.BMF.VKExpInput Cvk cvk)
    (hcvk0 : 0 < cvk) (hcvk1 : cvk ≤ 1) (hCvk : 0 < Cvk) :
    ∃ A c : ℝ, 0 < A ∧ 0 < c ∧ c ≤ 1 / 4 ∧
      ∀ σ t : ℝ, 3 ≤ |t| →
        1 - c * Real.log (|t| + 3) ^ (-(6 / 7 : ℝ)) ≤ σ → σ ≤ 2 →
        ‖riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤
          A * Real.log (|t| + 3) ^ (6 / 7 : ℝ) := by
  have hV1 : Work.BMF.N7.VKExpSumRaw :=
    ⟨Cvk, cvk, hCvk, hcvk0, fun N t hN hNt hlog u hu hu1 R hNR hR2N =>
      hVK.2.2 N t hN hNt hlog u hu hu1 R hNR hR2N⟩
  obtain ⟨A, c, hA, hc, hreg⟩ :=
    Work.BMF.N7.zeta_strip_bound_of_vk_aux hV1
      (fun c₀ cζ h₀ hζ => Work.BMF.N7.dyadic_vk_sum_bound c₀ cζ h₀ hζ)
  refine ⟨A, min (1 / 4) c, hA, lt_min (by norm_num) hc, min_le_left _ _, ?_⟩
  intro σ t ht hσ hσ2
  refine hreg σ t ht ?_ hσ2
  have hLpos : 0 < Real.log (|t| + 3) := by
    have h6 : (6 : ℝ) ≤ |t| + 3 := by
      have := abs_nonneg t; linarith
    have h16 : (1 : ℝ) < Real.log 6 := by
      rw [Real.lt_log_iff_exp_lt (by norm_num)]
      exact lt_trans Real.exp_one_lt_three (by norm_num)
    exact lt_of_lt_of_le (lt_trans zero_lt_one h16) (Real.log_le_log (by norm_num) h6)
  have hLnn : 0 ≤ Real.log (|t| + 3) ^ (-(6 / 7 : ℝ)) := Real.rpow_nonneg hLpos.le _
  have hle : min (1 / 4) c ≤ c := min_le_right _ _
  nlinarith [hσ, hLnn, hle]

/-- **Reduction of the Hurwitz bound to the shift-difference series bound.** -/
private theorem hurwitz_of_shift_bound {Cvk cvk As : ℝ} (hVK : Work.BMF.VKExpInput Cvk cvk)
    (hcvk0 : 0 < cvk) (hcvk1 : cvk ≤ 1) (hCvk : 0 < Cvk) (hAs : 0 < As)
    (hshift : ∀ (a σ t : ℝ), 0 < a → a ≤ 1 → 3 ≤ |t| →
      Real.exp (1000 / cvk ^ 6) ≤ |t| →
      1 - (cvk / 4) * Real.log (|t| + 3) ^ (-(6 / 7 : ℝ)) ≤ σ → σ ≤ 2 →
      ‖∑' m : ℕ, Work.BMF.shiftTerm a m ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤
        As * (a ^ (-σ) + Real.log (|t| + 3) ^ (6 / 7 : ℝ))) :
    ∃ A c : ℝ, 0 < A ∧ 0 < c ∧ c ≤ 1 / 4 ∧
      ∀ (a σ t : ℝ), 0 ≤ a → a ≤ 1 → 3 ≤ |t| →
        1 - c * Real.log (|t| + 3) ^ (-(6 / 7 : ℝ)) ≤ σ → σ ≤ 2 →
        ‖HurwitzZeta.hurwitzZeta (a : UnitAddCircle) ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤
          A * (a ^ (-σ) + Real.log (|t| + 3) ^ (6 / 7 : ℝ)) := by
  obtain ⟨Aζ, cζ, hAζ, hcζpos, hcζ14, hζ⟩ := zeta_growth_vk_abs hVK hcvk0 hcvk1 hCvk
  have hCnn : 0 ≤ max As (1 + (4 / 3) * Real.exp (1000 / cvk ^ 6)) :=
    le_trans hAs.le (le_max_left _ _)
  have hAsC : As ≤ max As (1 + (4 / 3) * Real.exp (1000 / cvk ^ 6)) := le_max_left _ _
  have hBC : (1 + (4 / 3) * Real.exp (1000 / cvk ^ 6)) ≤
      max As (1 + (4 / 3) * Real.exp (1000 / cvk ^ 6)) := le_max_right _ _
  refine ⟨Aζ + max As (1 + (4 / 3) * Real.exp (1000 / cvk ^ 6)),
    min (1 / 4) (min cζ (cvk / 4)), by linarith, ?_, min_le_left _ _, ?_⟩
  · exact lt_min (by norm_num) (lt_min hcζpos (by positivity))
  · intro a σ t ha0 ha1 ht3 hσ hσ2
    have h6 : (6 : ℝ) ≤ |t| + 3 := by
      have := abs_nonneg t; linarith
    have hlog6 : (1 : ℝ) < Real.log 6 := by
      rw [Real.lt_log_iff_exp_lt (by norm_num)]
      exact lt_trans Real.exp_one_lt_three (by norm_num)
    have hLgt : 1 < Real.log (|t| + 3) :=
      lt_of_lt_of_le hlog6 (Real.log_le_log (by norm_num) h6)
    have hLpos : 0 < Real.log (|t| + 3) := lt_trans zero_lt_one hLgt
    have hL1 : 1 ≤ Real.log (|t| + 3) := le_of_lt hLgt
    have hL67nn : 0 ≤ Real.log (|t| + 3) ^ (6 / 7 : ℝ) := Real.rpow_nonneg hLpos.le _
    have hLpownn : 0 ≤ Real.log (|t| + 3) ^ (-(6 / 7 : ℝ)) := Real.rpow_nonneg hLpos.le _
    have hLpowle1 : Real.log (|t| + 3) ^ (-(6 / 7 : ℝ)) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos hL1 (by norm_num)
    have hccζ : min (1 / 4) (min cζ (cvk / 4)) ≤ cζ :=
      le_trans (min_le_right _ _) (min_le_left _ _)
    have hccvk : min (1 / 4) (min cζ (cvk / 4)) ≤ cvk / 4 :=
      le_trans (min_le_right _ _) (min_le_right _ _)
    have hσ34 : 3 / 4 ≤ σ := by
      have h1 : min (1 / 4) (min cζ (cvk / 4)) * Real.log (|t| + 3) ^ (-(6 / 7 : ℝ)) ≤ 1 / 4 := by
        calc min (1 / 4) (min cζ (cvk / 4)) * Real.log (|t| + 3) ^ (-(6 / 7 : ℝ))
            ≤ (1 / 4) * 1 :=
              mul_le_mul (min_le_left _ _) hLpowle1 hLpownn (by norm_num)
          _ = 1 / 4 := by norm_num
      linarith
    have hσ0 : 0 < σ := by linarith
    have hs0 : 0 < ((σ : ℂ) + (t : ℂ) * Complex.I).re := by simpa using hσ0
    have hs1 : ((σ : ℂ) + (t : ℂ) * Complex.I) ≠ 1 := by
      intro hc1
      have him : t = 0 := by simpa using congrArg Complex.im hc1
      have : |t| = 0 := by rw [him]; exact abs_zero
      linarith [ht3]
    have hzbd : ‖riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤
        Aζ * Real.log (|t| + 3) ^ (6 / 7 : ℝ) := by
      refine hζ σ t ht3 ?_ hσ2
      nlinarith [hσ, hLpownn, hccζ]
    rcases eq_or_lt_of_le ha0 with ha_eq | ha_pos
    · -- `a = 0`
      subst ha_eq
      have hz0 : HurwitzZeta.hurwitzZeta ((0 : ℝ) : UnitAddCircle)
          ((σ : ℂ) + (t : ℂ) * Complex.I) = riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I) := by
        rw [show ((0 : ℝ) : UnitAddCircle) = 0 from by simp, HurwitzZeta.hurwitzZeta_zero]
      rw [hz0]
      have h0r : (0 : ℝ) ^ (-σ) = 0 := Real.zero_rpow (by linarith : -σ ≠ 0)
      rw [h0r, zero_add]
      have : Aζ * Real.log (|t| + 3) ^ (6 / 7 : ℝ) ≤
          (Aζ + max As (1 + (4 / 3) * Real.exp (1000 / cvk ^ 6))) *
            Real.log (|t| + 3) ^ (6 / 7 : ℝ) :=
        mul_le_mul_of_nonneg_right (by linarith) hL67nn
      exact le_trans hzbd this
    · -- `0 < a`
      have hid := Work.BMF.hurwitzZeta_sub_riemannZeta_eq_tsum ha_pos ha1 hs0 hs1
      have hsplit : HurwitzZeta.hurwitzZeta (a : UnitAddCircle) ((σ : ℂ) + (t : ℂ) * Complex.I) =
          riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I) +
            ∑' m : ℕ, Work.BMF.shiftTerm a m ((σ : ℂ) + (t : ℂ) * Complex.I) := by
        have h := sub_eq_iff_eq_add'.mp hid
        exact h
      rw [hsplit]
      have hann : 0 ≤ a ^ (-σ) := Real.rpow_nonneg ha0 _
      have hsum_nn : 0 ≤ a ^ (-σ) + Real.log (|t| + 3) ^ (6 / 7 : ℝ) := by linarith
      have hζterm : Aζ * Real.log (|t| + 3) ^ (6 / 7 : ℝ) ≤
          Aζ * (a ^ (-σ) + Real.log (|t| + 3) ^ (6 / 7 : ℝ)) :=
        mul_le_mul_of_nonneg_left (by linarith) hAζ.le
      by_cases hgate : Real.exp (1000 / cvk ^ 6) ≤ |t|
      · have hreg : 1 - (cvk / 4) * Real.log (|t| + 3) ^ (-(6 / 7 : ℝ)) ≤ σ := by
          nlinarith [hσ, hLpownn, hccvk]
        have hsh := hshift a σ t ha_pos ha1 ht3 hgate hreg hσ2
        have hsh' : ‖∑' m : ℕ, Work.BMF.shiftTerm a m
              ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤
            max As (1 + (4 / 3) * Real.exp (1000 / cvk ^ 6)) *
              (a ^ (-σ) + Real.log (|t| + 3) ^ (6 / 7 : ℝ)) :=
          le_trans hsh (mul_le_mul_of_nonneg_right hAsC hsum_nn)
        calc ‖riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I) +
              ∑' m : ℕ, Work.BMF.shiftTerm a m ((σ : ℂ) + (t : ℂ) * Complex.I)‖
            ≤ ‖riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I)‖ +
              ‖∑' m : ℕ, Work.BMF.shiftTerm a m ((σ : ℂ) + (t : ℂ) * Complex.I)‖ :=
              norm_add_le _ _
          _ ≤ Aζ * (a ^ (-σ) + Real.log (|t| + 3) ^ (6 / 7 : ℝ)) +
              max As (1 + (4 / 3) * Real.exp (1000 / cvk ^ 6)) *
                (a ^ (-σ) + Real.log (|t| + 3) ^ (6 / 7 : ℝ)) :=
              add_le_add (le_trans hzbd hζterm) hsh'
          _ = (Aζ + max As (1 + (4 / 3) * Real.exp (1000 / cvk ^ 6))) *
                (a ^ (-σ) + Real.log (|t| + 3) ^ (6 / 7 : ℝ)) := by ring
      · -- small `|t|`: the crude telescoping bound
        have hgate' : |t| < Real.exp (1000 / cvk ^ 6) := not_le.mp hgate
        have htail := Work.BMF.norm_tsum_shiftTerm_tail_le ha_pos ha1 hs0 0
        have hsn : ‖((σ : ℂ) + (t : ℂ) * Complex.I)‖ / σ ≤
            1 + (4 / 3) * Real.exp (1000 / cvk ^ 6) := by
          have h1 : ‖((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤ σ + |t| := by
            calc ‖((σ : ℂ) + (t : ℂ) * Complex.I)‖
                ≤ |((σ : ℂ) + (t : ℂ) * Complex.I).re| +
                  |((σ : ℂ) + (t : ℂ) * Complex.I).im| :=
                  Complex.norm_le_abs_re_add_abs_im _
              _ = |σ| + |t| := by simp
              _ = σ + |t| := by rw [abs_of_pos hσ0]
          calc ‖((σ : ℂ) + (t : ℂ) * Complex.I)‖ / σ ≤ (σ + |t|) / σ :=
                div_le_div_of_nonneg_right h1 hσ0.le
            _ = 1 + |t| / σ := by field_simp
            _ ≤ 1 + (4 / 3) * Real.exp (1000 / cvk ^ 6) := by
                have h3 : |t| / σ ≤ (4 / 3) * |t| := by
                  rw [div_le_iff₀ hσ0]
                  nlinarith [hσ34, abs_nonneg t]
                have h4 : (4 / 3) * |t| < (4 / 3) * Real.exp (1000 / cvk ^ 6) := by linarith
                linarith
        have htail' : ‖∑' m : ℕ, Work.BMF.shiftTerm a m
              ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤
            max As (1 + (4 / 3) * Real.exp (1000 / cvk ^ 6)) *
              (a ^ (-σ) + Real.log (|t| + 3) ^ (6 / 7 : ℝ)) := by
          have htb : ‖∑' m : ℕ, Work.BMF.shiftTerm a m ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤
              (1 + (4 / 3) * Real.exp (1000 / cvk ^ 6)) * a ^ (-σ) := by
            have h0 : ‖∑' m : ℕ, Work.BMF.shiftTerm a m ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤
                (‖((σ : ℂ) + (t : ℂ) * Complex.I)‖ / σ) * a ^ (-σ) := by
              simpa using htail
            exact le_trans h0 (mul_le_mul_of_nonneg_right hsn (Real.rpow_nonneg ha0 _))
          have htc : (1 + (4 / 3) * Real.exp (1000 / cvk ^ 6)) * a ^ (-σ) ≤
              max As (1 + (4 / 3) * Real.exp (1000 / cvk ^ 6)) *
                (a ^ (-σ) + Real.log (|t| + 3) ^ (6 / 7 : ℝ)) := by
            calc (1 + (4 / 3) * Real.exp (1000 / cvk ^ 6)) * a ^ (-σ)
                ≤ max As (1 + (4 / 3) * Real.exp (1000 / cvk ^ 6)) * a ^ (-σ) :=
                  mul_le_mul_of_nonneg_right hBC hann
              _ ≤ max As (1 + (4 / 3) * Real.exp (1000 / cvk ^ 6)) *
                    (a ^ (-σ) + Real.log (|t| + 3) ^ (6 / 7 : ℝ)) :=
                  mul_le_mul_of_nonneg_left (by linarith) hCnn
          exact le_trans htb htc
        calc ‖riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I) +
              ∑' m : ℕ, Work.BMF.shiftTerm a m ((σ : ℂ) + (t : ℂ) * Complex.I)‖
            ≤ ‖riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I)‖ +
              ‖∑' m : ℕ, Work.BMF.shiftTerm a m ((σ : ℂ) + (t : ℂ) * Complex.I)‖ :=
              norm_add_le _ _
          _ ≤ Aζ * (a ^ (-σ) + Real.log (|t| + 3) ^ (6 / 7 : ℝ)) +
              max As (1 + (4 / 3) * Real.exp (1000 / cvk ^ 6)) *
                (a ^ (-σ) + Real.log (|t| + 3) ^ (6 / 7 : ℝ)) :=
              add_le_add (le_trans hzbd hζterm) htail'
          _ = (Aζ + max As (1 + (4 / 3) * Real.exp (1000 / cvk ^ 6))) *
                (a ^ (-σ) + Real.log (|t| + 3) ^ (6 / 7 : ℝ)) := by ring

/-- **The Hurwitz-zeta growth bound in the Vinogradov-Korobov strip**, from the VK exponential-sum input `Work.BMF.VKExpInput`. -/
theorem hurwitz_growth_abs_vk {Cvk cvk : ℝ} (hVK : Work.BMF.VKExpInput Cvk cvk) (hcvk0 : 0 < cvk)
    (hcvk1 : cvk ≤ 1) (hCvk : 0 < Cvk) :
    ∃ A c : ℝ, 0 < A ∧ 0 < c ∧ c ≤ 1 / 4 ∧
      ∀ (a σ t : ℝ), 0 ≤ a → a ≤ 1 → 3 ≤ |t| →
        1 - c * Real.log (|t| + 3) ^ (-(6 / 7 : ℝ)) ≤ σ → σ ≤ 2 →
        ‖HurwitzZeta.hurwitzZeta (a : UnitAddCircle) ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤
          A * (a ^ (-σ) + Real.log (|t| + 3) ^ (6 / 7 : ℝ)) := by
  obtain ⟨As, hAs, hshift⟩ :=
    Work.BMF.VKChain.shift_series_tsum_bound hVK hcvk0 hcvk1 hCvk
  exact hurwitz_of_shift_bound hVK hcvk0 hcvk1 hCvk hAs hshift

end

end Work.BMF.VKChain
