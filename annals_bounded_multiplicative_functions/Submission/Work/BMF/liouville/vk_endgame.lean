import Mathlib
import Submission.Work.BMF.VKExpSum.weyl_small_lambda
import Submission.Work.BMF.liouville.vk_lambda_large_assembly
import Submission.Work.BMF.zeta_growth_defs
import Submission.Work.BMF.zeta_partial_sum_bound
import Submission.Work.BMF.zeta_approx_functional_eq
import Submission.Work.BMF.zeta_offline_bound
import Submission.Work.BMF.zeta_bdd_height
import Submission.Work.BMF.zeta_vk_region_of_growth
import Submission.Work.BMF.liouville.zeta_tw_vk_sum_region

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Endgame wiring for `Work.BMF.liouville.recip_twist_re_upper`

This file supplies the `χ = 1` Vinogradov–Korobov prime-sum estimate needed by
`Work.BMF.liouville.recip_twist_re_upper`, *without* routing through the stub
`Submission/Work/BMF/vk_exp_sum_ford.lean`: instead it uses the (sorry-free) two-regime
development of the VK exponential-sum estimate in `Submission/Work/BMF/VKExpSum/`:

* `Work.BMF.VKExpSum.weyl_small_lambda` — Weyl's method, `1 ≤ λ ≤ 13/5`, *proved*;
* `Work.BMF.liouville.vk_lambda_large_assembly` — Ford's §5 extraction, `λ ≥ 13/5`, whose inputs
  (`vkford_lemma51`, `vkford_incomplete_crude`, `vkford_Wproduct_self`, `vkford_H_lower2`,
  `Work.BMF.liouville.main_sharp`) are all `sorry`-free.

The remaining ingredient `ford51_lambda_large` is the only unproved statement in the closure;
once it lands, this file (and hence `recip_twist_re_upper`) is complete.

Chain: `VKExpSum C D` (two regimes) → Richert growth bound `Work.BMF.zeta_growth_strip_vkexp`
(the proof of `Work.BMF.zeta_growth_strip`, verbatim, with the exponential-sum input from the two
regimes) → ζ VK zero-free region + log-derivative bound
(`Work.BMF.zeta_vk_region_of_growth`) → twisted principal Perron
(`zeta_tw_vk_sum_of_region`) → the `χ = 1` twisted prime number theorem.
-/

namespace Work.BMF.liouville

open Complex
open scoped Real

noncomputable section

/-- **The Vinogradov–Korobov exponential-sum estimate**, from the two `λ`-regimes
`λ ≤ 13/5` (`Work.BMF.VKExpSum.weyl_small_lambda`) and `λ ≥ 13/5`
(`Work.BMF.VKExpSum.ford51_lambda_large`). -/
theorem vkExpSum_regimes : ∃ C D : ℝ, 0 < C ∧ 0 < D ∧ Work.BMF.VKExpSum C D := by
  obtain ⟨C₁, D₁, hC₁, hD₁, h₁⟩ := Work.BMF.VKExpSum.weyl_small_lambda
  obtain ⟨C₂, D₂, hC₂, hD₂, h₂⟩ := vk_lambda_large_assembly
  refine ⟨max C₁ C₂, max D₁ D₂, lt_max_of_lt_left hC₁, lt_max_of_lt_left hD₁, ?_⟩
  intro N t hN hNt u hu0 hu1 R hR hR2
  have hN1 : (1 : ℝ) ≤ N := by linarith
  have hNpos : 0 < N := by linarith
  have hlogNpos : 0 < Real.log N := Real.log_pos (by linarith)
  have ht0 : 0 < t := by linarith
  have hlogtpos : 0 < Real.log t := Real.log_pos (by linarith)
  have hlamp : 0 < Real.log t / Real.log N := div_pos hlogtpos hlogNpos
  have hlam2 : 0 < (Real.log t / Real.log N) ^ 2 := pow_pos hlamp 2
  have hD1le : D₁ ≤ max D₁ D₂ := le_max_left _ _
  have hD2le : D₂ ≤ max D₁ D₂ := le_max_right _ _
  have hexp_le : ∀ a b : ℝ, 0 < a → a ≤ b →
      1 - 1 / (a * (Real.log t / Real.log N) ^ 2)
        ≤ 1 - 1 / (b * (Real.log t / Real.log N) ^ 2) := by
    intro a b ha hab
    have h1 : a * (Real.log t / Real.log N) ^ 2 ≤ b * (Real.log t / Real.log N) ^ 2 :=
      mul_le_mul_of_nonneg_right hab hlam2.le
    have h2 : 0 < a * (Real.log t / Real.log N) ^ 2 := mul_pos ha hlam2
    have h3 : 0 < b * (Real.log t / Real.log N) ^ 2 :=
      lt_of_lt_of_le h2 h1
    have h4 : 1 / (b * (Real.log t / Real.log N) ^ 2)
        ≤ 1 / (a * (Real.log t / Real.log N) ^ 2) :=
      one_div_le_one_div_of_le h2 h1
    linarith
  rcases le_total (Real.log t) ((13 / 5 : ℝ) * Real.log N) with hcase | hcase
  · -- bounded `λ`
    have h := h₁ N t u R hN hNt hcase hu0 hu1 hR hR2
    have hmono : 1 - 1 / (D₁ * (Real.log t / Real.log N) ^ 2)
        ≤ 1 - 1 / (max D₁ D₂ * (Real.log t / Real.log N) ^ 2) :=
      hexp_le D₁ (max D₁ D₂) hD₁ hD1le
    calc ‖Work.BMF.Ssum N u t R‖
        ≤ C₁ * N ^ (1 - 1 / (D₁ * (Real.log t / Real.log N) ^ 2)) := h
      _ ≤ max C₁ C₂ * N ^ (1 - 1 / (max D₁ D₂ * (Real.log t / Real.log N) ^ 2)) := by
          refine mul_le_mul (le_max_left _ _)
            (Real.rpow_le_rpow_of_exponent_le hN1 hmono) (Real.rpow_nonneg (by linarith) _)
            (le_trans hC₁.le (le_max_left _ _))
  · -- large `λ`
    have hcase' : (13 / 5 : ℝ) * Real.log N ≤ Real.log t := hcase
    have h := h₂ N t u R hN hNt hcase' hu0 hu1 hR hR2
    have hmono : 1 - 1 / (D₂ * (Real.log t / Real.log N) ^ 2)
        ≤ 1 - 1 / (max D₁ D₂ * (Real.log t / Real.log N) ^ 2) :=
      hexp_le D₂ (max D₁ D₂) hD₂ hD2le
    calc ‖Work.BMF.Ssum N u t R‖
        ≤ C₂ * N ^ (1 - 1 / (D₂ * (Real.log t / Real.log N) ^ 2)) := h
      _ ≤ max C₁ C₂ * N ^ (1 - 1 / (max D₁ D₂ * (Real.log t / Real.log N) ^ 2)) := by
          refine mul_le_mul (le_max_right _ _)
            (Real.rpow_le_rpow_of_exponent_le hN1 hmono) (Real.rpow_nonneg (by linarith) _)
            (le_trans hC₂.le (le_max_right _ _))

/-- `1 ≤ x^z` for `1 ≤ x` and `0 ≤ z`. -/
private lemma one_le_rpow_alt {x z : ℝ} (hx : 1 ≤ x) (hz : 0 ≤ z) : (1:ℝ) ≤ x ^ z := by
  calc (1:ℝ) = (1:ℝ) ^ z := (Real.one_rpow z).symm
    _ ≤ x ^ z := Real.rpow_le_rpow zero_le_one hx hz

/-- **Richert's growth bound for `ζ` in the strip `1/2 ≤ σ < 1`** — the statement of
`Work.BMF.zeta_growth_strip`, with the Vinogradov–Korobov exponential-sum input taken from
`vkExpSum_regimes` (hence from the two-regime development) rather than from the stub
`Submission/Work/BMF/vk_exp_sum_ford.lean`. -/
theorem zeta_growth_strip_vkexp :
    ∃ A B : ℝ, 0 < A ∧ 0 < B ∧
      (∀ σ t : ℝ, 1 / 2 ≤ σ → σ < 1 → 3 ≤ |t| →
        ‖riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤
          A * (|t| + 3) ^ (B * (1 - σ) ^ (3 / 2 : ℝ)) *
            (Real.log (|t| + 3)) ^ (2 / 3 : ℝ)) := by
  obtain ⟨C, D, hC, hD, hVK'⟩ := vkExpSum_regimes
  have hVK : Work.BMF.VKExpSum C D := hVK'
  obtain ⟨Aps, hAps, hPS⟩ := Work.BMF.zeta_partial_sum_bound C D hC hD hVK
  obtain ⟨C₁, T₀, hC₁, hT₀, hAFE⟩ := Work.BMF.zeta_approx_functional_eq
  obtain ⟨Aoff, hAoff, hOFF⟩ := Work.BMF.zeta_offline_bound
  obtain ⟨Abd, hAbd, hBD⟩ := Work.BMF.zeta_bdd_height (max T₀ 1) (le_max_right _ _)
  set B : ℝ := max 4 ((2 / 9) * Real.sqrt (3 * D)) with hBdef
  set S : ℝ := Aoff + Aps + C₁ + Abd + 1 with hSdef
  have hBpos : 0 < B := lt_of_lt_of_le (by norm_num : (0:ℝ) < 4) (le_max_left _ _)
  have hB4 : (4 : ℝ) ≤ B := le_max_left _ _
  have hB0 : (2 / 9) * Real.sqrt (3 * D) ≤ B := le_max_right _ _
  have hSnn : 0 ≤ S := by rw [hSdef]; linarith [hAoff.le, hAps.le, hC₁.le, hAbd.le]
  refine ⟨S, B, by rw [hSdef]; linarith [hAoff.le, hAps.le, hC₁.le, hAbd.le], hBpos, ?_⟩
  intro σ t hσlo hσ1 ht
  rw [mul_assoc]
  set X : ℝ := |t| ^ ((2 / 9) * Real.sqrt (3 * D) * (1 - σ) ^ (3 / 2 : ℝ)) with hXdef
  set Y : ℝ := (Real.log |t|) ^ (2 / 3 : ℝ) with hYdef
  set P : ℝ := (|t| + 3) ^ (B * (1 - σ) ^ (3 / 2 : ℝ)) with hPdef
  set Q : ℝ := (Real.log (|t| + 3)) ^ (2 / 3 : ℝ) with hQdef
  have hσle : σ ≤ 1 := le_of_lt hσ1
  have h1σnn : 0 ≤ 1 - σ := by linarith
  have hx3 : (1:ℝ) ≤ |t| + 3 := by linarith [abs_nonneg t, ht]
  have ht1 : (1:ℝ) ≤ |t| := by linarith
  have hpowA_nn : 0 ≤ B * (1 - σ) ^ (3 / 2 : ℝ) :=
    mul_nonneg hBpos.le (Real.rpow_nonneg h1σnn _)
  have hlog6 : (1:ℝ) < Real.log (|t| + 3) := by
    have h63 : (6:ℝ) ≤ |t| + 3 := by linarith [ht]
    have h16 : (1:ℝ) < Real.log 6 := by
      have := Real.log_lt_log (Real.exp_pos 1)
        (lt_trans Real.exp_one_lt_three (by norm_num : (3:ℝ) < 6))
      rwa [Real.log_exp] at this
    exact lt_of_lt_of_le h16 (Real.log_le_log (by norm_num) h63)
  have hP1 : (1:ℝ) ≤ P := by rw [hPdef]; exact one_le_rpow_alt hx3 hpowA_nn
  have hP0 : (0:ℝ) ≤ P := le_trans zero_le_one hP1
  have hQ1 : (1:ℝ) ≤ Q := by rw [hQdef]; exact one_le_rpow_alt hlog6.le (by norm_num)
  have hQ0 : (0:ℝ) ≤ Q := le_trans zero_le_one hQ1
  have hPQ1 : (1:ℝ) ≤ P * Q := one_le_mul_of_one_le_of_one_le hP1 hQ1
  have hPQ0 : (0:ℝ) ≤ P * Q := le_trans zero_le_one hPQ1
  show ‖riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤ S * (P * Q)
  by_cases hσ : σ ≤ 15 / 16
  · have h := hOFF σ t hσlo hσle ht (Or.inl hσ)
    have h4 : |t| ^ (4 * (1 - σ) ^ (3 / 2 : ℝ)) ≤ P := by
      rw [hPdef]
      calc |t| ^ (4 * (1 - σ) ^ (3 / 2 : ℝ))
          ≤ |t| ^ (B * (1 - σ) ^ (3 / 2 : ℝ)) :=
            Real.rpow_le_rpow_of_exponent_le ht1
              (mul_le_mul_of_nonneg_right hB4 (Real.rpow_nonneg h1σnn _))
        _ ≤ (|t| + 3) ^ (B * (1 - σ) ^ (3 / 2 : ℝ)) :=
            Real.rpow_le_rpow (abs_nonneg t) (by linarith [abs_nonneg t]) hpowA_nn
    refine le_trans h ?_
    calc Aoff * |t| ^ (4 * (1 - σ) ^ (3 / 2 : ℝ)) ≤ Aoff * P :=
          mul_le_mul_of_nonneg_left h4 hAoff.le
      _ ≤ S * P := by
          rw [hSdef]; exact mul_le_mul_of_nonneg_right (by linarith [hAps.le, hC₁.le, hAbd.le]) hP0
      _ ≤ S * (P * Q) := mul_le_mul_of_nonneg_left (by nlinarith [hP1, hQ1]) hSnn
  · have hσ' : 15 / 16 < σ := lt_of_not_ge hσ
    by_cases hbig : T₀ ≤ |t|
    · have hafe := hAFE σ t (le_of_lt hσ') hσle hbig
      have hps := hPS σ t hσlo hσ1 ht
      have hlogt : Real.log |t| ≤ Real.log (|t| + 3) :=
        Real.log_le_log (by linarith [ht]) (by linarith [abs_nonneg t])
      have hlogt0 : 0 ≤ Real.log |t| := Real.log_nonneg ht1
      have hXY : X * Y ≤ P * Q := by
        rw [hXdef, hYdef, hPdef, hQdef]
        exact mul_le_mul
          (calc |t| ^ ((2 / 9) * Real.sqrt (3 * D) * (1 - σ) ^ (3 / 2 : ℝ))
              ≤ |t| ^ (B * (1 - σ) ^ (3 / 2 : ℝ)) :=
                Real.rpow_le_rpow_of_exponent_le ht1
                  (mul_le_mul_of_nonneg_right hB0 (Real.rpow_nonneg h1σnn _))
            _ ≤ (|t| + 3) ^ (B * (1 - σ) ^ (3 / 2 : ℝ)) :=
                Real.rpow_le_rpow (abs_nonneg t) (by linarith [abs_nonneg t]) hpowA_nn)
          (Real.rpow_le_rpow hlogt0 hlogt (by norm_num))
          (Real.rpow_nonneg hlogt0 _) (le_trans zero_le_one hP1)
      have hps' : ‖∑ n ∈ Finset.Icc 1 ⌊|t|⌋₊, ((n : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * Complex.I)))‖
          ≤ Aps * (X * Y) := by
        rw [hXdef, hYdef]
        simpa only [mul_assoc] using hps
      have htri : ‖riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤ C₁ + Aps * (X * Y) := by
        calc ‖riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I)‖
            = ‖(riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I)
                - ∑ n ∈ Finset.Icc 1 ⌊|t|⌋₊, ((n : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * Complex.I))))
                + ∑ n ∈ Finset.Icc 1 ⌊|t|⌋₊, ((n : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * Complex.I)))‖ := by
              ring_nf
          _ ≤ ‖riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I)
                - ∑ n ∈ Finset.Icc 1 ⌊|t|⌋₊, ((n : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * Complex.I)))‖
                + ‖∑ n ∈ Finset.Icc 1 ⌊|t|⌋₊, ((n : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * Complex.I)))‖ :=
              norm_add_le _ _
          _ ≤ C₁ + Aps * (X * Y) := add_le_add hafe hps'
      have hAX : Aps * (X * Y) ≤ Aps * (P * Q) := mul_le_mul_of_nonneg_left hXY hAps.le
      have hfin : C₁ + Aps * (X * Y) ≤ S * (P * Q) := by
        have h6 : C₁ ≤ C₁ * (P * Q) := by
          simpa using mul_le_mul_of_nonneg_left hPQ1 hC₁.le
        have h3 : C₁ + Aps * (X * Y) ≤ (C₁ + Aps) * (P * Q) := by
          calc C₁ + Aps * (X * Y) ≤ C₁ * (P * Q) + Aps * (P * Q) := by linarith [h6, hAX]
            _ = (C₁ + Aps) * (P * Q) := by ring
        have h7 : (C₁ + Aps) * (P * Q) ≤ S * (P * Q) := by
          rw [hSdef]; exact mul_le_mul_of_nonneg_right (by linarith [hAoff.le, hAbd.le]) hPQ0
        linarith
      exact le_trans htri hfin
    · have hbig' : |t| < T₀ := lt_of_not_ge hbig
      have hbd := hBD σ t hσlo hσle ht (le_trans hbig'.le (le_max_left _ _))
      have e : Abd ≤ Abd * (P * Q) := by
        simpa using mul_le_mul_of_nonneg_left hPQ1 hAbd.le
      exact le_trans hbd (le_trans e (by
        rw [hSdef]
        exact mul_le_mul_of_nonneg_right (by linarith [hAoff.le, hAps.le, hC₁.le]) hPQ0))

/-- **The `χ = 1` Vinogradov–Korobov prime-sum estimate** (the statement of
`Work.BMF.liouville.vk_chi_one`), obtained from the two-regime exponential-sum development and
the twisted principal Perron formula. -/
theorem vk_chi_one_endgame :
    ∃ c C : ℝ, 0 < c ∧
      ∀ x : ℝ, 3 ≤ x → ∀ u : ℝ, |u| ≤ Real.exp ((Real.log x) ^ (5 / 4 : ℝ)) →
        ‖(∑ n ∈ Finset.Icc 1 ⌊x⌋₊, ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) *
            (n : ℂ) ^ (-(Complex.I * u))) -
          (x : ℂ) ^ (1 - Complex.I * u) / (1 - Complex.I * u)‖ ≤
          C * x * Real.exp (-c * (Real.log x) ^ (1 / 10 : ℝ)) := by
  obtain ⟨A, B, hA, hB, hgr⟩ := zeta_growth_strip_vkexp
  obtain ⟨hreg, hlog⟩ := Work.BMF.zeta_vk_region_of_growth ⟨A, B, hA, hB, hgr⟩
  obtain ⟨c, C, hc, _hC, h⟩ := zeta_tw_vk_sum_of_region hreg hlog
  refine ⟨c, C, hc, ?_⟩
  intro x hx u hu
  have h' := h x hx u hu
  simpa only [zetaTwSum, neg_mul] using h'

end

end Work.BMF.liouville
