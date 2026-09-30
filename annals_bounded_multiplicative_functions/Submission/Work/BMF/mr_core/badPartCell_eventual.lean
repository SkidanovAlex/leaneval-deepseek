import Mathlib
import Submission.Work.BMF.mr_core_defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF.mr_core

open Filter
open scoped BigOperators

/-- Elementary eventual arithmetic for the coarse-cell bad-set bound.

Useful facts for the proof (`logPc Y = (log Y)^(47/48)`, `Pc Y = exp (logPc Y)`,
`Qc B Y = exp (Ac B * logPc Y)`; `H ≥ Y^θ ≥ 1` for `Y ≥ 1`):
* conjunct 1 is `Filter.eventually_ge_atTop`;
* conjunct 2: `j ∈ indexSet K (Pc Y) (Qc B Y)` gives
  `K * logPc Y - 1 < j` (`Nat.lt_floor_add_one`), so `j/K ≥ logPc Y - 1/K ≥ logPc Y / 2`
  once `logPc Y ≥ 2/K`, and `logPc Y = (log Y)^(47/48)`;
* conjunct 3, first part: `T ≤ (2C₀/ε)(Y/H) ≤ (2C₀/ε)Y`, so
  `log (2T) ≤ log (4C₀/ε) + log Y ≤ 2 log Y` eventually;
* conjunct 3, second part: `2*T*Qc B Y ≤ (4C₀/ε) * Y^(1-θ) * exp (Ac B * (log Y)^(47/48)) ≤ Y`
  since `Ac B * (log Y)^(47/48) - θ * log Y → -∞` (as `(log Y)^(1/48) → ∞`);
* conjunct 3, third part: `4*T ≤ (8C₀/ε) * Y` while
  `exp (((log Y)^(47/48)/4)^(21/20)) ≥ exp ((log Y)^(987/960) / 4^(21/20))`
  and `987/960 = 1.028... > 1`, so the exponential beats every fixed power of `Y`.

All three thresholds depend on `(ε, C₀, θ, B, K)` only, so `∀ᶠ Y in atTop` is legitimate. -/
theorem badPartCell_eventual (ε C₀ θ B K : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) (hC₀ : 0 < C₀)
    (hθ₀ : 0 < θ) (hθ₁ : θ < 1) (hB : 1000 / ε ≤ B) (hK : 4 ≤ K) :
    ∀ᶠ Y in Filter.atTop,
      (16 : ℝ) ^ 8 ≤ Y ∧
      (∀ j : ℕ, j ∈ Work.BMF.mrDirect.indexSet K (Work.BMF.mrCore.Pc Y) (Work.BMF.mrCore.Qc B Y) →
        (Real.log Y) ^ (47 / 48 : ℝ) ≤ 2 * ((j : ℝ) / K)) ∧
      (∀ H T : ℝ, Y ^ θ ≤ H → H ≤ Y → 3 ≤ T → T ≤ 2 * C₀ / ε * (Y / H) →
        Real.log (2 * T) ≤ 2 * Real.log Y ∧
        2 * T * Work.BMF.mrCore.Qc B Y ≤ Y ∧
        4 * T ≤ Real.exp (((Real.log Y) ^ (47 / 48 : ℝ) / 4) ^ (21 / 20 : ℝ))) := by
  have hθ2pos : (0 : ℝ) < θ / 2 := by linarith
  have hKpos : (0 : ℝ) < K := by linarith
  -- Basic divergence facts
  have hpow47 : Tendsto (fun Y : ℝ => (Real.log Y) ^ (47 / 48 : ℝ)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 47 / 48)).comp Real.tendsto_log_atTop
  have hpow1 : Tendsto (fun Y : ℝ => (Real.log Y) ^ (1 / 48 : ℝ)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 48)).comp Real.tendsto_log_atTop
  have hpow9 : Tendsto (fun Y : ℝ => (Real.log Y) ^ (9 / 320 : ℝ)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 9 / 320)).comp Real.tendsto_log_atTop
  -- Eventual pointwise conditions
  have eBase : ∀ᶠ Y : ℝ in atTop, (16 : ℝ) ^ 8 ≤ Y := Filter.eventually_ge_atTop _
  have eExp1 : ∀ᶠ Y : ℝ in atTop, Real.exp 1 ≤ Y := Filter.eventually_ge_atTop _
  have eKPc : ∀ᶠ Y : ℝ in atTop, 2 / K ≤ (Real.log Y) ^ (47 / 48 : ℝ) :=
    hpow47.eventually_ge_atTop (2 / K)
  have eAB : ∀ᶠ Y : ℝ in atTop,
      Work.BMF.mrCore.Ac B ≤ (θ / 2) * (Real.log Y) ^ (1 / 48 : ℝ) :=
    (Filter.Tendsto.const_mul_atTop hθ2pos hpow1).eventually_ge_atTop (Work.BMF.mrCore.Ac B)
  have eLog4 : ∀ᶠ Y : ℝ in atTop,
      Real.log (4 * C₀ / ε) ≤ (θ / 2) * Real.log Y :=
    (Filter.Tendsto.const_mul_atTop hθ2pos Real.tendsto_log_atTop).eventually_ge_atTop _
  have eLog8 : ∀ᶠ Y : ℝ in atTop, Real.log (8 * C₀ / ε) ≤ Real.log Y :=
    Real.tendsto_log_atTop.eventually_ge_atTop _
  have ePow9 : ∀ᶠ Y : ℝ in atTop, 2 * 4 ^ (21 / 20 : ℝ) ≤ (Real.log Y) ^ (9 / 320 : ℝ) :=
    hpow9.eventually_ge_atTop _
  refine (eBase.and (eExp1.and (eKPc.and (eAB.and (eLog4.and (eLog8.and ePow9)))))).mono ?_
  intro Y hY
  obtain ⟨hY8, hYe, hKPcY, hABY, hLog4Y, hLog8Y, hPow9Y⟩ := hY
  have hY1 : (1 : ℝ) ≤ Y := le_trans (Real.one_le_exp (show (0 : ℝ) ≤ 1 by norm_num)) hYe
  have hYpos : (0 : ℝ) < Y := lt_of_lt_of_le Real.zero_lt_one hY1
  have hL1 : (1 : ℝ) ≤ Real.log Y := (Real.le_log_iff_exp_le hYpos).mpr hYe
  have hLpos : (0 : ℝ) < Real.log Y := lt_of_lt_of_le Real.zero_lt_one hL1
  have hLnonneg : (0 : ℝ) ≤ Real.log Y := le_of_lt hLpos
  have hYθ1 : (1 : ℝ) ≤ Y ^ θ := Real.one_le_rpow hY1 (le_of_lt hθ₀)
  have hYθpos : (0 : ℝ) < Y ^ θ := Real.rpow_pos_of_pos hYpos θ
  have hYpow_le : Y ^ (1 - θ) ≤ Y := by
    have := Real.rpow_le_rpow_of_exponent_le hY1 (show (1 : ℝ) - θ ≤ 1 by linarith)
    rwa [Real.rpow_one] at this
  have hmulYθ : Y ^ θ * Y ^ (1 - θ) = Y := by
    rw [← Real.rpow_add hYpos]
    rw [show θ + (1 - θ) = 1 by ring, Real.rpow_one]
  refine ⟨hY8, ?_, ?_⟩
  · -- conjunct 2
    intro j hj
    rw [Work.BMF.mrDirect.indexSet, Finset.mem_Icc] at hj
    have hjge : ⌊K * Real.log (Work.BMF.mrCore.Pc Y)⌋₊ ≤ j := hj.1
    have hlogPc : Real.log (Work.BMF.mrCore.Pc Y) = Work.BMF.mrCore.logPc Y := by
      rw [Work.BMF.mrCore.Pc, Real.log_exp]
    have hcast : ((⌊K * Real.log (Work.BMF.mrCore.Pc Y)⌋₊ : ℕ) : ℝ) ≤ (j : ℝ) := by
      exact_mod_cast hjge
    have h1' : K * Real.log (Work.BMF.mrCore.Pc Y) - 1 < (j : ℝ) := by
      have hfl := Nat.lt_floor_add_one (K * Real.log (Work.BMF.mrCore.Pc Y))
      linarith
    have h1 : K * Work.BMF.mrCore.logPc Y - 1 < (j : ℝ) := by
      rw [hlogPc] at h1'
      exact h1'
    have h2 : Work.BMF.mrCore.logPc Y - 1 / K < (j : ℝ) / K := by
      rw [lt_div_iff₀ hKpos]
      have heq : (Work.BMF.mrCore.logPc Y - 1 / K) * K = K * Work.BMF.mrCore.logPc Y - 1 := by
        field_simp
      rw [heq]; exact h1
    have h3 : 1 / K ≤ Work.BMF.mrCore.logPc Y / 2 := by
      have h2' : 2 ≤ K * Work.BMF.mrCore.logPc Y := by
        have h := mul_le_mul_of_nonneg_right hKPcY (le_of_lt hKpos)
        rw [div_mul_cancel₀ 2 (ne_of_gt hKpos), mul_comm] at h
        exact h
      rw [div_le_iff₀ hKpos,
        show (Work.BMF.mrCore.logPc Y / 2) * K = (K * Work.BMF.mrCore.logPc Y) / 2 by ring,
        le_div_iff₀ (show (0 : ℝ) < 2 by norm_num)]
      linarith
    have h4 : Work.BMF.mrCore.logPc Y / 2 ≤ (j : ℝ) / K := by linarith
    have h5 : Work.BMF.mrCore.logPc Y ≤ 2 * ((j : ℝ) / K) := by linarith
    simpa only [Work.BMF.mrCore.logPc] using h5
  · -- conjunct 3
    intro H T hHθ hHY hT3 hTle
    have hHpos : (0 : ℝ) < H := lt_of_lt_of_le hYθpos hHθ
    have hYH_le : Y / H ≤ Y ^ (1 - θ) := by
      rw [div_le_iff₀ hHpos]
      have hstep : Y ^ (1 - θ) * Y ^ θ ≤ Y ^ (1 - θ) * H :=
        mul_le_mul_of_nonneg_left hHθ (Real.rpow_nonneg (le_of_lt hYpos) _)
      have hmul : Y ^ (1 - θ) * Y ^ θ = Y := by
        rw [← Real.rpow_add hYpos]
        rw [show (1 : ℝ) - θ + θ = 1 by ring, Real.rpow_one]
      linarith
    have hTle' : T ≤ 2 * C₀ / ε * Y ^ (1 - θ) := by
      have hc2 : (0 : ℝ) < 2 * C₀ / ε := by positivity
      calc T ≤ 2 * C₀ / ε * (Y / H) := hTle
        _ ≤ 2 * C₀ / ε * Y ^ (1 - θ) := mul_le_mul_of_nonneg_left hYH_le (le_of_lt hc2)
    have h4C0 : (0 : ℝ) ≤ 4 * C₀ / ε := by positivity
    have h8C0 : (0 : ℝ) ≤ 8 * C₀ / ε := by positivity
    -- part 1
    have hp1 : Real.log (2 * T) ≤ 2 * Real.log Y := by
      have hTpos : (0 : ℝ) < T := by linarith
      have h2Tpos : (0 : ℝ) < 2 * T := by linarith
      have h2T_le : 2 * T ≤ (4 * C₀ / ε) * Y := by
        calc 2 * T ≤ 2 * (2 * C₀ / ε * Y ^ (1 - θ)) := by linarith [hTle']
          _ = (4 * C₀ / ε) * Y ^ (1 - θ) := by ring
          _ ≤ (4 * C₀ / ε) * Y := mul_le_mul_of_nonneg_left hYpow_le h4C0
      have hlog2T : Real.log (2 * T) ≤ Real.log ((4 * C₀ / ε) * Y) := Real.log_le_log h2Tpos h2T_le
      have hlogmul : Real.log ((4 * C₀ / ε) * Y) = Real.log (4 * C₀ / ε) + Real.log Y :=
        Real.log_mul (ne_of_gt (by positivity : (0 : ℝ) < 4 * C₀ / ε)) (ne_of_gt hYpos)
      rw [hlogmul] at hlog2T
      have hb : (θ / 2) * Real.log Y + Real.log Y ≤ 2 * Real.log Y := by
        nlinarith [hLnonneg, hθ₁]
      linarith
    -- part 2
    have hAcpos : (0 : ℝ) < Work.BMF.mrCore.Ac B := by
      rw [Work.BMF.mrCore.Ac]; exact Real.exp_pos _
    have hQc : Work.BMF.mrCore.Qc B Y
        = Real.exp (Work.BMF.mrCore.Ac B * (Real.log Y) ^ (47 / 48 : ℝ)) := by
      rw [Work.BMF.mrCore.Qc, Work.BMF.mrCore.logQc, Work.BMF.mrCore.logPc]
    have hstep : Work.BMF.mrCore.Ac B * (Real.log Y) ^ (47 / 48 : ℝ) ≤ (θ / 2) * Real.log Y := by
      have hL47nn : (0 : ℝ) ≤ (Real.log Y) ^ (47 / 48 : ℝ) := Real.rpow_nonneg hLnonneg _
      have h := mul_le_mul_of_nonneg_right hABY hL47nn
      have hrhs : ((θ / 2) * (Real.log Y) ^ (1 / 48 : ℝ)) * (Real.log Y) ^ (47 / 48 : ℝ)
          = (θ / 2) * Real.log Y := by
        rw [mul_assoc, ← Real.rpow_add hLpos]
        rw [show (1 : ℝ) / 48 + 47 / 48 = 1 by norm_num, Real.rpow_one]
      linarith [h, hrhs]
    have hA_le : (4 * C₀ / ε) * Real.exp (Work.BMF.mrCore.Ac B * (Real.log Y) ^ (47 / 48 : ℝ))
        ≤ Y ^ θ := by
      have hposA : (0 : ℝ) < (4 * C₀ / ε)
          * Real.exp (Work.BMF.mrCore.Ac B * (Real.log Y) ^ (47 / 48 : ℝ)) := by positivity
      refine (Real.log_le_log_iff hposA hYθpos).mp ?_
      rw [Real.log_mul (ne_of_gt (by positivity : (0 : ℝ) < 4 * C₀ / ε)) (Real.exp_ne_zero _),
        Real.log_exp, Real.log_rpow hYpos θ]
      linarith [hLog4Y, hstep]
    have hp2 : 2 * T * Work.BMF.mrCore.Qc B Y ≤ Y := by
      have hY1θnn : (0 : ℝ) ≤ Y ^ (1 - θ) := Real.rpow_nonneg (le_of_lt hYpos) _
      have hkey : (4 * C₀ / ε) * Y ^ (1 - θ)
          * Real.exp (Work.BMF.mrCore.Ac B * (Real.log Y) ^ (47 / 48 : ℝ)) ≤ Y := by
        calc (4 * C₀ / ε) * Y ^ (1 - θ)
              * Real.exp (Work.BMF.mrCore.Ac B * (Real.log Y) ^ (47 / 48 : ℝ))
            = ((4 * C₀ / ε) * Real.exp (Work.BMF.mrCore.Ac B * (Real.log Y) ^ (47 / 48 : ℝ)))
                * Y ^ (1 - θ) := by ring
          _ ≤ Y ^ θ * Y ^ (1 - θ) := mul_le_mul_of_nonneg_right hA_le hY1θnn
          _ = Y := hmulYθ
      have hb : 2 * T * Real.exp (Work.BMF.mrCore.Ac B * (Real.log Y) ^ (47 / 48 : ℝ))
          ≤ 2 * (2 * C₀ / ε * Y ^ (1 - θ))
              * Real.exp (Work.BMF.mrCore.Ac B * (Real.log Y) ^ (47 / 48 : ℝ)) := by
        have hlt : 2 * T ≤ 2 * (2 * C₀ / ε * Y ^ (1 - θ)) := by linarith [hTle']
        exact mul_le_mul_of_nonneg_right hlt (le_of_lt (Real.exp_pos _))
      calc 2 * T * Work.BMF.mrCore.Qc B Y
          = 2 * T * Real.exp (Work.BMF.mrCore.Ac B * (Real.log Y) ^ (47 / 48 : ℝ)) := by rw [hQc]
        _ ≤ 2 * (2 * C₀ / ε * Y ^ (1 - θ))
              * Real.exp (Work.BMF.mrCore.Ac B * (Real.log Y) ^ (47 / 48 : ℝ)) := hb
        _ = (4 * C₀ / ε) * Y ^ (1 - θ)
              * Real.exp (Work.BMF.mrCore.Ac B * (Real.log Y) ^ (47 / 48 : ℝ)) := by ring
        _ ≤ Y := hkey
    -- part 3
    have hp3 : 4 * T ≤ Real.exp (((Real.log Y) ^ (47 / 48 : ℝ) / 4) ^ (21 / 20 : ℝ)) := by
      have hE_eq : (((Real.log Y) ^ (47 / 48 : ℝ) / 4) ^ (21 / 20 : ℝ))
          = (Real.log Y) ^ (329 / 320 : ℝ) / 4 ^ (21 / 20 : ℝ) := by
        rw [Real.div_rpow (Real.rpow_nonneg hLnonneg _) (by norm_num : (0 : ℝ) ≤ 4),
          ← Real.rpow_mul hLnonneg,
          show (47 : ℝ) / 48 * (21 / 20) = 329 / 320 by norm_num]
      have h2L_le_E : 2 * Real.log Y ≤ (Real.log Y) ^ (329 / 320 : ℝ) / 4 ^ (21 / 20 : ℝ) := by
        have h4powpos : (0 : ℝ) < 4 ^ (21 / 20 : ℝ) := Real.rpow_pos_of_pos (by norm_num) _
        have hdivnn : (0 : ℝ) ≤ Real.log Y / 4 ^ (21 / 20 : ℝ) := by positivity
        have h := mul_le_mul_of_nonneg_right hPow9Y hdivnn
        have hLHS : (2 * 4 ^ (21 / 20 : ℝ)) * (Real.log Y / 4 ^ (21 / 20 : ℝ)) = 2 * Real.log Y := by
          field_simp
        have hRHS : (Real.log Y) ^ (9 / 320 : ℝ) * (Real.log Y / 4 ^ (21 / 20 : ℝ))
            = (Real.log Y) ^ (329 / 320 : ℝ) / 4 ^ (21 / 20 : ℝ) := by
          have hpow : (Real.log Y) ^ (9 / 320 : ℝ) * Real.log Y = (Real.log Y) ^ (329 / 320 : ℝ) := by
            rw [show (329 : ℝ) / 320 = 9 / 320 + 1 by norm_num, Real.rpow_add hLpos, Real.rpow_one]
          rw [← mul_div_assoc, hpow]
        rw [← hLHS, ← hRHS]
        exact h
      have hlog8Y : Real.log ((8 * C₀ / ε) * Y) = Real.log (8 * C₀ / ε) + Real.log Y :=
        Real.log_mul (ne_of_gt (by positivity : (0 : ℝ) < 8 * C₀ / ε)) (ne_of_gt hYpos)
      have hlog8Y_le : Real.log ((8 * C₀ / ε) * Y)
          ≤ (Real.log Y) ^ (329 / 320 : ℝ) / 4 ^ (21 / 20 : ℝ) := by
        rw [hlog8Y]; linarith
      have hexp_ge : (8 * C₀ / ε) * Y
          ≤ Real.exp ((Real.log Y) ^ (329 / 320 : ℝ) / 4 ^ (21 / 20 : ℝ)) :=
        (Real.log_le_iff_le_exp (by positivity : (0 : ℝ) < (8 * C₀ / ε) * Y)).mp hlog8Y_le
      have h4T_le : 4 * T ≤ (8 * C₀ / ε) * Y := by
        calc 4 * T ≤ 4 * (2 * C₀ / ε * Y ^ (1 - θ)) := by linarith [hTle']
          _ = (8 * C₀ / ε) * Y ^ (1 - θ) := by ring
          _ ≤ (8 * C₀ / ε) * Y := mul_le_mul_of_nonneg_left hYpow_le h8C0
      calc 4 * T ≤ (8 * C₀ / ε) * Y := h4T_le
        _ ≤ Real.exp ((Real.log Y) ^ (329 / 320 : ℝ) / 4 ^ (21 / 20 : ℝ)) := hexp_ge
        _ = Real.exp (((Real.log Y) ^ (47 / 48 : ℝ) / 4) ^ (21 / 20 : ℝ)) := by rw [hE_eq]
    exact ⟨hp1, hp2, hp3⟩

end Work.BMF.mr_core
