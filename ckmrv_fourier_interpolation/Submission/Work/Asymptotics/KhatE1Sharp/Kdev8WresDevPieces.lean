import Mathlib
import Submission.Work.Asymptotics.KhatE1Sharp.Kdev8WresZAtoms
import Submission.Work.Asymptotics.KhatE1Sharp.Kdev8WresAssembly
import Submission.Work.Asymptotics.KPlus8FunnelAux
import Submission.Work.Asymptotics.Funnel24Aux

/-!
# First pieces of the deviation bound `WresDevBound`

`WresDev` (see `KhatE1Core.Kdev8WresAssembly`) is the sum

  `(kdevA2JF - 2u²Δ(τ)KdevE2)·ShDev + KdevA2Dev·ShDeltaZtr + KdevSig2Dev`

of three aggregates.  This file proves the elementary bounds for the three "deviation factors"
that appear in them, with thresholds:

* `‖ShDev τ z‖ = O(‖q(τ)‖‖q(z)‖³)`,
* `‖ShDeltaZtr τ z‖ = O(‖q(τ)‖)`,
* `‖KdevSig2Dev ℓ τ z‖ = O((scale τ)^N‖q(τ)‖‖q(z)‖⁴(1+‖z‖)²)`.

The inputs are the proved truncation deviations (`exists_dE4z_bound`, `exists_dDz_bound`), the
uniform funnel bounds `‖Δ(τ)‖ ≤ 2‖q(τ)‖` and `‖E₄(τ)³‖ ≤ 27/8`, and the atom bounds
`funnel_phi2_bound`, `funnel_E14_bound`.
-/

namespace Work.Asymptotics.KhatE1Core

open UpperHalfPlane

noncomputable section

open Work.Kernels

private lemma norm_sum3 (a b c : ℂ) : ‖a + b + c‖ ≤ ‖a‖ + ‖b‖ + ‖c‖ := by
  have h1 := norm_add_le (a + b) c
  have h2 := norm_add_le a b
  linarith

private lemma norm_dsub3 (a b c : ℂ) : ‖a - b + c‖ ≤ ‖a‖ + ‖b‖ + ‖c‖ := by
  have h1 := norm_add_le (a - b) c
  have h2 := norm_sub_le a b
  linarith

private lemma norm_Ept_le_one {z : ℍ} (hz : 1 ≤ z.im) : ‖Work.Residues.Ept z‖ ≤ 1 := by
  rw [Work.Residues.norm_Ept, Real.exp_le_one_iff]
  nlinarith [Real.pi_pos, hz]

private lemma norm_E4Ztr_le {z : ℍ} (hz : 1 ≤ z.im) :
    ‖Work.Asymptotics.KhatE1.E4Ztr z‖ ≤ 2401 := by
  have hu := norm_Ept_le_one hz
  have hu0 : (0 : ℝ) ≤ ‖Work.Residues.Ept z‖ := norm_nonneg _
  have h2 : ‖(Work.Residues.Ept z) ^ 2‖ ≤ 1 := by
    rw [norm_pow]; exact pow_le_one₀ hu0 hu
  have h4 : ‖(Work.Residues.Ept z) ^ 4‖ ≤ 1 := by
    rw [norm_pow]; exact pow_le_one₀ hu0 hu
  rw [Work.Asymptotics.KhatE1.E4Ztr_eq_Ept z]
  refine le_trans (norm_sum3 _ _ _) ?_
  have h1 : ‖(240 : ℂ) * (Work.Residues.Ept z) ^ 2‖
      = 240 * ‖(Work.Residues.Ept z) ^ 2‖ := by rw [norm_mul]; norm_num
  have h3 : ‖(2160 : ℂ) * (Work.Residues.Ept z) ^ 4‖
      = 2160 * ‖(Work.Residues.Ept z) ^ 4‖ := by rw [norm_mul]; norm_num
  rw [norm_one, h1, h3]
  linarith

private lemma norm_DeltaZtr_le {z : ℍ} (hz : 1 ≤ z.im) :
    ‖Work.Asymptotics.KhatE1.DeltaZtr z‖
      ≤ 277 * ‖Work.Kernels.qParamFun z‖ := by
  have hu := norm_Ept_le_one hz
  have hu0 : (0 : ℝ) ≤ ‖Work.Residues.Ept z‖ := norm_nonneg _
  have hq : ‖Work.Kernels.qParamFun z‖ = ‖Work.Residues.Ept z‖ ^ 2 := by
    rw [Work.Asymptotics.Small.qParamFun_eq_Ept_sq z, norm_pow]
  have hq0 : (0 : ℝ) ≤ ‖Work.Kernels.qParamFun z‖ := norm_nonneg _
  have hqs : ‖Work.Kernels.qParamFun z‖ ≤ 1 := by rw [hq]; nlinarith
  have e2 : ‖(Work.Residues.Ept z) ^ 2‖ = ‖Work.Kernels.qParamFun z‖ := by rw [norm_pow, hq]
  have e4 : ‖(Work.Residues.Ept z) ^ 4‖ = ‖Work.Kernels.qParamFun z‖ ^ 2 := by
    rw [norm_pow, hq]; ring
  have e6 : ‖(Work.Residues.Ept z) ^ 6‖ = ‖Work.Kernels.qParamFun z‖ ^ 3 := by
    rw [norm_pow, hq]; ring
  rw [Work.Asymptotics.KhatE1.DeltaZtr_eq_Ept z]
  refine le_trans (norm_dsub3 _ _ _) ?_
  have h1 : ‖(24 : ℂ) * (Work.Residues.Ept z) ^ 4‖
      = 24 * ‖(Work.Residues.Ept z) ^ 4‖ := by rw [norm_mul]; norm_num
  have h3 : ‖(252 : ℂ) * (Work.Residues.Ept z) ^ 6‖
      = 252 * ‖(Work.Residues.Ept z) ^ 6‖ := by rw [norm_mul]; norm_num
  rw [e2, h1, e4, h3, e6]
  nlinarith [hq0, hqs]

private lemma norm_Delta_le (τ : ℍ) (hτ : Work.Asymptotics.Funnel τ) :
    ‖DeltaFun τ‖ ≤ 2 * ‖Work.Kernels.qParamFun τ‖ :=
  Work.Asymptotics.DeltaFun_funnel_le τ hτ

private lemma qz_le_qt {τ z : ℍ} (h : τ.im + 1 ≤ z.im) :
    ‖Work.Kernels.qParamFun z‖ ≤ ‖Work.Kernels.qParamFun τ‖ := by
  rw [Work.Asymptotics.norm_qParamFun, Work.Asymptotics.norm_qParamFun]
  exact Real.exp_le_exp.mpr (by nlinarith [Real.pi_pos, h])

/-- **`‖ShDev τ z‖ = O(‖q(τ)‖‖q(z)‖³)`.** -/
theorem ShDev_bound :
    ∃ T C : ℝ, 1 ≤ T ∧ 0 < C ∧ ∀ (τ z : ℍ), Work.Asymptotics.Funnel τ → T ≤ z.im →
      τ.im + 1 ≤ z.im →
      ‖Work.Asymptotics.KhatE1.ShDev τ z‖
        ≤ C * ‖Work.Kernels.qParamFun τ‖ * ‖Work.Kernels.qParamFun z‖ ^ 3 := by
  obtain ⟨T4, C4, hT4, hC4, hb4⟩ := Work.Asymptotics.KhatE1.exists_dE4z_bound
  obtain ⟨Td, Cd, hTd, hCd, hbd⟩ := Work.Asymptotics.KhatE1.exists_dDz_bound
  refine ⟨max T4 Td, 2 * (3 * 2401 ^ 2 * C4 + 3 * 2401 * C4 ^ 2 + C4 ^ 3)
      + Cd * (27 / 8), le_trans hT4 (le_max_left _ _), by positivity, fun τ z hτ hz hzt => ?_⟩
  have hT4' : T4 ≤ z.im := le_trans (le_max_left T4 Td) hz
  have hTd' : Td ≤ z.im := le_trans (le_max_right T4 Td) hz
  have hd4 := hb4 z hT4'
  have hdd := hbd z hTd'
  have hD := norm_Delta_le τ hτ
  have hE4 := norm_E4Ztr_le (by linarith : (1 : ℝ) ≤ z.im)
  have hE43 := Work.Asymptotics.E4cube_funnel_le τ hτ
  have hz0 : (0 : ℝ) ≤ ‖Work.Kernels.qParamFun z‖ := norm_nonneg _
  have hzq : ‖Work.Kernels.qParamFun z‖ ≤ ‖Work.Kernels.qParamFun τ‖ := qz_le_qt hzt
  have hqt0 : (0 : ℝ) ≤ ‖Work.Kernels.qParamFun τ‖ := norm_nonneg _
  have hz1' : ‖Work.Kernels.qParamFun z‖ ≤ 1 := by
    have h2 : (2 : ℝ) ≤ τ.im := hτ.2
    refine le_trans hzq ?_
    rw [Work.Asymptotics.norm_qParamFun, Real.exp_le_one_iff]
    nlinarith [Real.pi_pos, h2]
  have hq3 : ‖Work.Kernels.qParamFun z‖ ^ 3 ≤ ‖Work.Kernels.qParamFun τ‖ ^ 3 :=
    pow_le_pow_left₀ hz0 hzq 3
  rw [Work.Asymptotics.KhatE1.ShDev]
  have hfirst :
      ‖DeltaFun τ * (3 * (Work.Asymptotics.KhatE1.E4Ztr z) ^ 2 * Work.Asymptotics.KhatE1.dE4z z
          + 3 * Work.Asymptotics.KhatE1.E4Ztr z * (Work.Asymptotics.KhatE1.dE4z z) ^ 2
          + (Work.Asymptotics.KhatE1.dE4z z) ^ 3)‖
        ≤ 2 * ‖Work.Kernels.qParamFun τ‖
            * ((3 * 2401 ^ 2 * C4 + 3 * 2401 * C4 ^ 2 + C4 ^ 3)
                * ‖Work.Kernels.qParamFun z‖ ^ 3) := by
    rw [norm_mul]
    refine mul_le_mul hD ?_ (norm_nonneg _) (by positivity)
    set x : ℝ := ‖Work.Kernels.qParamFun z‖ ^ 3 with hxdef
    have hx0 : (0 : ℝ) ≤ x := by rw [hxdef]; positivity
    have hxle : x ≤ 1 := by rw [hxdef]; exact pow_le_one₀ hz0 hz1'
    have hx2 : x ^ 2 ≤ x := by
      calc x ^ 2 = x * x := by ring
        _ ≤ 1 * x := mul_le_mul_of_nonneg_right hxle hx0
        _ = x := by ring
    have hx3' : x ^ 3 ≤ x := by
      calc x ^ 3 = x * x ^ 2 := by ring
        _ ≤ x * x := mul_le_mul_of_nonneg_left hx2 hx0
        _ ≤ x * 1 := mul_le_mul_of_nonneg_left hxle hx0
        _ = x := by ring
    have hsum :
        ‖3 * (Work.Asymptotics.KhatE1.E4Ztr z) ^ 2 * Work.Asymptotics.KhatE1.dE4z z
          + 3 * Work.Asymptotics.KhatE1.E4Ztr z * (Work.Asymptotics.KhatE1.dE4z z) ^ 2
          + (Work.Asymptotics.KhatE1.dE4z z) ^ 3‖
        ≤ (3 * 2401 ^ 2 * C4 + 3 * 2401 * C4 ^ 2 + C4 ^ 3) * x := by
      refine le_trans (norm_sum3 _ _ _) ?_
      have h1 := norm_add_le
        ((3 : ℂ) * (Work.Asymptotics.KhatE1.E4Ztr z) ^ 2 * Work.Asymptotics.KhatE1.dE4z z)
        ((3 : ℂ) * Work.Asymptotics.KhatE1.E4Ztr z * (Work.Asymptotics.KhatE1.dE4z z) ^ 2)
      have hA : ‖(3 : ℂ) * (Work.Asymptotics.KhatE1.E4Ztr z) ^ 2
            * Work.Asymptotics.KhatE1.dE4z z‖ ≤ 3 * 2401 ^ 2 * C4 * x := by
        rw [norm_mul, norm_mul, norm_pow, show ‖(3 : ℂ)‖ = 3 by norm_num, hxdef]
        have h1' : ‖Work.Asymptotics.KhatE1.E4Ztr z‖ ^ 2 ≤ 2401 ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) hE4 2
        have h2'' : ‖Work.Asymptotics.KhatE1.dE4z z‖
            ≤ C4 * ‖Work.Kernels.qParamFun z‖ ^ 3 := hd4
        have ha : (0 : ℝ) ≤ ‖Work.Asymptotics.KhatE1.E4Ztr z‖ := norm_nonneg _
        have hb : (0 : ℝ) ≤ ‖Work.Asymptotics.KhatE1.dE4z z‖ := norm_nonneg _
        have hc : (0 : ℝ) ≤ ‖Work.Kernels.qParamFun z‖ ^ 3 := by positivity
        have hstep : ‖Work.Asymptotics.KhatE1.E4Ztr z‖ ^ 2
              * ‖Work.Asymptotics.KhatE1.dE4z z‖
            ≤ 2401 ^ 2 * (C4 * ‖Work.Kernels.qParamFun z‖ ^ 3) :=
          mul_le_mul h1' h2'' (norm_nonneg _) (by positivity)
        nlinarith [hstep, ha, hb, hc, hC4, norm_nonneg (Work.Kernels.qParamFun z)]
      have hB : ‖(3 : ℂ) * Work.Asymptotics.KhatE1.E4Ztr z
            * (Work.Asymptotics.KhatE1.dE4z z) ^ 2‖ ≤ 3 * 2401 * C4 ^ 2 * x := by
        rw [norm_mul, norm_mul, norm_pow, show ‖(3 : ℂ)‖ = 3 by norm_num, hxdef]
        have h2' : ‖Work.Asymptotics.KhatE1.dE4z z‖ ^ 2
            ≤ (C4 * ‖Work.Kernels.qParamFun z‖ ^ 3) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) hd4 2
        have ha : (0 : ℝ) ≤ ‖Work.Asymptotics.KhatE1.E4Ztr z‖ := norm_nonneg _
        have hstep : ‖Work.Asymptotics.KhatE1.E4Ztr z‖
              * ‖Work.Asymptotics.KhatE1.dE4z z‖ ^ 2
            ≤ 2401 * (C4 * ‖Work.Kernels.qParamFun z‖ ^ 3) ^ 2 :=
          mul_le_mul hE4 h2' (by positivity) (by positivity)
        have hpow : (C4 * ‖Work.Kernels.qParamFun z‖ ^ 3) ^ 2
            ≤ C4 ^ 2 * ‖Work.Kernels.qParamFun z‖ ^ 3 := by
          nlinarith [hx2, hxdef, hC4]
        nlinarith [hstep, hpow, ha, hx0, hC4, norm_nonneg (Work.Asymptotics.KhatE1.dE4z z)]
      have hC : ‖(Work.Asymptotics.KhatE1.dE4z z) ^ 3‖ ≤ C4 ^ 3 * x := by
        rw [norm_pow, hxdef]
        have h3' := pow_le_pow_left₀ (norm_nonneg (Work.Asymptotics.KhatE1.dE4z z)) hd4 3
        have hpow : (C4 * ‖Work.Kernels.qParamFun z‖ ^ 3) ^ 3
            ≤ C4 ^ 3 * ‖Work.Kernels.qParamFun z‖ ^ 3 := by
          rw [show (C4 * ‖Work.Kernels.qParamFun z‖ ^ 3) ^ 3
              = C4 ^ 3 * (‖Work.Kernels.qParamFun z‖ ^ 3) ^ 3 by ring]
          exact mul_le_mul_of_nonneg_left hx3' (by positivity)
        linarith [h3', hpow]
      linarith [h1, hA, hB, hC]
    simpa only [hxdef] using hsum
  have hsecond :
      ‖Work.Asymptotics.KhatE1.dDz z * (Work.Kernels.E4Fun τ) ^ 3‖
        ≤ Cd * ‖Work.Kernels.qParamFun z‖ ^ 4 * (27 / 8) := by
    rw [norm_mul]
    exact mul_le_mul hdd hE43 (norm_nonneg _) (by positivity)
  calc ‖DeltaFun τ * (3 * (Work.Asymptotics.KhatE1.E4Ztr z) ^ 2
          * Work.Asymptotics.KhatE1.dE4z z
        + 3 * Work.Asymptotics.KhatE1.E4Ztr z * (Work.Asymptotics.KhatE1.dE4z z) ^ 2
        + (Work.Asymptotics.KhatE1.dE4z z) ^ 3)
      - Work.Asymptotics.KhatE1.dDz z * (Work.Kernels.E4Fun τ) ^ 3‖
      ≤ _ + _ := norm_sub_le _ _
    _ ≤ 2 * ‖Work.Kernels.qParamFun τ‖
            * ((3 * 2401 ^ 2 * C4 + 3 * 2401 * C4 ^ 2 + C4 ^ 3)
                * ‖Work.Kernels.qParamFun z‖ ^ 3)
          + Cd * ‖Work.Kernels.qParamFun z‖ ^ 4 * (27 / 8) := add_le_add hfirst hsecond
    _ ≤ (2 * (3 * 2401 ^ 2 * C4 + 3 * 2401 * C4 ^ 2 + C4 ^ 3) + Cd * (27 / 8))
          * ‖Work.Kernels.qParamFun τ‖ * ‖Work.Kernels.qParamFun z‖ ^ 3 := by
        have hq4 : ‖Work.Kernels.qParamFun z‖ ^ 4
            ≤ ‖Work.Kernels.qParamFun z‖ ^ 3 * ‖Work.Kernels.qParamFun τ‖ := by
          calc ‖Work.Kernels.qParamFun z‖ ^ 4
              = ‖Work.Kernels.qParamFun z‖ ^ 3 * ‖Work.Kernels.qParamFun z‖ := by ring
            _ ≤ ‖Work.Kernels.qParamFun z‖ ^ 3 * ‖Work.Kernels.qParamFun τ‖ :=
                mul_le_mul_of_nonneg_left hzq (by positivity)
        nlinarith [hz0, hz1', hq4, hqt0, hCd, hC4]

/-- **`‖ShDeltaZtr τ z‖ = O(‖q(τ)‖)`.** -/
theorem ShDeltaZtr_bound :
    ∃ T C : ℝ, 1 ≤ T ∧ 0 < C ∧ ∀ (τ z : ℍ), Work.Asymptotics.Funnel τ → T ≤ z.im →
      τ.im + 1 ≤ z.im →
      ‖Work.Asymptotics.KhatE1.ShDeltaZtr τ z‖
        ≤ C * ‖Work.Kernels.qParamFun τ‖ := by
  refine ⟨1, 2 * 2401 ^ 3 + 277 * (27 / 8), le_refl 1, by norm_num, fun τ z hτ hz hzt => ?_⟩
  have hD := norm_Delta_le τ hτ
  have hE4 := norm_E4Ztr_le hz
  have hE43 := Work.Asymptotics.E4cube_funnel_le τ hτ
  have hDz := norm_DeltaZtr_le hz
  have hzq := qz_le_qt hzt
  have hqt0 : (0 : ℝ) ≤ ‖Work.Kernels.qParamFun τ‖ := norm_nonneg _
  rw [Work.Asymptotics.KhatE1.ShDeltaZtr]
  calc ‖DeltaFun τ * (Work.Asymptotics.KhatE1.E4Ztr z) ^ 3
        - Work.Asymptotics.KhatE1.DeltaZtr z * (Work.Kernels.E4Fun τ) ^ 3‖
      ≤ ‖DeltaFun τ * (Work.Asymptotics.KhatE1.E4Ztr z) ^ 3‖
        + ‖Work.Asymptotics.KhatE1.DeltaZtr z * (Work.Kernels.E4Fun τ) ^ 3‖ := norm_sub_le _ _
    _ ≤ 2 * ‖Work.Kernels.qParamFun τ‖ * 2401 ^ 3
        + 277 * ‖Work.Kernels.qParamFun z‖ * (27 / 8) := by
        rw [norm_mul, norm_mul]
        have h3 : ‖(Work.Asymptotics.KhatE1.E4Ztr z) ^ 3‖ ≤ 2401 ^ 3 := by
          rw [norm_pow]
          exact pow_le_pow_left₀ (norm_nonneg _) hE4 3
        exact add_le_add (mul_le_mul hD h3 (norm_nonneg _) (by positivity))
          (mul_le_mul hDz hE43 (norm_nonneg _) (by positivity))
    _ ≤ (2 * 2401 ^ 3 + 277 * (27 / 8)) * ‖Work.Kernels.qParamFun τ‖ := by
        nlinarith [hzq, hqt0]

/-- **`‖KdevSig2Dev ℓ τ z‖ = O((scale τ)^N‖q(τ)‖‖q(z)‖⁴(1+‖z‖)²)`.** -/
theorem KdevSig2Dev_bound (ℓ : Work.Kernels.LogLambdaData) :
    ∃ T C N : ℝ, 1 ≤ T ∧ 0 < C ∧ 0 ≤ N ∧ ∀ (τ z : ℍ), Work.Asymptotics.Funnel τ →
      T ≤ z.im →
      ‖Work.Asymptotics.KhatE1.KdevSig2Dev ℓ τ z‖
        ≤ C * (Work.Kernels.scale τ) ^ N * ‖Work.Kernels.qParamFun τ‖
            * ‖Work.Kernels.qParamFun z‖ ^ 4 * (1 + ‖(z : ℂ)‖) ^ 2 := by
  obtain ⟨C2, hC2, h2⟩ := Work.Asymptotics.funnel_phi2_bound
  obtain ⟨C14, hC14, h14⟩ := Work.Asymptotics.funnel_E14_bound
  obtain ⟨Td, Cd, hTd, hCd, hbd⟩ := Work.Asymptotics.KhatE1.exists_dDz_bound
  refine ⟨max Td 1, ‖(Work.Asymptotics.Compact.tailC⁻¹)‖ * 2 * C2 * C14 * Cd + 1, 1,
    le_max_right _ _, by positivity, by norm_num, fun τ z hτ hz => ?_⟩
  have hTd' : Td ≤ z.im := le_trans (le_max_left Td 1) hz
  have hz1 : (1 : ℝ) ≤ z.im := le_trans (le_max_right Td 1) hz
  have hdd := hbd z hTd'
  have hD := norm_Delta_le τ hτ
  have hp2 := h2 τ hτ
  have hE14 := h14 τ hτ
  have hs1 : (1 : ℝ) ≤ Work.Kernels.scale τ := Work.Kernels.one_le_scale τ
  have hzs : ‖(z : ℂ)‖ ^ 2 ≤ (1 + ‖(z : ℂ)‖) ^ 2 := by
    have h0 : (0 : ℝ) ≤ ‖(z : ℂ)‖ := norm_nonneg _
    nlinarith
  have hzle1 : ‖Work.Kernels.qParamFun z‖ ≤ 1 := by
    rw [Work.Asymptotics.norm_qParamFun, Real.exp_le_one_iff]
    nlinarith [Real.pi_pos, hz1]
  have hq4 : ‖Work.Kernels.qParamFun z‖ ^ 4 ≤ 1 :=
    pow_le_one₀ (norm_nonneg (Work.Kernels.qParamFun z)) hzle1
  have hMs : (Work.Kernels.scale τ) ^ (1 : ℝ) = Work.Kernels.scale τ := Real.rpow_one _
  have hmid : ‖DeltaFun τ * (Work.Kernels.phi2 τ * Work.Kernels.E14Fun τ
        * (z : ℂ) ^ 2 * Work.Asymptotics.KhatE1.dDz z)‖
      ≤ 2 * ‖Work.Kernels.qParamFun τ‖ * ((((C2 * Work.Kernels.scale τ) * C14)
          * ‖(z : ℂ)‖ ^ 2) * (Cd * ‖Work.Kernels.qParamFun z‖ ^ 4)) := by
    refine le_trans (norm_mul _ _).le ?_
    refine mul_le_mul hD ?_ (norm_nonneg _) (by positivity)
    refine le_trans (norm_mul _ _).le ?_
    refine mul_le_mul ?_ hdd (norm_nonneg _) (by positivity)
    refine le_trans (norm_mul _ _).le ?_
    refine mul_le_mul ?_ (le_of_eq (norm_pow (z : ℂ) 2)) (norm_nonneg _) (by positivity)
    refine le_trans (norm_mul _ _).le ?_
    exact mul_le_mul hp2 hE14 (norm_nonneg _) (by positivity)
  rw [hMs, Work.Asymptotics.KhatE1.KdevSig2Dev]
  have hq : ‖(-(Work.Asymptotics.Compact.tailC⁻¹)) * (DeltaFun τ * (Work.Kernels.phi2 τ
        * Work.Kernels.E14Fun τ * (z : ℂ) ^ 2 * Work.Asymptotics.KhatE1.dDz z))‖
      = ‖(Work.Asymptotics.Compact.tailC⁻¹)‖ * ‖DeltaFun τ * (Work.Kernels.phi2 τ
        * Work.Kernels.E14Fun τ * (z : ℂ) ^ 2 * Work.Asymptotics.KhatE1.dDz z)‖ := by
    rw [norm_mul, norm_neg]
  rw [hq]
  refine le_trans (mul_le_mul_of_nonneg_left hmid (norm_nonneg _)) ?_
  have hle1 : ‖(z : ℂ)‖ ^ 2 * (Cd * ‖Work.Kernels.qParamFun z‖ ^ 4)
      ≤ (1 + ‖(z : ℂ)‖) ^ 2 * (Cd * ‖Work.Kernels.qParamFun z‖ ^ 4) :=
    mul_le_mul hzs le_rfl (by positivity) (by positivity)
  have hstep1 : ((((C2 * Work.Kernels.scale τ) * C14) * ‖(z : ℂ)‖ ^ 2)
        * (Cd * ‖Work.Kernels.qParamFun z‖ ^ 4))
      ≤ ((((C2 * Work.Kernels.scale τ) * C14) * (1 + ‖(z : ℂ)‖) ^ 2)
        * (Cd * ‖Work.Kernels.qParamFun z‖ ^ 4)) := by
    calc (((C2 * Work.Kernels.scale τ) * C14) * ‖(z : ℂ)‖ ^ 2)
          * (Cd * ‖Work.Kernels.qParamFun z‖ ^ 4)
        = ((C2 * Work.Kernels.scale τ) * C14)
          * (‖(z : ℂ)‖ ^ 2 * (Cd * ‖Work.Kernels.qParamFun z‖ ^ 4)) := by ring
      _ ≤ ((C2 * Work.Kernels.scale τ) * C14)
          * ((1 + ‖(z : ℂ)‖) ^ 2 * (Cd * ‖Work.Kernels.qParamFun z‖ ^ 4)) :=
          mul_le_mul_of_nonneg_left hle1 (by positivity)
      _ = (((C2 * Work.Kernels.scale τ) * C14) * (1 + ‖(z : ℂ)‖) ^ 2)
          * (Cd * ‖Work.Kernels.qParamFun z‖ ^ 4) := by ring
  calc ‖(Work.Asymptotics.Compact.tailC⁻¹)‖
        * (2 * ‖Work.Kernels.qParamFun τ‖ * ((((C2 * Work.Kernels.scale τ) * C14)
            * ‖(z : ℂ)‖ ^ 2) * (Cd * ‖Work.Kernels.qParamFun z‖ ^ 4)))
      ≤ ‖(Work.Asymptotics.Compact.tailC⁻¹)‖
        * (2 * ‖Work.Kernels.qParamFun τ‖ * ((((C2 * Work.Kernels.scale τ) * C14)
            * (1 + ‖(z : ℂ)‖) ^ 2) * (Cd * ‖Work.Kernels.qParamFun z‖ ^ 4))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hstep1 (by positivity))
          (norm_nonneg _)
    _ = (‖(Work.Asymptotics.Compact.tailC⁻¹)‖ * 2 * C2 * C14 * Cd)
        * ((Work.Kernels.scale τ * ‖Work.Kernels.qParamFun τ‖
            * ‖Work.Kernels.qParamFun z‖ ^ 4) * (1 + ‖(z : ℂ)‖) ^ 2) := by ring
    _ ≤ (‖(Work.Asymptotics.Compact.tailC⁻¹)‖ * 2 * C2 * C14 * Cd + 1)
        * ((Work.Kernels.scale τ * ‖Work.Kernels.qParamFun τ‖
            * ‖Work.Kernels.qParamFun z‖ ^ 4) * (1 + ‖(z : ℂ)‖) ^ 2) := by
        have hB : (0 : ℝ) ≤ (Work.Kernels.scale τ * ‖Work.Kernels.qParamFun τ‖
            * ‖Work.Kernels.qParamFun z‖ ^ 4) * (1 + ‖(z : ℂ)‖) ^ 2 := by positivity
        have hA : (0 : ℝ) ≤ ‖(Work.Asymptotics.Compact.tailC⁻¹)‖ * 2 * C2 * C14 * Cd := by
          positivity
        nlinarith [hB, hA]
    _ = (‖(Work.Asymptotics.Compact.tailC⁻¹)‖ * 2 * C2 * C14 * Cd + 1)
        * Work.Kernels.scale τ * ‖Work.Kernels.qParamFun τ‖ * ‖Work.Kernels.qParamFun z‖ ^ 4
        * (1 + ‖(z : ℂ)‖) ^ 2 := by ring

end

end Work.Asymptotics.KhatE1Core
