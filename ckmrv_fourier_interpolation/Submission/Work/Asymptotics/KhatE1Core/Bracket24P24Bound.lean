import Mathlib
import Submission.Work.Asymptotics.KhatE1Core.BigCalc
import Submission.Work.Asymptotics.KhatE1.E1combo8FirstOrderBound
import Submission.Work.Asymptotics.KhatE1.E1combo24_first_order
import Submission.Work.Asymptotics.KhatE1.E1combo8_bound
import Submission.Work.Asymptotics.KhatE1.E1combo24_bound
import Submission.Work.Asymptotics.Funnel24Aux
import Submission.Work.Asymptotics.KPlusXiDefs
import Submission.Work.Residues.E4FunSecondOrder

namespace Work.Asymptotics.KhatE1Core

open UpperHalfPlane

noncomputable section

/-!
# `P24 = 15·E₄(τ)²·E1combo8 + 25·E1combo24 - 14745600·Δ` is `O(‖q(τ)‖² (scale τ)^N)`

`P24` is the "second-order `τ`-atom combination" of the `d = 24` funnel analysis
(`KhatE1.P24 = 15 E₄²·E1combo8 + 25·E1combo24 - 14745600·Δ`; up to the constant `205/8` it is
`E1combo24 + Am24`, by the proved `P24_eq`).  The `q⁰`- and `q¹`-parts cancel exactly:
with `Λ = πiτ + cuspC ℓ`,

  `E1combo8 = (737280 Λ + 122880) q + O(q² scale^N)`  (`E1combo8FirstOrderBound`),
  `E1combo24 = (516096 - 442368 Λ) q + O(q² scale^N)`  (`E1combo24_first_order`),
  `E₄² - 1 = O(q)`  (`E4FunSecondOrder`),  `Δ - q = O(q² scale^N)`  (`DeltaFun_two_term`),

and the numerical identities `15·737280 = 11059200 = 25·442368` and
`15·122880 + 25·516096 = 14745600` kill the `Λ`- and constant terms, so `P24 = O(q² scale^N)`.
-/

private lemma big_q1 : Big 1 (fun τ : ℍ => Work.Kernels.qParamFun τ) :=
  ⟨1, 0, one_pos, le_rfl, fun τ _ => by simp [Real.rpow_zero]⟩

/-- The second-order `τ`-atom combination `P24 = 15 E₄²·E1combo8 + 25·E1combo24 - 14745600·Δ`. -/
noncomputable def P24F (ℓ : Work.Kernels.LogLambdaData) (τ : ℍ) : ℂ :=
  15 * (Work.Kernels.E4Fun τ) ^ 2 * Work.Asymptotics.E1combo8 ℓ τ
    + 25 * Work.Asymptotics.E1combo24 ℓ τ
    - 14745600 * Work.Kernels.DeltaFun τ

/-- **`P24` is `Big 2`.** -/
theorem P24F_big (ℓ : Work.Kernels.LogLambdaData) : Big 2 (P24F ℓ) := by
  obtain ⟨C8, N8, hC8, hN8, h8⟩ := Work.Asymptotics.KhatE1.E1combo8FirstOrderBound ℓ
  obtain ⟨C24, N24, hC24, hN24, h24⟩ := Work.Asymptotics.KhatE1.E1combo24_first_order ℓ
  obtain ⟨CE4, hCE4, hE4⟩ := Work.Residues.E4FunSecondOrder
  obtain ⟨CD, hCD, hD⟩ := Work.Asymptotics.DeltaFun_two_term
  obtain ⟨Cb, Nb, hCb, hNb, hb⟩ := Work.Asymptotics.KhatE1.E1combo8_bound ℓ
  have h8' : Big 2 (fun τ : ℍ => Work.Asymptotics.E1combo8 ℓ τ
      - (737280 * ((Real.pi : ℂ) * Complex.I * (τ : ℂ)
          + Work.Asymptotics.Compact.cuspC ℓ) + 122880) * Work.Kernels.qParamFun τ) :=
    ⟨C8, N8, hC8, hN8, h8⟩
  have h24' : Big 2 (fun τ : ℍ => Work.Asymptotics.E1combo24 ℓ τ
      - (516096 - 442368 * ((Real.pi : ℂ) * Complex.I * (τ : ℂ)
          + Work.Asymptotics.Compact.cuspC ℓ)) * Work.Kernels.qParamFun τ) :=
    ⟨C24, N24, hC24, hN24, h24⟩
  have hD' : Big 2 (fun τ : ℍ => Work.Kernels.DeltaFun τ - Work.Kernels.qParamFun τ) :=
    ⟨CD, 0, hCD, le_rfl, fun τ hτ => by
      have h := hD τ (by have := hτ.2; linarith)
      simpa [Real.rpow_zero] using h⟩
  have hb' : Big 1 (fun τ : ℍ => Work.Asymptotics.E1combo8 ℓ τ) :=
    ⟨Cb, Nb, hCb, hNb, fun τ hτ => by simpa using hb τ hτ⟩
  -- `E₄ - 1` is `Big 1` and `E₄ + 1` is `Big 0`, hence `E₄² - 1` is `Big 1`
  have hr : Big 2 (fun τ : ℍ => Work.Kernels.E4Fun τ - 1
      - 240 * Work.Kernels.qParamFun τ) :=
    ⟨CE4, 0, hCE4, le_rfl, fun τ hτ => by
      have h := hE4 τ (by have := hτ.2; linarith)
      simpa [Real.rpow_zero] using h⟩
  have hE4m1 : Big 1 (fun τ : ℍ => Work.Kernels.E4Fun τ - 1) := by
    have hsum : Big 1 (fun τ : ℍ => (Work.Kernels.E4Fun τ - 1
        - 240 * Work.Kernels.qParamFun τ) + 240 * Work.Kernels.qParamFun τ) :=
      Big.add (hr.mono (by norm_num : 1 ≤ 2)) (Big.const_mul (240 : ℂ) big_q1)
    exact hsum.congr_on (fun τ _ => by ring)
  have hE4p1 : Big 0 (fun τ : ℍ => Work.Kernels.E4Fun τ + 1) := by
    have hsum : Big 0 (fun τ : ℍ => (Work.Kernels.E4Fun τ - 1) + 2 * (1 : ℂ)) :=
      Big.add (hE4m1.mono (by norm_num : 0 ≤ 1)) (Big.const_mul (2 : ℂ) Big.one)
    exact hsum.congr_on (fun τ _ => by ring)
  have hE4sq : Big 1 (fun τ : ℍ => (Work.Kernels.E4Fun τ) ^ 2 - 1) := by
    have hm := Big.mul hE4m1 hE4p1
    exact hm.congr_on (fun τ _ => by ring)
  -- assemble
  have hmain : Big 2 (fun τ : ℍ =>
      15 * ((Work.Kernels.E4Fun τ) ^ 2 - 1) * Work.Asymptotics.E1combo8 ℓ τ
        + 15 * (Work.Asymptotics.E1combo8 ℓ τ
            - (737280 * ((Real.pi : ℂ) * Complex.I * (τ : ℂ)
                + Work.Asymptotics.Compact.cuspC ℓ) + 122880) * Work.Kernels.qParamFun τ)
        + 25 * (Work.Asymptotics.E1combo24 ℓ τ
            - (516096 - 442368 * ((Real.pi : ℂ) * Complex.I * (τ : ℂ)
                + Work.Asymptotics.Compact.cuspC ℓ)) * Work.Kernels.qParamFun τ)
        - 14745600 * (Work.Kernels.DeltaFun τ - Work.Kernels.qParamFun τ)) := by
    have t1 : Big 2 (fun τ : ℍ => 15 * ((Work.Kernels.E4Fun τ) ^ 2 - 1)
        * Work.Asymptotics.E1combo8 ℓ τ) := by
      exact (Big.const_mul (15 : ℂ) (Big.mul hE4sq hb')).congr_on
        (fun τ _ => by ring)
    have t2 : Big 2 (fun τ : ℍ => 15 * (Work.Asymptotics.E1combo8 ℓ τ
        - (737280 * ((Real.pi : ℂ) * Complex.I * (τ : ℂ)
            + Work.Asymptotics.Compact.cuspC ℓ) + 122880) * Work.Kernels.qParamFun τ)) :=
      Big.const_mul (15 : ℂ) h8'
    have t3 : Big 2 (fun τ : ℍ => 25 * (Work.Asymptotics.E1combo24 ℓ τ
        - (516096 - 442368 * ((Real.pi : ℂ) * Complex.I * (τ : ℂ)
            + Work.Asymptotics.Compact.cuspC ℓ)) * Work.Kernels.qParamFun τ)) :=
      Big.const_mul (25 : ℂ) h24'
    have t4 : Big 2 (fun τ : ℍ => -(14745600 * (Work.Kernels.DeltaFun τ
        - Work.Kernels.qParamFun τ))) :=
      Big.neg (Big.const_mul (14745600 : ℂ) hD')
    have s1 := Big.add t1 t2
    have s2 := Big.add s1 t3
    have s3 := Big.add s2 t4
    exact s3.congr_on (fun τ _ => by ring)
  refine hmain.congr_on (fun τ hτ => ?_)
  simp only [P24F]
  ring

/-- `Δ = O(‖q‖)` on the funnel (`Work.Asymptotics.DeltaFun_funnel_le`). -/
private lemma big_delta : Big 1 (fun τ : ℍ => Work.Kernels.DeltaFun τ) :=
  ⟨2, 0, by norm_num, le_rfl, fun τ hτ => by
    have h := Work.Asymptotics.DeltaFun_funnel_le τ hτ
    simpa [Real.rpow_zero] using h⟩

/-- `E₄` is bounded on the funnel. -/
private lemma big_E4 : Big 0 (fun τ : ℍ => Work.Kernels.E4Fun τ) :=
  ⟨3 / 2, 0, by norm_num, le_rfl, fun τ hτ => by
    have h := Work.FunnelNumerics.E4_funnel_bounds.1 τ hτ
    simpa [Real.rpow_zero] using h⟩

/-- `E1combo8` is `Big 1`. -/
private lemma big_E1c8 (ℓ : Work.Kernels.LogLambdaData) :
    Big 1 (fun τ : ℍ => Work.Asymptotics.E1combo8 ℓ τ) := by
  obtain ⟨C, N, hC, hN, h⟩ := Work.Asymptotics.KhatE1.E1combo8_bound ℓ
  exact ⟨C, N, hC, hN, fun τ hτ => by simpa using h τ hτ⟩

/-- `E1combo24` is `Big 1`. -/
private lemma big_E1c24 (ℓ : Work.Kernels.LogLambdaData) :
    Big 1 (fun τ : ℍ => Work.Asymptotics.E1combo24 ℓ τ) := by
  obtain ⟨C, N, hC, hN, h⟩ := Work.Asymptotics.KhatE1.E1combo24_bound ℓ
  exact ⟨C, N, hC, hN, fun τ hτ => by simpa using h τ hτ⟩

/-- `E₄³·P24/Δ` is `Big 1` (`‖Δ‖ ≥ (1/2)‖q‖` on the funnel). -/
private lemma big_E4cube_P24_div (ℓ : Work.Kernels.LogLambdaData) :
    Big 1 (fun τ : ℍ => (Work.Kernels.E4Fun τ) ^ 3 * P24F ℓ τ / Work.Kernels.DeltaFun τ) := by
  obtain ⟨CP, NP, hCP, hNP, hP⟩ := P24F_big ℓ
  refine ⟨2 * (3 / 2) ^ 3 * CP, NP, by positivity, hNP, fun τ hτ => ?_⟩
  have hq0 : (0 : ℝ) ≤ ‖Work.Kernels.qParamFun τ‖ := Big.qnorm_nonneg τ
  have hq1 : ‖Work.Kernels.qParamFun τ‖ ≤ 1 := Big.qnorm_le_one τ hτ
  have hqpos : (0 : ℝ) < ‖Work.Kernels.qParamFun τ‖ := by
    rw [Work.Asymptotics.norm_qParamFun]; exact Real.exp_pos _
  have hsc1 : (1 : ℝ) ≤ Work.Kernels.scale τ := Big.one_le_scale τ
  have hdl : (1 / 2 : ℝ) * ‖Work.Kernels.qParamFun τ‖ ≤ ‖Work.Kernels.DeltaFun τ‖ :=
    Work.FunnelNumerics.Delta_funnel_bounds.1 τ (by have := hτ.2; linarith)
  have hE4 : ‖Work.Kernels.E4Fun τ‖ ≤ 3 / 2 := Work.FunnelNumerics.E4_funnel_bounds.1 τ hτ
  have h1 : ‖(Work.Kernels.E4Fun τ) ^ 3 * P24F ℓ τ‖
      ≤ (3 / 2) ^ 3 * (CP * (Work.Kernels.scale τ) ^ NP * ‖Work.Kernels.qParamFun τ‖ ^ 2) := by
    rw [norm_mul, norm_pow]
    exact mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) hE4 3) (hP τ hτ) (norm_nonneg _) (by positivity)
  have hc : (0 : ℝ) ≤ (3 / 2) ^ 3 * (CP * (Work.Kernels.scale τ) ^ NP
      * ‖Work.Kernels.qParamFun τ‖ ^ 2) := by positivity
  have hd : (0 : ℝ) < (1 / 2 : ℝ) * ‖Work.Kernels.qParamFun τ‖ := by linarith
  calc ‖(Work.Kernels.E4Fun τ) ^ 3 * P24F ℓ τ / Work.Kernels.DeltaFun τ‖
      = ‖(Work.Kernels.E4Fun τ) ^ 3 * P24F ℓ τ‖ / ‖Work.Kernels.DeltaFun τ‖ := norm_div _ _
    _ ≤ ((3 / 2) ^ 3 * (CP * (Work.Kernels.scale τ) ^ NP * ‖Work.Kernels.qParamFun τ‖ ^ 2))
          / ((1 / 2 : ℝ) * ‖Work.Kernels.qParamFun τ‖) := div_le_div₀ hc h1 hd hdl
    _ = (2 * (3 / 2) ^ 3 * CP) * (Work.Kernels.scale τ) ^ NP
          * ‖Work.Kernels.qParamFun τ‖ ^ 1 := by
        rw [pow_one]
        have hqne : ‖Work.Kernels.qParamFun τ‖ ≠ 0 := ne_of_gt hqpos
        field_simp

/-- **The reduced form of the `E(z)³`-coefficient of `Sh·Bracket24` is bounded.**

`KhatE1.Bracket24B3_eq_red` (proved in `KhatE1/Bracket24Tail_bound.lean`) identifies the
`E(z)³`-coefficient `Bracket24B3` of the `Sh`-cleared bracket with
`-(84106543104·Δ + 225780·E₄²·E1combo8 + 8940·E1combo24 - E₄³·P24/Δ)/(88560·π)`;
here that combination is shown to be `O((scale τ)^N)`, i.e. `Big 0` — far stronger than the
`O(‖q(τ)‖^{1/2})` that the tail bound requires of the `E(z)³`-coefficient. -/
theorem Bracket24B3_reduced_big (ℓ : Work.Kernels.LogLambdaData) :
    Big 1 (fun τ : ℍ =>
      -((84106543104 : ℂ) * Work.Kernels.DeltaFun τ
          + 225780 * (Work.Kernels.E4Fun τ) ^ 2 * Work.Asymptotics.E1combo8 ℓ τ
          + 8940 * Work.Asymptotics.E1combo24 ℓ τ
          - (Work.Kernels.E4Fun τ) ^ 3 * P24F ℓ τ / Work.Kernels.DeltaFun τ)
        / (88560 * (Real.pi : ℂ))) := by
  have h0 : Big 1 (fun τ : ℍ => (84106543104 : ℂ) * Work.Kernels.DeltaFun τ) :=
    Big.const_mul (84106543104 : ℂ) big_delta
  have h1 : Big 1 (fun τ : ℍ => 225780 * (Work.Kernels.E4Fun τ) ^ 2
      * Work.Asymptotics.E1combo8 ℓ τ) :=
    (Big.const_mul (225780 : ℂ) (Big.mul (Big.mul big_E4 big_E4) (big_E1c8 ℓ))).congr_on
      (fun τ _ => by ring)
  have h2 : Big 1 (fun τ : ℍ => 8940 * Work.Asymptotics.E1combo24 ℓ τ) :=
    Big.const_mul (8940 : ℂ) (big_E1c24 ℓ)
  have h3 : Big 1 (fun τ : ℍ => (Work.Kernels.E4Fun τ) ^ 3 * P24F ℓ τ
      / Work.Kernels.DeltaFun τ) := big_E4cube_P24_div ℓ
  have s1 : Big 1 (fun τ : ℍ => (84106543104 : ℂ) * Work.Kernels.DeltaFun τ
      + 225780 * (Work.Kernels.E4Fun τ) ^ 2 * Work.Asymptotics.E1combo8 ℓ τ) := by
    simpa using Big.add h0 h1
  have s2 : Big 1 (fun τ : ℍ => (84106543104 : ℂ) * Work.Kernels.DeltaFun τ
      + 225780 * (Work.Kernels.E4Fun τ) ^ 2 * Work.Asymptotics.E1combo8 ℓ τ
      + 8940 * Work.Asymptotics.E1combo24 ℓ τ) := by
    simpa using Big.add s1 h2
  have s3 : Big 1 (fun τ : ℍ => (84106543104 : ℂ) * Work.Kernels.DeltaFun τ
      + 225780 * (Work.Kernels.E4Fun τ) ^ 2 * Work.Asymptotics.E1combo8 ℓ τ
      + 8940 * Work.Asymptotics.E1combo24 ℓ τ
      - (Work.Kernels.E4Fun τ) ^ 3 * P24F ℓ τ / Work.Kernels.DeltaFun τ) := by
    simpa using Big.sub s2 h3
  have s4 : Big 1 (fun τ : ℍ => -((84106543104 : ℂ) * Work.Kernels.DeltaFun τ
      + 225780 * (Work.Kernels.E4Fun τ) ^ 2 * Work.Asymptotics.E1combo8 ℓ τ
      + 8940 * Work.Asymptotics.E1combo24 ℓ τ
      - (Work.Kernels.E4Fun τ) ^ 3 * P24F ℓ τ / Work.Kernels.DeltaFun τ)) :=
    Big.neg s3
  have s5 := Big.const_mul (((88560 * (Real.pi : ℂ)))⁻¹) s4
  refine s5.congr_on (fun τ _ => ?_)
  rw [div_eq_mul_inv]
  ring

/-- **The reduced form of the `E(z)⁵`-coefficient of `Sh·Bracket24` is bounded.**

`KhatE1.Bracket24B5_eq_red` identifies the `E(z)⁵`-coefficient `Bracket24B5` with
`-(5866622484480·Δ + 5702403·E₄²·E1combo8 + 834309·E1combo24 + (28/5)·E₄³·P24/Δ)/(20664·π)`;
that combination is `Big 1`, i.e. `O(‖q(τ)‖(scale τ)^N)`, stronger than the `O(‖q(τ)‖^{-1/2})`
the tail requires. -/
theorem Bracket24B5_reduced_big (ℓ : Work.Kernels.LogLambdaData) :
    Big 1 (fun τ : ℍ =>
      -((5866622484480 : ℂ) * Work.Kernels.DeltaFun τ
          + 5702403 * (Work.Kernels.E4Fun τ) ^ 2 * Work.Asymptotics.E1combo8 ℓ τ
          + 834309 * Work.Asymptotics.E1combo24 ℓ τ
          + (28 / 5) * (Work.Kernels.E4Fun τ) ^ 3 * P24F ℓ τ / Work.Kernels.DeltaFun τ)
        / (20664 * (Real.pi : ℂ))) := by
  have h0 : Big 1 (fun τ : ℍ => (5866622484480 : ℂ) * Work.Kernels.DeltaFun τ) :=
    Big.const_mul (5866622484480 : ℂ) big_delta
  have h1 : Big 1 (fun τ : ℍ => 5702403 * (Work.Kernels.E4Fun τ) ^ 2
      * Work.Asymptotics.E1combo8 ℓ τ) :=
    (Big.const_mul (5702403 : ℂ) (Big.mul (Big.mul big_E4 big_E4) (big_E1c8 ℓ))).congr_on
      (fun τ _ => by ring)
  have h2 : Big 1 (fun τ : ℍ => 834309 * Work.Asymptotics.E1combo24 ℓ τ) :=
    Big.const_mul (834309 : ℂ) (big_E1c24 ℓ)
  have h3 : Big 1 (fun τ : ℍ => (28 / 5) * ((Work.Kernels.E4Fun τ) ^ 3 * P24F ℓ τ
      / Work.Kernels.DeltaFun τ)) :=
    Big.const_mul ((28 / 5 : ℂ)) (big_E4cube_P24_div ℓ)
  have h3' : Big 1 (fun τ : ℍ => (28 / 5) * (Work.Kernels.E4Fun τ) ^ 3 * P24F ℓ τ
      / Work.Kernels.DeltaFun τ) :=
    h3.congr_on (fun τ _ => by ring)
  have s1 : Big 1 (fun τ : ℍ => (5866622484480 : ℂ) * Work.Kernels.DeltaFun τ
      + 5702403 * (Work.Kernels.E4Fun τ) ^ 2 * Work.Asymptotics.E1combo8 ℓ τ) := by
    simpa using Big.add h0 h1
  have s2 : Big 1 (fun τ : ℍ => (5866622484480 : ℂ) * Work.Kernels.DeltaFun τ
      + 5702403 * (Work.Kernels.E4Fun τ) ^ 2 * Work.Asymptotics.E1combo8 ℓ τ
      + 834309 * Work.Asymptotics.E1combo24 ℓ τ) := by
    simpa using Big.add s1 h2
  have s3 : Big 1 (fun τ : ℍ => (5866622484480 : ℂ) * Work.Kernels.DeltaFun τ
      + 5702403 * (Work.Kernels.E4Fun τ) ^ 2 * Work.Asymptotics.E1combo8 ℓ τ
      + 834309 * Work.Asymptotics.E1combo24 ℓ τ
      + (28 / 5) * (Work.Kernels.E4Fun τ) ^ 3 * P24F ℓ τ / Work.Kernels.DeltaFun τ) := by
    simpa using Big.add s2 h3'
  have s4 : Big 1 (fun τ : ℍ => -((5866622484480 : ℂ) * Work.Kernels.DeltaFun τ
      + 5702403 * (Work.Kernels.E4Fun τ) ^ 2 * Work.Asymptotics.E1combo8 ℓ τ
      + 834309 * Work.Asymptotics.E1combo24 ℓ τ
      + (28 / 5) * (Work.Kernels.E4Fun τ) ^ 3 * P24F ℓ τ / Work.Kernels.DeltaFun τ)) :=
    Big.neg s3
  have s5 := Big.const_mul (((20664 * (Real.pi : ℂ)))⁻¹) s4
  refine s5.congr_on (fun τ _ => ?_)
  rw [div_eq_mul_inv]
  ring

end

end Work.Asymptotics.KhatE1Core
