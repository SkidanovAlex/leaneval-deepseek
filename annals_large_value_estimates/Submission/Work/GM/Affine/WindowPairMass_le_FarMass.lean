import Mathlib
import Submission.Work.GM.Affine.far_part_defs
import Submission.Work.GM.Affine.window_part_defs
import Submission.Work.GM.Affine.bsum_far_le_winmass
import Submission.Work.GM.Affine.far_mass_eq
import Submission.Work.GM.Affine.region_I_bound
import Submission.Work.GM.Affine.far_weight_uniform_bound
import Submission.Work.GM.Affine.WinMass_basic
import Submission.Work.GM.Affine.winPairMass_pointwise_le

/-!
# GM §9 (affine sums): the window pair mass is bounded by `M₃` times the far mass

The target of this file is the lemma

`∫⁻ ξ in A, ofReal (Σ_{p ∈ Pwin T M₁ M₃ B ξ} ‖aTerm K M₂ M₃ f ξ p‖²) ≤ ofReal (C * M₃ * FarMass)`

for a universal constant `C`, uniformly in `T, M₁, M₂, M₃ ≥ 1, B`, in the test function
`f` (continuous, nonnegative, `SuppHyp C₀ f`) and in the measurable set `A`.

## Route

Write `y = ξ/m₁` and `τ = M₃(y - ℓ)`.  For a pair `p = (m₁, ℓ)`,

`‖aTerm K M₂ M₃ f ξ p‖² = (1/m₁²) ‖Bsum f M₂ y‖² · M₃² ‖ψ̂₁ K (M₃(y-ℓ))‖²`

(`normSq_aTerm`), and the pairs of `Pwin` are the `(m₁,ℓ)` with `m₁ ∈ R1 M₁` and
`2/M₃ < |ℓ-y| ≤ B/M₃`.  Dropping the upper window bound `B/M₃` and the truncation `|ℓ| ≤ Lwin`
only *enlarges* the sum, so pointwise

`Σ_{p∈Pwin} ‖aTerm p‖² ≤ Σ_{m₁∈R1 M₁} (1/m₁²)‖Bsum f M₂ (ξ/m₁)‖² · M₃² Σ'_ℓ [2/M₃<|·|]‖ψ̂₁‖²`

(`winPairMass_pointwise_le`).  Integrating in `ξ` and substituting `ξ = m₁ y` turns this into
`Σ_{m₁∈R1 M₁} (1/|m₁|) M₃² ∫_ℝ ‖Bsum f M₂ u‖² Ẇ(u) du`, where

`Ẇ(u) = Σ'_ℓ [2/M₃ < |u-ℓ|] ‖ψ̂₁ K (M₃(u-ℓ))‖²`

is the periodic far weight; `Σ_{m₁∈R1 M₁} 1/|m₁| ≤ 8` (`region_I_bound.sum_inv_abs_R1_le`) and
`Ẇ` is uniformly bounded via `far_weight_uniform_bound`.  It remains to identify

`∫_ℝ ‖Bsum f M₂ u‖² Ẇ(u) du = FarMass K f M₂ M₃ / M₃`:

expand `Ẇ`, swap the `ℓ`-sum with the integral (`lintegral_tsum`), translate `u = ℓ + s` and apply
the a.e. "sampling = periodization" identity `ofReal (Σ'_ℓ ‖Bsum(ℓ+s)‖²) = Σ'_ℓ ofReal (‖Bsum(ℓ+s)‖²)`
(`fm_ae_tsum_ne_top_of_lintegral`) — after which the integral is *literally*
`∫_{|s|>2/M₃} ofReal (P(s) ‖ψ̂₁ K (M₃ s)‖²) ds`, `P(s) = Σ'_ℓ ‖Bsum f M₂ (ℓ+s)‖²`, whose finiteness
follows from the bound on `Ẇ` and `fm_lintegral_Bsum_sq_ne_top`, and which `far_mass_eq` identifies
with `FarMass/M₃` (`ofReal_integral_eq_lintegral_ofReal`).

The value of the constant is `C = 16` (the computation gives `8`).
-/

open Complex MeasureTheory Finset
open scoped BigOperators FourierTransform

set_option autoImplicit false
set_option linter.unusedVariables false

namespace Work.GM.Affine

noncomputable section

/-- The periodic far weight
`Ẇ(u) = Σ'_ℓ [2/M₃ < |u-ℓ|] ‖ψ̂₁ K (M₃(u-ℓ))‖²` of the far part of the `ℓ`-sum. -/
def wpmFarWeight (K M₃ : ℝ) (u : ℝ) : ENNReal :=
  ∑' ℓ : ℤ, (if 2 / M₃ < |u - (ℓ : ℝ)| then
    ENNReal.ofReal (‖psi1hat K (M₃ * (u - (ℓ : ℝ)))‖ ^ 2) else 0)

/-- The pointwise majorant of the window pair mass produced by
`Work.GM.Affine.winPairMass_pointwise_le`. -/
def wpmPairMajorant (K T M₁ M₂ M₃ B : ℝ) (f : ℝ → ℝ) (ξ : ℝ) : ENNReal :=
  ∑ m₁ ∈ R1 M₁, ENNReal.ofReal (1 / (m₁ : ℝ) ^ 2 * ‖Bsum f M₂ (ξ / (m₁ : ℝ))‖ ^ 2) *
    (∑' ℓ : ℤ, (if 2 / M₃ < |ξ / (m₁ : ℝ) - (ℓ : ℝ)| then
      ENNReal.ofReal (M₃ ^ 2 * ‖psi1hat K (M₃ * (ξ / (m₁ : ℝ) - (ℓ : ℝ)))‖ ^ 2) else 0))

/-- The inner `ℓ`-sum of `wpmPairMajorant` is `M₃²` times the periodic far weight. -/
lemma wpm_farWeight_mul_ofReal (K M₃ : ℝ) (y : ℝ) :
    ENNReal.ofReal (M₃ ^ 2) * wpmFarWeight K M₃ y
      = ∑' ℓ : ℤ, (if 2 / M₃ < |y - (ℓ : ℝ)| then
          ENNReal.ofReal (M₃ ^ 2 * ‖psi1hat K (M₃ * (y - (ℓ : ℝ)))‖ ^ 2) else 0) := by
  rw [wpmFarWeight, ← ENNReal.tsum_mul_left]
  refine tsum_congr (fun ℓ => ?_)
  by_cases h : 2 / M₃ < |y - ↑ℓ|
  · rw [if_pos h, if_pos h, ENNReal.ofReal_mul (sq_nonneg M₃)]
  · rw [if_neg h, if_neg h, mul_zero]

/-- The factored form of `wpmPairMajorant`. -/
lemma wpm_pairMajorant_eq (K T M₁ M₂ M₃ B : ℝ) (f : ℝ → ℝ) (ξ : ℝ) :
    wpmPairMajorant K T M₁ M₂ M₃ B f ξ
      = ∑ m₁ ∈ R1 M₁, ENNReal.ofReal (1 / (m₁:ℝ)^2) * ENNReal.ofReal (‖Bsum f M₂ (ξ/(m₁:ℝ))‖^2)
          * (ENNReal.ofReal (M₃^2) * wpmFarWeight K M₃ (ξ/(m₁:ℝ))) := by
  rw [wpmPairMajorant]
  refine Finset.sum_congr rfl (fun m₁ hm₁ => ?_)
  rw [wpm_farWeight_mul_ofReal, ENNReal.ofReal_mul (by positivity : (0:ℝ) ≤ 1 / (m₁:ℝ)^2)]

lemma wpm_measurable_farWeight_term (K M₃ : ℝ) (ℓ : ℤ) :
    Measurable (fun u : ℝ => (if 2 / M₃ < |u - (ℓ : ℝ)| then
      ENNReal.ofReal (‖psi1hat K (M₃ * (u - (ℓ : ℝ)))‖ ^ 2) else 0)) := by
  refine Measurable.ite ?_ ?_ measurable_const
  · measurability
  · exact ENNReal.measurable_ofReal.comp (((psi1hat_continuous K).measurable.comp
      (measurable_const.mul (measurable_id.sub measurable_const))).norm.pow_const 2)

lemma wpm_measurable_farWeight (K M₃ : ℝ) : Measurable (wpmFarWeight K M₃) := by
  unfold wpmFarWeight
  exact Measurable.tsum (fun ℓ => wpm_measurable_farWeight_term K M₃ ℓ)

/-- Change of variables `x ↦ c * x` for the Lebesgue integral of an `ℝ≥0∞`-valued function. -/
lemma wpm_lintegral_comp_mul_left_volume {c : ℝ} (hc : c ≠ 0) {g : ℝ → ENNReal}
    (hg : Measurable g) :
    (∫⁻ x : ℝ, g (c * x)) = (ENNReal.ofReal |c⁻¹|) * (∫⁻ x : ℝ, g x) := by
  have h1 : (∫⁻ a : ℝ, g a ∂(Measure.map (fun x : ℝ => c * x) (volume : Measure ℝ))) =
      ∫⁻ x : ℝ, g (c * x) :=
    MeasureTheory.lintegral_map (f := g) (g := fun x : ℝ => c * x) hg (by fun_prop)
  rw [← h1, Real.map_volume_mul_left hc, MeasureTheory.lintegral_smul_measure, smul_eq_mul]

/-- If the `ℝ≥0∞`-sum of a nonnegative real family is finite then the family is summable. -/
lemma wpm_summable_of_tsum_ofReal_ne_top {a : ℤ → ℝ} (ha : ∀ ℓ, 0 ≤ a ℓ)
    (ht : (∑' ℓ : ℤ, ENNReal.ofReal (a ℓ)) ≠ ⊤) : Summable a := by
  have h1 : (∑' ℓ : ℤ, (((a ℓ).toNNReal : NNReal) : ENNReal)) ≠ ⊤ := by
    simpa only [ENNReal.ofReal, Real.toNNReal_of_nonneg (ha _)] using ht
  have h2 : Summable (fun ℓ : ℤ => (a ℓ).toNNReal) := ENNReal.tsum_coe_ne_top_iff_summable.mp h1
  have h3 : Summable (fun ℓ : ℤ => ((a ℓ).toNNReal : ℝ)) := NNReal.summable_coe.mpr h2
  exact h3.congr (fun ℓ => Real.coe_toNNReal (a ℓ) (ha ℓ))

/-! ## The measure-theoretic core -/

/-- Expansion of the far weight integral into its `ℓ`-terms. -/
lemma wpm_farWeight_lintegral_expand {K M₂ M₃ : ℝ} {f : ℝ → ℝ} :
    (∫⁻ u : ℝ, ENNReal.ofReal (‖Bsum f M₂ u‖ ^ 2) * wpmFarWeight K M₃ u)
      = ∑' ℓ : ℤ, ∫⁻ u : ℝ, ENNReal.ofReal (‖Bsum f M₂ u‖ ^ 2) *
          (if 2 / M₃ < |u - (ℓ : ℝ)| then
            ENNReal.ofReal (‖psi1hat K (M₃ * (u - (ℓ : ℝ)))‖ ^ 2) else 0) := by
  unfold wpmFarWeight
  rw [show (∫⁻ u : ℝ, ENNReal.ofReal (‖Bsum f M₂ u‖ ^ 2) *
        (∑' ℓ : ℤ, if 2 / M₃ < |u - (ℓ : ℝ)| then
          ENNReal.ofReal (‖psi1hat K (M₃ * (u - (ℓ : ℝ)))‖ ^ 2) else 0))
      = ∫⁻ u : ℝ, ∑' ℓ : ℤ, ENNReal.ofReal (‖Bsum f M₂ u‖ ^ 2) *
        (if 2 / M₃ < |u - (ℓ : ℝ)| then
          ENNReal.ofReal (‖psi1hat K (M₃ * (u - (ℓ : ℝ)))‖ ^ 2) else 0) from
    MeasureTheory.lintegral_congr (fun u => (ENNReal.tsum_mul_left).symm)]
  exact MeasureTheory.lintegral_tsum (β := ℤ) (fun ℓ => ((ENNReal.measurable_ofReal.comp
    ((measurable_Bsum f M₂).norm.pow_const 2)).mul
      (wpm_measurable_farWeight_term K M₃ ℓ)).aemeasurable)

/-- Translation invariance of the `ℓ`-th term of the far weight integral. -/
lemma wpm_farWeight_lintegral_translate {K M₂ M₃ : ℝ} {f : ℝ → ℝ} (ℓ : ℤ) :
    (∫⁻ u : ℝ, ENNReal.ofReal (‖Bsum f M₂ u‖ ^ 2) *
        (if 2 / M₃ < |u - (ℓ : ℝ)| then
          ENNReal.ofReal (‖psi1hat K (M₃ * (u - (ℓ : ℝ)))‖ ^ 2) else 0))
      = ∫⁻ s : ℝ, ENNReal.ofReal (‖Bsum f M₂ ((ℓ : ℝ) + s)‖ ^ 2) *
        (if 2 / M₃ < |s| then ENNReal.ofReal (‖psi1hat K (M₃ * s)‖ ^ 2) else 0) := by
  rw [show (∫⁻ u : ℝ, ENNReal.ofReal (‖Bsum f M₂ u‖ ^ 2) *
        (if 2 / M₃ < |u - (ℓ : ℝ)| then
          ENNReal.ofReal (‖psi1hat K (M₃ * (u - (ℓ : ℝ)))‖ ^ 2) else 0))
      = ∫⁻ s : ℝ, (fun u : ℝ => ENNReal.ofReal (‖Bsum f M₂ u‖ ^ 2) *
        (if 2 / M₃ < |u - (ℓ : ℝ)| then
          ENNReal.ofReal (‖psi1hat K (M₃ * (u - (ℓ : ℝ)))‖ ^ 2) else 0)) ((ℓ : ℝ) + s) from
    (MeasureTheory.lintegral_add_left_eq_self _ (ℓ : ℝ)).symm]
  refine MeasureTheory.lintegral_congr (fun s => ?_)
  dsimp only
  rw [show (ℓ : ℝ) + s - (ℓ : ℝ) = s by ring]

/-- **The far weight integral is `FarMass / M₃`.** -/
theorem wpm_far_weight_lintegral_eq {C₀ K M₂ M₃ : ℝ} (hC₀ : 1 ≤ C₀) (hK : 0 < K) (hM₂ : 0 < M₂)
    (hM₃ : 1 ≤ M₃) {f : ℝ → ℝ} (hf : Continuous f) (hsup : SuppHyp C₀ f) :
    (∫⁻ u : ℝ, ENNReal.ofReal (‖Bsum f M₂ u‖ ^ 2) * wpmFarWeight K M₃ u)
      = ENNReal.ofReal (FarMass K f M₂ M₃ / M₃) := by
  have hM₃pos : 0 < M₃ := lt_of_lt_of_le zero_lt_one hM₃
  set S : Set ℝ := Set.Ioi (2 / M₃) ∪ Set.Iio (-(2 / M₃)) with hSdef
  have hSmeas : MeasurableSet S := measurableSet_Ioi.union measurableSet_Iio
  have hSmem : ∀ s : ℝ, s ∈ S ↔ 2 / M₃ < |s| := fun s => fm_mem_far_iff_abs (2 / M₃) s
  have hVmeas : Measurable (fun s : ℝ => (if 2 / M₃ < |s| then
      ENNReal.ofReal (‖psi1hat K (M₃ * s)‖ ^ 2) else 0)) := by
    simpa using wpm_measurable_farWeight_term K M₃ 0
  have hBne : (∫⁻ u : ℝ, ENNReal.ofReal (‖Bsum f M₂ u‖ ^ 2)) ≠ ⊤ :=
    fm_lintegral_Bsum_sq_ne_top hC₀ hM₂ hf hsup
  have hae : ∀ᵐ s : ℝ, ENNReal.ofReal (∑' ℓ : ℤ, ‖Bsum f M₂ ((ℓ : ℝ) + s)‖ ^ 2)
      = ∑' ℓ : ℤ, ENNReal.ofReal (‖Bsum f M₂ ((ℓ : ℝ) + s)‖ ^ 2) := by
    filter_upwards [fm_ae_tsum_ne_top_of_lintegral (M₂ := M₂) (f := f) hBne] with s hs
    exact ENNReal.ofReal_tsum_of_nonneg (fun ℓ => sq_nonneg _)
      (wpm_summable_of_tsum_ofReal_ne_top (fun ℓ => sq_nonneg _) hs)
  have hA : (∫⁻ u : ℝ, ENNReal.ofReal (‖Bsum f M₂ u‖ ^ 2) * wpmFarWeight K M₃ u)
      = ∫⁻ s : ℝ, ENNReal.ofReal (∑' ℓ : ℤ, ‖Bsum f M₂ ((ℓ : ℝ) + s)‖ ^ 2) *
          (if 2 / M₃ < |s| then ENNReal.ofReal (‖psi1hat K (M₃ * s)‖ ^ 2) else 0) := by
    rw [wpm_farWeight_lintegral_expand]
    rw [tsum_congr (fun ℓ =>
      wpm_farWeight_lintegral_translate (K := K) (M₂ := M₂) (M₃ := M₃) (f := f) ℓ)]
    rw [show (∑' ℓ : ℤ, ∫⁻ s : ℝ, ENNReal.ofReal (‖Bsum f M₂ ((ℓ : ℝ) + s)‖ ^ 2) *
          (if 2 / M₃ < |s| then ENNReal.ofReal (‖psi1hat K (M₃ * s)‖ ^ 2) else 0))
        = ∫⁻ s : ℝ, ∑' ℓ : ℤ, ENNReal.ofReal (‖Bsum f M₂ ((ℓ : ℝ) + s)‖ ^ 2) *
          (if 2 / M₃ < |s| then ENNReal.ofReal (‖psi1hat K (M₃ * s)‖ ^ 2) else 0) from
      (MeasureTheory.lintegral_tsum (β := ℤ)
        (f := fun ℓ s => ENNReal.ofReal (‖Bsum f M₂ ((ℓ:ℝ) + s)‖ ^ 2) *
          (if 2 / M₃ < |s| then ENNReal.ofReal (‖psi1hat K (M₃ * s)‖ ^ 2) else 0))
        (fun ℓ => ((ENNReal.measurable_ofReal.comp (((measurable_Bsum f M₂).norm.pow_const 2).comp
            (measurable_const.add measurable_id))).mul hVmeas).aemeasurable)).symm]
    refine MeasureTheory.lintegral_congr_ae ?_
    filter_upwards [hae] with s hs
    rw [hs, ENNReal.tsum_mul_right]
  obtain ⟨Cw, _hCwpos, hCw⟩ := far_weight_uniform_bound hK
  have hfinU : (∫⁻ u : ℝ, ENNReal.ofReal (‖Bsum f M₂ u‖ ^ 2) * wpmFarWeight K M₃ u) < ⊤ := by
    have hle : (∫⁻ u : ℝ, ENNReal.ofReal (‖Bsum f M₂ u‖ ^ 2) * wpmFarWeight K M₃ u)
        ≤ ENNReal.ofReal Cw * (∫⁻ u : ℝ, ENNReal.ofReal (‖Bsum f M₂ u‖ ^ 2)) := by
      calc (∫⁻ u : ℝ, ENNReal.ofReal (‖Bsum f M₂ u‖ ^ 2) * wpmFarWeight K M₃ u)
          ≤ ∫⁻ u : ℝ, ENNReal.ofReal (‖Bsum f M₂ u‖ ^ 2) * ENNReal.ofReal Cw :=
            MeasureTheory.lintegral_mono
              (fun u => mul_le_mul_of_nonneg_left (hCw M₃ hM₃ u) bot_le)
        _ = (∫⁻ u : ℝ, ENNReal.ofReal (‖Bsum f M₂ u‖ ^ 2)) * ENNReal.ofReal Cw :=
            MeasureTheory.lintegral_mul_const _
              (ENNReal.measurable_ofReal.comp ((measurable_Bsum f M₂).norm.pow_const 2))
        _ = ENNReal.ofReal Cw * (∫⁻ u : ℝ, ENNReal.ofReal (‖Bsum f M₂ u‖ ^ 2)) := mul_comm _ _
    refine lt_of_le_of_lt hle ?_
    exact lt_top_iff_ne_top.mpr (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hBne)
  set F : ℝ → ℝ := fun s => (∑' ℓ : ℤ, ‖Bsum f M₂ ((ℓ : ℝ) + s)‖ ^ 2) * ‖psi1hat K (M₃ * s)‖ ^ 2
    with hFdef
  have hFnn : ∀ s : ℝ, 0 ≤ F s := by
    intro s
    rw [hFdef]
    exact mul_nonneg (tsum_nonneg (fun ℓ => sq_nonneg _)) (sq_nonneg _)
  have h5 : (∫⁻ s : ℝ, ENNReal.ofReal (∑' ℓ : ℤ, ‖Bsum f M₂ ((ℓ : ℝ) + s)‖ ^ 2) *
        (if 2 / M₃ < |s| then ENNReal.ofReal (‖psi1hat K (M₃ * s)‖ ^ 2) else 0))
      = ∫⁻ s in S, ENNReal.ofReal (F s) := by
    rw [← MeasureTheory.lintegral_indicator hSmeas]
    refine MeasureTheory.lintegral_congr (fun s => ?_)
    rw [Set.indicator_apply]
    by_cases hs : s ∈ S
    · rw [if_pos hs, if_pos ((hSmem s).mp hs),
        ENNReal.ofReal_mul (tsum_nonneg (fun ℓ => sq_nonneg _))]
    · rw [if_neg hs, if_neg (fun h => hs ((hSmem s).mpr h)), mul_zero]
  have hfin7 : (∫⁻ s in S, ENNReal.ofReal (F s)) < ⊤ := by
    rw [← h5, ← hA]
    exact hfinU
  have hmeasP : Measurable (fun s : ℝ =>
      ∑' ℓ : ℤ, ENNReal.ofReal (‖Bsum f M₂ ((ℓ : ℝ) + s)‖ ^ 2)) := by
    refine Measurable.tsum (fun ℓ => ?_)
    exact ENNReal.measurable_ofReal.comp (((measurable_Bsum f M₂).norm.pow_const 2).comp
      (measurable_const.add measurable_id))
  have hmeasG : Measurable (fun s : ℝ =>
      (∑' ℓ : ℤ, ENNReal.ofReal (‖Bsum f M₂ ((ℓ : ℝ) + s)‖ ^ 2)).toReal
        * ‖psi1hat K (M₃ * s)‖ ^ 2) :=
    (ENNReal.measurable_toReal.comp hmeasP).mul
      (((psi1hat_continuous K).measurable.comp (measurable_const.mul measurable_id)).norm.pow_const 2)
  have hFG : (fun s : ℝ => (∑' ℓ : ℤ, ENNReal.ofReal (‖Bsum f M₂ ((ℓ : ℝ) + s)‖ ^ 2)).toReal
        * ‖psi1hat K (M₃ * s)‖ ^ 2) =ᵐ[volume] F := by
    filter_upwards [hae] with s hs
    rw [hFdef, ← hs, ENNReal.toReal_ofReal (tsum_nonneg (fun ℓ => sq_nonneg _))]
  have hIntOn : IntegrableOn F S :=
    ⟨(hmeasG.aestronglyMeasurable).congr (MeasureTheory.ae_restrict_of_ae hFG),
      (MeasureTheory.hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall hFnn)).mpr hfin7⟩
  have h6 : (∫⁻ s in S, ENNReal.ofReal (F s)) = ENNReal.ofReal (∫ s in S, F s) :=
    (MeasureTheory.ofReal_integral_eq_lintegral_ofReal hIntOn
      (Filter.Eventually.of_forall hFnn)).symm
  have h7 : (∫ s in S, F s) = FarMass K f M₂ M₃ / M₃ := by
    rw [hSdef, hFdef, far_mass_eq hC₀ hK hM₂ hM₃pos hf hsup]
    rw [mul_div_cancel_left₀ _ (ne_of_gt hM₃pos)]
  calc (∫⁻ u : ℝ, ENNReal.ofReal (‖Bsum f M₂ u‖ ^ 2) * wpmFarWeight K M₃ u)
      = ∫⁻ s : ℝ, ENNReal.ofReal (∑' ℓ : ℤ, ‖Bsum f M₂ ((ℓ : ℝ) + s)‖ ^ 2) *
          (if 2 / M₃ < |s| then ENNReal.ofReal (‖psi1hat K (M₃ * s)‖ ^ 2) else 0) := hA
    _ = ∫⁻ s in S, ENNReal.ofReal (F s) := h5
    _ = ENNReal.ofReal (∫ s in S, F s) := h6
    _ = ENNReal.ofReal (FarMass K f M₂ M₃ / M₃) := by rw [h7]

/-! ## The assembly -/

/-- **Assembly.**  Given the pointwise reduction of the pair mass to `wpmPairMajorant` and the
identification of the periodic far weight integral with `FarMass/M₃`, the window pair mass is at
most `16 M₃ FarMass`. -/
theorem windowPairMass_le_of {K T M₁ M₂ M₃ B : ℝ} {f : ℝ → ℝ}
    (hpt : ∀ ξ, ENNReal.ofReal (∑ p ∈ Pwin T M₁ M₃ B ξ, ‖aTerm K M₂ M₃ f ξ p‖ ^ 2)
        ≤ wpmPairMajorant K T M₁ M₂ M₃ B f ξ)
    (hfar : (∫⁻ u : ℝ, ENNReal.ofReal (‖Bsum f M₂ u‖ ^ 2) * wpmFarWeight K M₃ u)
        = ENNReal.ofReal (FarMass K f M₂ M₃ / M₃))
    (hM₁ : 0 < M₁) (hM₃ : 1 ≤ M₃) (A : Set ℝ) :
    (∫⁻ ξ in A, ENNReal.ofReal (∑ p ∈ Pwin T M₁ M₃ B ξ, ‖aTerm K M₂ M₃ f ξ p‖ ^ 2))
      ≤ ENNReal.ofReal (16 * M₃ * FarMass K f M₂ M₃) := by
  have hM₃pos : 0 < M₃ := lt_of_lt_of_le zero_lt_one hM₃
  set U : ENNReal :=
    ∫⁻ u : ℝ, ENNReal.ofReal (‖Bsum f M₂ u‖ ^ 2) * wpmFarWeight K M₃ u with hUdef
  have hfarU : U = ENNReal.ofReal (FarMass K f M₂ M₃ / M₃) := hfar
  set F : ℝ → ENNReal := fun x => ENNReal.ofReal (‖Bsum f M₂ x‖ ^ 2) * wpmFarWeight K M₃ x
    with hF
  have hG : Measurable F :=
    (ENNReal.measurable_ofReal.comp ((measurable_Bsum f M₂).norm.pow_const 2)).mul
      (wpm_measurable_farWeight K M₃)
  have hmeasm₁ : ∀ m₁ ∈ R1 M₁, Measurable (fun ξ : ℝ =>
      ENNReal.ofReal (1 / (m₁:ℝ)^2) * ENNReal.ofReal (‖Bsum f M₂ (ξ/(m₁:ℝ))‖^2)
        * (ENNReal.ofReal (M₃^2) * wpmFarWeight K M₃ (ξ/(m₁:ℝ)))) := by
    intro m₁ hm₁
    refine ((measurable_const.mul ((ENNReal.measurable_ofReal.comp
      ((measurable_Bsum f M₂).norm.pow_const 2)).comp (measurable_id.div_const _)))).mul ?_
    exact (measurable_const.mul ((wpm_measurable_farWeight K M₃).comp
      (measurable_id.div_const _)))
  have hterm : ∀ m₁ ∈ R1 M₁,
      (∫⁻ ξ in A, ENNReal.ofReal (1 / (m₁:ℝ)^2) * ENNReal.ofReal (‖Bsum f M₂ (ξ/(m₁:ℝ))‖^2)
          * (ENNReal.ofReal (M₃^2) * wpmFarWeight K M₃ (ξ/(m₁:ℝ))))
        ≤ (ENNReal.ofReal (1/(m₁:ℝ)^2) * ENNReal.ofReal |(m₁:ℝ)|)
          * (ENNReal.ofReal (M₃^2) * U) := by
    intro m₁ hm₁
    have hne : (m₁:ℝ) ≠ 0 := by
      intro h
      have h2 := (Finset.mem_filter.mp hm₁).2
      rw [h, abs_zero] at h2
      linarith
    have hGm₁ : Measurable (fun ξ : ℝ => F (ξ / (m₁:ℝ))) :=
      hG.comp (measurable_id.div_const (m₁:ℝ))
    have hrew1 : (∫⁻ ξ in A, ENNReal.ofReal (1 / (m₁:ℝ)^2)
          * ENNReal.ofReal (‖Bsum f M₂ (ξ/(m₁:ℝ))‖^2)
          * (ENNReal.ofReal (M₃^2) * wpmFarWeight K M₃ (ξ/(m₁:ℝ))))
        = ∫⁻ ξ in A, (ENNReal.ofReal (1/(m₁:ℝ)^2) * ENNReal.ofReal (M₃^2))
            * (fun x : ℝ => F (x / (m₁:ℝ))) ξ := by
      refine MeasureTheory.lintegral_congr (fun ξ => ?_)
      rw [hF]; ring
    rw [hrew1, MeasureTheory.lintegral_const_mul _ hGm₁]
    have hmono : (ENNReal.ofReal (1/(m₁:ℝ)^2) * ENNReal.ofReal (M₃^2))
          * ∫⁻ ξ in A, (fun x : ℝ => F (x / (m₁:ℝ))) ξ
        ≤ (ENNReal.ofReal (1/(m₁:ℝ)^2) * ENNReal.ofReal (M₃^2))
          * ∫⁻ ξ : ℝ, (fun x : ℝ => F (x / (m₁:ℝ))) ξ :=
      mul_le_mul_of_nonneg_left
        (by simpa only [MeasureTheory.Measure.restrict_univ] using
          lintegral_mono_set (Set.subset_univ A))
        bot_le
    refine hmono.trans ?_
    have hsc := wpm_lintegral_comp_mul_left_volume (c := 1/(m₁:ℝ)) (by simpa using hne) hG
    have hsc' : (∫⁻ ξ : ℝ, (fun x : ℝ => F (x / (m₁:ℝ))) ξ) = ENNReal.ofReal |(m₁:ℝ)| * U := by
      rw [show (∫⁻ ξ : ℝ, (fun x : ℝ => F (x / (m₁:ℝ))) ξ)
          = ∫⁻ ξ : ℝ, F ((1/(m₁:ℝ)) * ξ) from
        MeasureTheory.lintegral_congr (fun ξ => by rw [one_div_mul_eq_div])]
      rw [hsc, hUdef]
      congr 1
      rw [one_div, inv_inv]
    rw [hsc']
    exact le_of_eq (by ring)
  calc (∫⁻ ξ in A, ENNReal.ofReal (∑ p ∈ Pwin T M₁ M₃ B ξ, ‖aTerm K M₂ M₃ f ξ p‖ ^ 2))
      ≤ ∫⁻ ξ in A, wpmPairMajorant K T M₁ M₂ M₃ B f ξ := MeasureTheory.lintegral_mono (fun ξ => hpt ξ)
    _ = ∑ m₁ ∈ R1 M₁, ∫⁻ ξ in A, ENNReal.ofReal (1/(m₁:ℝ)^2)
          * ENNReal.ofReal (‖Bsum f M₂ (ξ/(m₁:ℝ))‖^2)
          * (ENNReal.ofReal (M₃^2) * wpmFarWeight K M₃ (ξ/(m₁:ℝ))) := by
        rw [show (∫⁻ ξ in A, wpmPairMajorant K T M₁ M₂ M₃ B f ξ)
            = ∫⁻ ξ in A, ∑ m₁ ∈ R1 M₁, ENNReal.ofReal (1/(m₁:ℝ)^2)
                * ENNReal.ofReal (‖Bsum f M₂ (ξ/(m₁:ℝ))‖^2)
                * (ENNReal.ofReal (M₃^2) * wpmFarWeight K M₃ (ξ/(m₁:ℝ))) from
          MeasureTheory.lintegral_congr (fun ξ => wpm_pairMajorant_eq K T M₁ M₂ M₃ B f ξ)]
        exact MeasureTheory.lintegral_finsetSum _ (fun m₁ hm₁ => hmeasm₁ m₁ hm₁)
    _ ≤ ∑ m₁ ∈ R1 M₁, (ENNReal.ofReal (1/(m₁:ℝ)^2) * ENNReal.ofReal |(m₁:ℝ)|)
          * (ENNReal.ofReal (M₃^2) * U) := Finset.sum_le_sum hterm
    _ = (∑ m₁ ∈ R1 M₁, ENNReal.ofReal (1/|(m₁:ℝ)|)) * (ENNReal.ofReal (M₃^2) * U) := by
        rw [← Finset.sum_mul]
        congr 1
        refine Finset.sum_congr rfl (fun m₁ hm₁ => ?_)
        have hne : (m₁:ℝ) ≠ 0 := by
          intro h
          have h2 := (Finset.mem_filter.mp hm₁).2
          rw [h, abs_zero] at h2
          linarith
        rw [← ENNReal.ofReal_mul (by positivity : (0:ℝ) ≤ 1/(m₁:ℝ)^2)]
        congr 1
        rw [← sq_abs]
        field_simp
    _ ≤ ENNReal.ofReal 8 * (ENNReal.ofReal (M₃^2) * U) := by
        refine mul_le_mul_of_nonneg_right ?_ bot_le
        rw [← ENNReal.ofReal_sum_of_nonneg (fun m₁ hm₁ => by positivity)]
        exact ENNReal.ofReal_le_ofReal (sum_inv_abs_R1_le M₁ hM₁)
    _ = ENNReal.ofReal (8 * M₃^2) * U := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 8)]
    _ = ENNReal.ofReal (8 * M₃^2) * ENNReal.ofReal (FarMass K f M₂ M₃ / M₃) := by rw [hfarU]
    _ = ENNReal.ofReal (8 * M₃^2 * (FarMass K f M₂ M₃ / M₃)) := by
        rw [← ENNReal.ofReal_mul (by positivity)]
    _ ≤ ENNReal.ofReal (16 * M₃ * FarMass K f M₂ M₃) := by
        refine ENNReal.ofReal_le_ofReal ?_
        have hF0 : 0 ≤ FarMass K f M₂ M₃ :=
          tsum_nonneg (fun ℓ => integral_nonneg (fun τ => by positivity))
        have hkey : 8 * M₃^2 * (FarMass K f M₂ M₃ / M₃) = 8 * M₃ * FarMass K f M₂ M₃ := by
          field_simp
        rw [hkey]
        nlinarith [hM₃pos.le, hF0]

theorem WindowPairMass_le_FarMass {C₀ K : ℝ} (hC₀ : 1 ≤ C₀) (hK : 0 < K) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (T M₁ M₂ M₃ B : ℝ), 0 < M₁ → 0 < M₂ → 1 ≤ M₃ →
      ∀ f : ℝ → ℝ, Continuous f → (∀ u, 0 ≤ f u) → SuppHyp C₀ f →
      ∀ A : Set ℝ,
        (∫⁻ ξ in A, ENNReal.ofReal (∑ p ∈ Pwin T M₁ M₃ B ξ, ‖aTerm K M₂ M₃ f ξ p‖ ^ 2))
          ≤ ENNReal.ofReal (C * M₃ * FarMass K f M₂ M₃) := by
  refine ⟨16, by norm_num, ?_⟩
  intro T M₁ M₂ M₃ B hM₁ hM₂ hM₃ f hf hfnn hsup A
  exact windowPairMass_le_of
    (fun ξ => winPairMass_pointwise_le K T M₁ M₂ M₃ B hM₁
      (lt_of_lt_of_le zero_lt_one hM₃) f ξ)
    (wpm_far_weight_lintegral_eq hC₀ hK hM₂ hM₃ hf hsup) hM₁ hM₃ A

end

end Work.GM.Affine
