import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.Work.BoseFixB1.BoxFrameAux
import Submission.Work.BoseFixB1.boxTauGen_mode_bound_meas
import Submission.Work.BoseFixB1.slotInvariant_indicator_integral
import Submission.Work.BoseFixB1.stronglyMeasurable_frameIntegrand
import Submission.Work.BoseFixB1.tBamp_boxQInd_normSq
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB1B.pairRung.winModeContentLeWord`

The `F`-weighted windowed-mode content of an arbitrary state `Ψ : X n → ℝ` is paid by the
`p`-diagonal kinetic word `Work.UBBInputs8.tBdiagFormInd` with the **slot count** `n` as
constant:

`(2π)⁻³∫_q fsKinCoeff c₀ ‖q‖ · boxWinModePGen a volA Ac χ Ψ q ≤ n · tBdiagFormInd a Ac volA χ (fsKinCoeff c₀) Ψ`.

## Structure of the proof

1. **Pointwise (in `q`) slot Cauchy–Schwarz** (§0b, proved here in a *clash-free* cone).
   For each of the two real windowed modes `g = boxWinModeReGen/ImGen`,
   `(boxTauAnnGen volA Ac g Ψ x)² ≤ volA⁻¹·n·Σ_i 1_{Ac}(x_i)·(∫_{Ac} g z Ψ(x_{i←z})dz)²`
   (`boxTauAnnGen_sq_le_card`); after the slot peel `slotInvariant_indicator_integral` and the
   amplitude dictionary `tBamp_boxQInd_normSq` this gives, for every `q`,
   `boxWinModePGen … q ≤ n · Σ_i (a³)⁻¹∫_{abox n a} ‖tBamp χ q (Q_{Ac,i}Ψ) i x‖²`
   (`boxWinModePGen_le_slotSum_clean`).

2. **Integrability of the `q`-integrand on the right** (§2).  The FS support hypothesis `hχsupp`
   makes the windowed fibre of the box projection the difference of two `(1+‖q‖)⁻³`-decaying
   amplitudes (`Work.BoseBox.tBamp_boxQInd_eq_sub` + `Work.SmallBoxTBWord.tBamp_decay`), so the
   `q`-integrand of `tBdiagFormInd` is dominated by `(1+‖q‖)⁻⁴`, integrable in dimension three.

3. **Monotone-integral step** (§1).  `f := q ↦ fsKinCoeff c₀ ‖q‖ · boxWinModePGen … q` is
   nonnegative, pointwise dominated by the integrable `q ↦ fsKinCoeff c₀ ‖q‖ · n · Σ_i (…)`,
   hence integrable, and `MeasureTheory.integral_mono` gives
   `∫ f ≤ ∫ q, fsKinCoeff c₀ ‖q‖ · (n · Σ_i …) = n (2π)³ tBdiagFormInd`.

4. **Arithmetic**: multiply by `(2π)⁻³`.

Measurability of `q ↦ boxWinModePGen … q` is proved here from scratch
(`aeStronglyMeasurable_boxWinModePGen`), since the corpus's `stronglyMeasurable_frameIntegrand`
is stated for `X (N+1)`; it needs no hypotheses beyond measurability of `Ac`, continuity of `χ`
and continuity of `Ψ`.

## Hygiene (why the bound is re-proved here)

The corpus's `Work.BoseFixB1.boxWinModePGen_le_slotSum`, `…_le_count_tBamp`,
`boxWinModePGen_eq_integral_frameIntegrand` and `tBamp_boxQInd_decay` all live *above*
`Submission.Work.BoseFixB1.boxWords_eq_sum_sectorPiece`, which declares
`Work.BoseFixB1.exists_bound_abox` — a name duplicated in
`Submission.Work.BoseFixB1.BoxPairIntGenC2.boxC2SumC2`, which is in the import cone of this
directory's `pairRungImports`.  Importing both poisons the environment, so none of those modules
is imported here: every ingredient is taken from a module compatible with `pairRungImports`
(this file together with `pairRungImports` builds).
-/

noncomputable section

open MeasureTheory Filter
open scoped Topology Real BigOperators ENNReal

namespace Work.BoseFixB1B.pairRung

local notation "E3" => EuclideanSpace ℝ (Fin 3)

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

/-! ## 0. Measurability of `q ↦ boxWinModePGen … q` -/

/-- The genuine windowed mode content `q ↦ boxWinModePGen a volA Ac χ Ψ q` is
`AEStronglyMeasurable` for a measurable box `Ac`, a continuous window `χ` and a continuous
state `Ψ` (no smoothness or support hypothesis is needed). -/
theorem aeStronglyMeasurable_boxWinModePGen {n : ℕ} {a volA : ℝ}
    {Ac : Set E3} (hAcm : MeasurableSet Ac)
    {χ : E3 → ℝ} (hχc : Continuous χ)
    {Ψ : Submission.BoseGases.X n → ℝ} (hΨc : Continuous Ψ) :
    AEStronglyMeasurable (fun q : E3 => Work.BoseFixB1.boxWinModePGen a volA Ac χ Ψ q)
      (volume : Measure E3) := by
  have hReM : Measurable (fun p : E3 × Submission.BoseGases.X n =>
      Work.BoseFixB1.boxTauAnnGen volA Ac
        (Work.BoseFixB1.boxWinModeReGen volA Ac χ p.1) Ψ p.2) :=
    Work.BoseFixB1.measurable_boxTauAnnGen_param volA hAcm
      (Work.BoseFixB1.measurable_boxWinModeReGen_uncurry hAcm hχc) hΨc.measurable
  have hRe : StronglyMeasurable (fun q : E3 => ∫ x,
      (Work.BoseFixB1.boxTauAnnGen volA Ac (Work.BoseFixB1.boxWinModeReGen volA Ac χ q) Ψ x) ^ 2
        ∂((volume : Measure (Submission.BoseGases.X n)).restrict
            (Submission.BoseGases.abox n a))) :=
    hReM.pow_const 2 |>.stronglyMeasurable |>.integral_prod_right'
      (ν := (volume : Measure (Submission.BoseGases.X n)).restrict
        (Submission.BoseGases.abox n a))
  have hImM : Measurable (fun p : E3 × Submission.BoseGases.X n =>
      Work.BoseFixB1.boxTauAnnGen volA Ac
        (Work.BoseFixB1.boxWinModeImGen volA Ac χ p.1) Ψ p.2) :=
    Work.BoseFixB1.measurable_boxTauAnnGen_param volA hAcm
      (Work.BoseFixB1.measurable_boxWinModeImGen_uncurry hAcm hχc) hΨc.measurable
  have hIm : StronglyMeasurable (fun q : E3 => ∫ x,
      (Work.BoseFixB1.boxTauAnnGen volA Ac (Work.BoseFixB1.boxWinModeImGen volA Ac χ q) Ψ x) ^ 2
        ∂((volume : Measure (Submission.BoseGases.X n)).restrict
            (Submission.BoseGases.abox n a))) :=
    hImM.pow_const 2 |>.stronglyMeasurable |>.integral_prod_right'
      (ν := (volume : Measure (Submission.BoseGases.X n)).restrict
        (Submission.BoseGases.abox n a))
  have hgoal : (fun q : E3 => Work.BoseFixB1.boxWinModePGen a volA Ac χ Ψ q)
      = fun q : E3 => (∫ x,
            (Work.BoseFixB1.boxTauAnnGen volA Ac
              (Work.BoseFixB1.boxWinModeReGen volA Ac χ q) Ψ x) ^ 2
              ∂((volume : Measure (Submission.BoseGases.X n)).restrict
                (Submission.BoseGases.abox n a)))
          + (∫ x,
            (Work.BoseFixB1.boxTauAnnGen volA Ac
              (Work.BoseFixB1.boxWinModeImGen volA Ac χ q) Ψ x) ^ 2
              ∂((volume : Measure (Submission.BoseGases.X n)).restrict
                (Submission.BoseGases.abox n a))) := by
    funext q
    simp only [Work.BoseFixB1.boxWinModePGen, Work.BoseFixB1.boxModePGen]
  rw [hgoal]
  exact (hRe.add hIm).aestronglyMeasurable

/-! ## 0b. The pointwise slot bound, in a clash-free cone

The corpus's `Work.BoseFixB1.boxWinModePGen_le_slotSum` (and everything needed for it:
`frameIntegrand_le` for `n` slots, `boxWinModePGen_eq_integral_frameIntegrand`,
`abs_boxWinModeReGen_le`, …) lives in a module that is *incompatible* with the consumer's
import point `Submission.Work.BoseFixB1B.pairRungImports` (the duplicate declaration
`Work.BoseFixB1.exists_bound_abox`).  The pieces below therefore re-derive the bound using only
clash-free modules.

The content is the sharp slot Cauchy–Schwarz for one mode `g`,

`(boxTauAnnGen volA Ac g Ψ x)² ≤ volA⁻¹·n·Σ_i 1_{Ac}(x_i)·(∫_{Ac} g z Ψ(x_{i←z}) dz)²`,

followed by the slot peel `volA⁻¹∫_x 1_{Ac}(x_i)G = (a³)⁻¹∫_x G` (corpus, clash-free:
`slotInvariant_indicator_integral`) and the amplitude dictionary
`‖tBamp χ q (Q_{Ac,i}Ψ) i x‖² = (∫Re·Ψ)² + (∫Im·Ψ)²` (corpus, clash-free:
`tBamp_boxQInd_normSq`). -/

/-- The restricted box measure of `Ac ⊆ acube a` is finite. -/
private lemma isFiniteMeasure_restrict_acube {a : ℝ} (ha : 0 < a) {Ac : Set E3}
    (hAc : Ac ⊆ Submission.BoseGases.acube a) :
    IsFiniteMeasure ((volume : Measure E3).restrict Ac) := by
  refine ⟨?_⟩
  rw [Measure.restrict_apply_univ]
  exact lt_of_le_of_lt (measure_mono hAc) (Submission.BoseGases.acube_lt_top a ha.le)

/-- **The mode bound.**  For a unit-bounded continuous `f` and a window `χ` with `0 ≤ χ ≤ κ`,
the mean-free windowed mode is bounded by `2κ`. -/
lemma abs_modeMeanFree_le {a volA κ : ℝ} (ha : 0 < a) (hvolpos : 0 < volA)
    {Ac : Set E3} (hAcm : MeasurableSet Ac) (hAc : Ac ⊆ Submission.BoseGases.acube a)
    (hvol : volA = (volume Ac).toReal)
    {χ f : E3 → ℝ} (hχc : Continuous χ) (hfc : Continuous f) (hf1 : ∀ z, |f z| ≤ 1)
    (hχnn : ∀ z, 0 ≤ χ z) (hκ0 : 0 ≤ κ) (hκ : ∀ z, χ z ≤ κ) (z : E3) :
    |Ac.indicator (fun _ => (1 : ℝ)) z * (χ z * f z - volA⁻¹ * ∫ w in Ac, χ w * f w)|
      ≤ 2 * κ := by
  haveI : IsFiniteMeasure ((volume : Measure E3).restrict Ac) :=
    isFiniteMeasure_restrict_acube ha hAc
  have hc : |∫ w in Ac, χ w * f w| ≤ κ * volA := by
    have hb : ∀ w ∈ Ac, |χ w * f w| ≤ κ := by
      intro w _
      rw [abs_mul, abs_of_nonneg (hχnn w)]
      calc χ w * |f w| ≤ κ * 1 := mul_le_mul (hκ w) (hf1 w) (abs_nonneg _) hκ0
        _ = κ := mul_one κ
    have hInt : IntegrableOn (fun w : E3 => χ w * f w) Ac volume :=
      ((hχc.mul hfc).continuousOn.integrableOn_compact
        (Submission.BoseGases.acube_compact ha)).mono_set hAc
    calc |∫ w in Ac, χ w * f w| ≤ ∫ w in Ac, |χ w * f w| := abs_integral_le_integral_abs
      _ ≤ ∫ _w in Ac, (κ : ℝ) := by
          refine integral_mono_of_nonneg (Eventually.of_forall fun w => abs_nonneg _)
            (integrable_const κ) ((ae_restrict_iff' hAcm).mpr (Eventually.of_forall fun w _ => hb w ‹_›))
      _ = κ * volA := by
          rw [MeasureTheory.setIntegral_const, Measure.real_def, ← hvol]
          rw [smul_eq_mul, mul_comm]
  by_cases hz : z ∈ Ac
  · rw [Set.indicator_of_mem hz, one_mul]
    have h1 : |χ z * f z| ≤ κ := by
      rw [abs_mul, abs_of_nonneg (hχnn z)]
      calc χ z * |f z| ≤ κ * 1 := mul_le_mul (hκ z) (hf1 z) (abs_nonneg _) hκ0
        _ = κ := mul_one κ
    have h2 : |volA⁻¹ * ∫ w in Ac, χ w * f w| ≤ κ := by
      rw [abs_mul, abs_of_nonneg (inv_nonneg.mpr hvolpos.le)]
      calc volA⁻¹ * |∫ w in Ac, χ w * f w| ≤ volA⁻¹ * (κ * volA) :=
            mul_le_mul_of_nonneg_left hc (inv_nonneg.mpr hvolpos.le)
        _ = κ := by
            rw [inv_mul_eq_iff_eq_mul₀ (ne_of_gt hvolpos)]
            ring
    calc |χ z * f z - volA⁻¹ * ∫ w in Ac, χ w * f w|
        ≤ |χ z * f z| + |volA⁻¹ * ∫ w in Ac, χ w * f w| := abs_sub _ _
      _ ≤ κ + κ := add_le_add h1 h2
      _ = 2 * κ := by ring
  · rw [Set.indicator_of_notMem hz, zero_mul, abs_zero]
    linarith

/-- The genuine real windowed mode is bounded by `2κ`. -/
private lemma abs_boxWinModeReGen_le_twoK {a volA κ : ℝ} (ha : 0 < a) (hvolpos : 0 < volA)
    {Ac : Set E3} (hAcm : MeasurableSet Ac) (hAc : Ac ⊆ Submission.BoseGases.acube a)
    (hvol : volA = (volume Ac).toReal)
    {χ : E3 → ℝ} (hχc : Continuous χ) (hχnn : ∀ z, 0 ≤ χ z)
    (hκ0 : 0 ≤ κ) (hκ : ∀ z, χ z ≤ κ) (q z : E3) :
    |Work.BoseFixB1.boxWinModeReGen volA Ac χ q z| ≤ 2 * κ :=
  abs_modeMeanFree_le ha hvolpos hAcm hAc hvol hχc
    (Real.continuous_cos.comp (continuous_const.inner continuous_id)) (fun w => Real.abs_cos_le_one _)
    hχnn hκ0 hκ z

/-- The genuine imaginary windowed mode is bounded by `2κ`. -/
private lemma abs_boxWinModeImGen_le_twoK {a volA κ : ℝ} (ha : 0 < a) (hvolpos : 0 < volA)
    {Ac : Set E3} (hAcm : MeasurableSet Ac) (hAc : Ac ⊆ Submission.BoseGases.acube a)
    (hvol : volA = (volume Ac).toReal)
    {χ : E3 → ℝ} (hχc : Continuous χ) (hχnn : ∀ z, 0 ≤ χ z)
    (hκ0 : 0 ≤ κ) (hκ : ∀ z, χ z ≤ κ) (q z : E3) :
    |Work.BoseFixB1.boxWinModeImGen volA Ac χ q z| ≤ 2 * κ := by
  rw [Work.BoseFixB1.boxWinModeImGen, abs_neg]
  exact abs_modeMeanFree_le ha hvolpos hAcm hAc hvol hχc
    (Real.continuous_sin.comp (continuous_const.inner continuous_id))
    (fun w => Real.abs_sin_le_one _) hχnn hκ0 hκ z

/-- **The sharp slot Cauchy–Schwarz for one mode.** -/
lemma boxTauAnnGen_sq_le_card {n : ℕ} {volA : ℝ} (hvolpos : 0 < volA)
    {Ac : Set E3} {g : E3 → ℝ} {Ψ : Submission.BoseGases.X n → ℝ}
    (x : Submission.BoseGases.X n) :
    (Work.BoseFixB1.boxTauAnnGen volA Ac g Ψ x) ^ 2
      ≤ volA⁻¹ * (n : ℝ) * ∑ i : Fin n, Ac.indicator (fun _ => (1 : ℝ)) (x i)
          * (∫ z in Ac, g z * Ψ (Function.update x i z)) ^ 2 := by
  have hsq : (Real.sqrt volA)⁻¹ ^ 2 = volA⁻¹ := by rw [inv_pow, Real.sq_sqrt hvolpos.le]
  have hidem : ∀ (i : Fin n) (y : ℝ),
      (Ac.indicator (fun _ => (1 : ℝ)) (x i) * y) ^ 2
        = Ac.indicator (fun _ => (1 : ℝ)) (x i) * y ^ 2 := by
    intro i y
    by_cases h : x i ∈ Ac
    · rw [Set.indicator_of_mem h, one_mul, one_mul]
    · rw [Set.indicator_of_notMem h]; ring
  have hcs := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (Fin n)))
    (f := fun i : Fin n => Ac.indicator (fun _ => (1 : ℝ)) (x i) *
      ∫ z in Ac, g z * Ψ (Function.update x i z))
  rw [Finset.card_fin] at hcs
  push_cast at hcs
  have hsumeq : (∑ i : Fin n, (Ac.indicator (fun _ => (1 : ℝ)) (x i) *
        ∫ z in Ac, g z * Ψ (Function.update x i z)) ^ 2)
      = ∑ i : Fin n, Ac.indicator (fun _ => (1 : ℝ)) (x i) *
          (∫ z in Ac, g z * Ψ (Function.update x i z)) ^ 2 :=
    Finset.sum_congr rfl (fun i _ => hidem i _)
  calc (Work.BoseFixB1.boxTauAnnGen volA Ac g Ψ x) ^ 2
      = volA⁻¹ * (∑ i : Fin n, (Ac.indicator (fun _ => (1 : ℝ)) (x i) *
            ∫ z in Ac, g z * Ψ (Function.update x i z))) ^ 2 := by
        rw [Work.BoseFixB1.boxTauAnnGen, mul_pow, hsq]
    _ ≤ volA⁻¹ * ((n : ℝ) * ∑ i : Fin n, (Ac.indicator (fun _ => (1 : ℝ)) (x i) *
            ∫ z in Ac, g z * Ψ (Function.update x i z)) ^ 2) :=
        mul_le_mul_of_nonneg_left (by simpa using hcs) (inv_nonneg.mpr hvolpos.le)
    _ = volA⁻¹ * (n : ℝ) * ∑ i : Fin n, Ac.indicator (fun _ => (1 : ℝ)) (x i) *
          (∫ z in Ac, g z * Ψ (Function.update x i z)) ^ 2 := by
        rw [hsumeq]; ring

/-- **The slot amplitude is bounded.** -/
lemma abs_slotAmp_le {n : ℕ} {a volA M CΨ : ℝ} (ha : 0 < a) (hvolpos : 0 < volA)
    (hM0 : 0 ≤ M) {Ac : Set E3} (hAcm : MeasurableSet Ac)
    (hAc : Ac ⊆ Submission.BoseGases.acube a) (hvol : volA = (volume Ac).toReal)
    {g : E3 → ℝ} (hgm : Measurable g) (hg : ∀ z, |g z| ≤ M)
    {Ψ : Submission.BoseGases.X n → ℝ} (hΨ : Continuous Ψ)
    (hCΨ : ∀ x ∈ Submission.BoseGases.abox n a, |Ψ x| ≤ CΨ) (hCΨ0 : 0 ≤ CΨ)
    {x : Submission.BoseGases.X n} (hx : x ∈ Submission.BoseGases.abox n a) (i : Fin n) :
    |∫ z in Ac, g z * Ψ (Function.update x i z)| ≤ M * CΨ * volA := by
  haveI : IsFiniteMeasure ((volume : Measure E3).restrict Ac) :=
    isFiniteMeasure_restrict_acube ha hAc
  have hb : ∀ z ∈ Ac, |g z * Ψ (Function.update x i z)| ≤ M * CΨ := by
    intro z hz
    rw [abs_mul]
    exact mul_le_mul (hg z) (hCΨ _ (Submission.BoseGases.update_mem_abox i hx (hAc hz)))
      (abs_nonneg _) hM0
  have haesm : AEStronglyMeasurable (fun z : E3 => g z * Ψ (Function.update x i z))
      ((volume : Measure E3).restrict Ac) :=
    (hgm.mul (hΨ.measurable.comp (measurable_update (f := x) (a := i)))).aestronglyMeasurable
  have hInt : IntegrableOn (fun z : E3 => g z * Ψ (Function.update x i z)) Ac volume :=
    IntegrableOn.of_bound
      (lt_of_le_of_lt (measure_mono hAc) (Submission.BoseGases.acube_lt_top a ha.le))
      haesm (M * CΨ) ((ae_restrict_iff' hAcm).mpr (Eventually.of_forall fun z hz => hb z hz))
  calc |∫ z in Ac, g z * Ψ (Function.update x i z)|
      ≤ ∫ z in Ac, |g z * Ψ (Function.update x i z)| := abs_integral_le_integral_abs
    _ ≤ ∫ _z in Ac, (M * CΨ) := by
        refine integral_mono_of_nonneg (Eventually.of_forall fun z => abs_nonneg _)
          (integrable_const _) ((ae_restrict_iff' hAcm).mpr (Eventually.of_forall fun z hz => hb z hz))
    _ = M * CΨ * volA := by
        rw [MeasureTheory.setIntegral_const, Measure.real_def, ← hvol, smul_eq_mul]
        ring

/-- The square of the slot amplitude is integrable on the box. -/
lemma integrableOn_slotAmp_sq {n : ℕ} {a volA M CΨ : ℝ} (ha : 0 < a) (hvolpos : 0 < volA)
    (hM0 : 0 ≤ M) {Ac : Set E3} (hAcm : MeasurableSet Ac)
    (hAc : Ac ⊆ Submission.BoseGases.acube a) (hvol : volA = (volume Ac).toReal)
    {g : E3 → ℝ} (hgm : Measurable g) (hg : ∀ z, |g z| ≤ M)
    {Ψ : Submission.BoseGases.X n → ℝ} (hΨ : Continuous Ψ)
    (hCΨ : ∀ x ∈ Submission.BoseGases.abox n a, |Ψ x| ≤ CΨ) (hCΨ0 : 0 ≤ CΨ) (i : Fin n) :
    IntegrableOn (fun x : Submission.BoseGases.X n =>
      (∫ z in Ac, g z * Ψ (Function.update x i z)) ^ 2)
      (Submission.BoseGases.abox n a) volume := by
  have hmeas : Measurable (fun x : Submission.BoseGases.X n =>
      ∫ z in Ac, g z * Ψ (Function.update x i z)) :=
    Work.BoseFixB1.measurable_setIntegral_param hAcm (by
      refine (hgm.comp measurable_snd).mul ?_
      exact hΨ.measurable.comp measurable_update')
  refine IntegrableOn.of_bound (Submission.BoseGases.abox_lt_top n a ha.le)
    ((hmeas.pow_const 2).aestronglyMeasurable) ((M * CΨ * volA) ^ 2) ?_
  filter_upwards [MeasureTheory.ae_restrict_mem (Submission.BoseGases.abox_measurable n a)]
    with x hx
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), ← sq_abs]
  exact pow_le_pow_left₀ (abs_nonneg _)
    (abs_slotAmp_le ha hvolpos hM0 hAcm hAc hvol hgm hg hΨ hCΨ hCΨ0 hx i) 2

/-- **The per-mode slot bound.** -/
theorem boxModePGen_le_slotAmpSum {n : ℕ} {a volA M CΨ : ℝ} (ha : 0 < a)
    (hvolpos : 0 < volA) (hM0 : 0 ≤ M) {Ac : Set E3} (hAcm : MeasurableSet Ac)
    (hAc : Ac ⊆ Submission.BoseGases.acube a) (hvol : volA = (volume Ac).toReal)
    {g : E3 → ℝ} (hgm : Measurable g) (hg : ∀ z, |g z| ≤ M)
    {Ψ : Submission.BoseGases.X n → ℝ} (hΨ : Continuous Ψ)
    (hCΨ : ∀ x ∈ Submission.BoseGases.abox n a, |Ψ x| ≤ CΨ) (hCΨ0 : 0 ≤ CΨ) :
    Work.BoseFixB1.boxModePGen a volA Ac g Ψ
      ≤ (n : ℝ) * ∑ i : Fin n, (a ^ 3)⁻¹ *
          ∫ x in Submission.BoseGases.abox n a,
            (∫ z in Ac, g z * Ψ (Function.update x i z)) ^ 2 := by
  have hvolAne : volA ≠ 0 := ne_of_gt hvolpos
  have hAmpInt : ∀ i : Fin n, IntegrableOn (fun x : Submission.BoseGases.X n =>
      (∫ z in Ac, g z * Ψ (Function.update x i z)) ^ 2)
      (Submission.BoseGases.abox n a) volume :=
    fun i => integrableOn_slotAmp_sq ha hvolpos hM0 hAcm hAc hvol hgm hg hΨ hCΨ hCΨ0 i
  have hwInt : ∀ i : Fin n, IntegrableOn (fun x : Submission.BoseGases.X n =>
      Ac.indicator (fun _ => (1 : ℝ)) (x i) *
        (∫ z in Ac, g z * Ψ (Function.update x i z)) ^ 2)
      (Submission.BoseGases.abox n a) volume := by
    intro i
    refine (hAmpInt i).bdd_mul ?_ (c := 1) ?_
    · exact ((measurable_const.indicator hAcm).comp (measurable_pi_apply i)).aestronglyMeasurable
    · filter_upwards with x
      by_cases h : x i ∈ Ac
      · rw [Set.indicator_of_mem h]; norm_num
      · rw [Set.indicator_of_notMem h]; norm_num
  have hmajInt : IntegrableOn (fun x : Submission.BoseGases.X n => volA⁻¹ * ((n : ℝ) *
      ∑ i : Fin n, Ac.indicator (fun _ => (1 : ℝ)) (x i) *
        (∫ z in Ac, g z * Ψ (Function.update x i z)) ^ 2))
      (Submission.BoseGases.abox n a) volume :=
    ((integrable_finsetSum _ (fun i _ => hwInt i)).const_mul (n : ℝ)).const_mul volA⁻¹
  have hpoint : ∀ᵐ x ∂((volume : Measure (Submission.BoseGases.X n)).restrict
      (Submission.BoseGases.abox n a)), (Work.BoseFixB1.boxTauAnnGen volA Ac g Ψ x) ^ 2
      ≤ volA⁻¹ * ((n : ℝ) * ∑ i : Fin n, Ac.indicator (fun _ => (1 : ℝ)) (x i) *
          (∫ z in Ac, g z * Ψ (Function.update x i z)) ^ 2) :=
    (ae_restrict_iff' (Submission.BoseGases.abox_measurable n a)).mpr
      (Eventually.of_forall fun x _ =>
        (boxTauAnnGen_sq_le_card (n := n) (volA := volA) hvolpos (Ac := Ac) (g := g) (Ψ := Ψ) x
          ).trans (le_of_eq (by rw [mul_assoc])))
  have hmono := integral_mono_of_nonneg
    (f := fun x : Submission.BoseGases.X n => (Work.BoseFixB1.boxTauAnnGen volA Ac g Ψ x) ^ 2)
    (g := fun x : Submission.BoseGases.X n => volA⁻¹ * ((n : ℝ) * ∑ i : Fin n,
        Ac.indicator (fun _ => (1 : ℝ)) (x i) *
          (∫ z in Ac, g z * Ψ (Function.update x i z)) ^ 2))
    (Eventually.of_forall fun x => sq_nonneg _) hmajInt hpoint
  rw [Work.BoseFixB1.boxModePGen]
  refine hmono.trans (le_of_eq ?_)
  have hpeel : ∀ i : Fin n, (∫ x in Submission.BoseGases.abox n a,
        Ac.indicator (fun _ => (1 : ℝ)) (x i) *
          (∫ z in Ac, g z * Ψ (Function.update x i z)) ^ 2)
      = volA * ((a ^ 3)⁻¹ * ∫ x in Submission.BoseGases.abox n a,
          (∫ z in Ac, g z * Ψ (Function.update x i z)) ^ 2) := by
    intro i
    have hinv := Work.BoseFixB1.slotInvariant_indicator_integral (n := n) (a := a) (volA := volA)
      ha hvolpos hAcm hAc hvol i
      (G := fun x : Submission.BoseGases.X n => (∫ z in Ac, g z * Ψ (Function.update x i z)) ^ 2)
      (fun x t => by simp only [Function.update_idem]) (hAmpInt i)
    calc (∫ x in Submission.BoseGases.abox n a,
          Ac.indicator (fun _ => (1 : ℝ)) (x i) *
            (∫ z in Ac, g z * Ψ (Function.update x i z)) ^ 2)
        = volA * (volA⁻¹ * (∫ x in Submission.BoseGases.abox n a,
            Ac.indicator (fun _ => (1 : ℝ)) (x i) *
              (∫ z in Ac, g z * Ψ (Function.update x i z)) ^ 2)) := by
          rw [← mul_assoc, mul_inv_cancel₀ hvolAne, one_mul]
      _ = volA * ((a ^ 3)⁻¹ * ∫ x in Submission.BoseGases.abox n a,
            (∫ z in Ac, g z * Ψ (Function.update x i z)) ^ 2) := by rw [hinv]
  rw [MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul,
    MeasureTheory.integral_finsetSum _ (fun i _ => hwInt i)]
  have hsum : (∑ i : Fin n, ∫ x in Submission.BoseGases.abox n a,
        Ac.indicator (fun _ => (1 : ℝ)) (x i) *
          (∫ z in Ac, g z * Ψ (Function.update x i z)) ^ 2)
      = ∑ i : Fin n, volA * ((a ^ 3)⁻¹ * ∫ x in Submission.BoseGases.abox n a,
          (∫ z in Ac, g z * Ψ (Function.update x i z)) ^ 2) :=
    Finset.sum_congr rfl (fun i _ => hpeel i)
  rw [hsum]
  rw [← Finset.mul_sum]
  have key : ∀ S : ℝ, volA⁻¹ * ((n : ℝ) * (volA * S)) = (n : ℝ) * S := by
    intro S
    calc volA⁻¹ * ((n : ℝ) * (volA * S)) = (volA⁻¹ * volA) * ((n : ℝ) * S) := by ring
      _ = (n : ℝ) * S := by rw [inv_mul_cancel₀ hvolAne, one_mul]
  exact key _

/-- **The pointwise slot bound** for the genuine windowed mode content. -/
theorem boxWinModePGen_le_slotSum_clean {n : ℕ} {a volA κ CΨ : ℝ} (ha : 0 < a)
    (hvolpos : 0 < volA) (hκ0 : 0 ≤ κ) {Ac : Set E3} (hAcm : MeasurableSet Ac)
    (hAc : Ac ⊆ Submission.BoseGases.acube a) (hvol : volA = (volume Ac).toReal)
    {χ : E3 → ℝ} (hχc : Continuous χ) (hχs : HasCompactSupport χ)
    (hχnn : ∀ z, 0 ≤ χ z) (hκ : ∀ z, χ z ≤ κ)
    {Ψ : Submission.BoseGases.X n → ℝ} (hΨ : Continuous Ψ)
    (hCΨ : ∀ x ∈ Submission.BoseGases.abox n a, |Ψ x| ≤ CΨ) (hCΨ0 : 0 ≤ CΨ)
    (q : E3) :
    Work.BoseFixB1.boxWinModePGen a volA Ac χ Ψ q
      ≤ (n : ℝ) * ∑ i : Fin n, (a ^ 3)⁻¹ *
          ∫ x in Submission.BoseGases.abox n a,
            ‖Work.SmallBoxTBWord.tBamp χ q (Work.UBBInputs8.boxQInd volA Ac i Ψ) i x‖ ^ 2 := by
  set M : ℝ := 2 * κ with hMdef
  have hM0 : 0 ≤ M := by rw [hMdef]; linarith
  have hReMeas : Measurable (Work.BoseFixB1.boxWinModeReGen volA Ac χ q) :=
    (Work.BoseFixB1.measurable_boxWinModeReGen_uncurry hAcm hχc).comp
      (measurable_const.prodMk measurable_id)
  have hImMeas : Measurable (Work.BoseFixB1.boxWinModeImGen volA Ac χ q) :=
    (Work.BoseFixB1.measurable_boxWinModeImGen_uncurry hAcm hχc).comp
      (measurable_const.prodMk measurable_id)
  have hRe := boxModePGen_le_slotAmpSum (n := n) ha hvolpos hM0 hAcm hAc hvol
    (g := Work.BoseFixB1.boxWinModeReGen volA Ac χ q) hReMeas
    (fun z => abs_boxWinModeReGen_le_twoK ha hvolpos hAcm hAc hvol hχc hχnn hκ0 hκ q z)
    hΨ hCΨ hCΨ0
  have hIm := boxModePGen_le_slotAmpSum (n := n) ha hvolpos hM0 hAcm hAc hvol
    (g := Work.BoseFixB1.boxWinModeImGen volA Ac χ q) hImMeas
    (fun z => abs_boxWinModeImGen_le_twoK ha hvolpos hAcm hAc hvol hχc hχnn hκ0 hκ q z)
    hΨ hCΨ hCΨ0
  have hAmpReInt : ∀ i : Fin n, IntegrableOn (fun x : Submission.BoseGases.X n =>
      (∫ z in Ac, Work.BoseFixB1.boxWinModeReGen volA Ac χ q z * Ψ (Function.update x i z)) ^ 2)
      (Submission.BoseGases.abox n a) volume :=
    fun i => integrableOn_slotAmp_sq ha hvolpos hM0 hAcm hAc hvol hReMeas
      (fun z => abs_boxWinModeReGen_le_twoK ha hvolpos hAcm hAc hvol hχc hχnn hκ0 hκ q z)
      hΨ hCΨ hCΨ0 i
  have hAmpImInt : ∀ i : Fin n, IntegrableOn (fun x : Submission.BoseGases.X n =>
      (∫ z in Ac, Work.BoseFixB1.boxWinModeImGen volA Ac χ q z * Ψ (Function.update x i z)) ^ 2)
      (Submission.BoseGases.abox n a) volume :=
    fun i => integrableOn_slotAmp_sq ha hvolpos hM0 hAcm hAc hvol hImMeas
      (fun z => abs_boxWinModeImGen_le_twoK ha hvolpos hAcm hAc hvol hχc hχnn hκ0 hκ q z)
      hΨ hCΨ hCΨ0 i
  have hXY : ∀ i : Fin n,
      (∫ x in Submission.BoseGases.abox n a,
          (∫ z in Ac, Work.BoseFixB1.boxWinModeReGen volA Ac χ q z
            * Ψ (Function.update x i z)) ^ 2)
        + (∫ x in Submission.BoseGases.abox n a,
          (∫ z in Ac, Work.BoseFixB1.boxWinModeImGen volA Ac χ q z
            * Ψ (Function.update x i z)) ^ 2)
      = ∫ x in Submission.BoseGases.abox n a,
          ‖Work.SmallBoxTBWord.tBamp χ q (Work.UBBInputs8.boxQInd volA Ac i Ψ) i x‖ ^ 2 := by
    intro i
    rw [← MeasureTheory.integral_add (hAmpReInt i) (hAmpImInt i)]
    refine MeasureTheory.integral_congr_ae ?_
    filter_upwards [MeasureTheory.ae_restrict_mem (Submission.BoseGases.abox_measurable n a)]
      with x hx
    exact (Work.BoseFixB1.tBamp_boxQInd_normSq ha hvolpos hAcm hAc hχc hχs hΨ i hx q).symm
  rw [Work.BoseFixB1.boxWinModePGen, Work.BoseFixB1.boxModePGen, Work.BoseFixB1.boxModePGen]
  refine (add_le_add hRe hIm).trans (le_of_eq ?_)
  show (n : ℝ) * (∑ i : Fin n, (a ^ 3)⁻¹ * ∫ x in Submission.BoseGases.abox n a,
        (∫ z in Ac, Work.BoseFixB1.boxWinModeReGen volA Ac χ q z
          * Ψ (Function.update x i z)) ^ 2)
      + (n : ℝ) * (∑ i : Fin n, (a ^ 3)⁻¹ * ∫ x in Submission.BoseGases.abox n a,
        (∫ z in Ac, Work.BoseFixB1.boxWinModeImGen volA Ac χ q z
          * Ψ (Function.update x i z)) ^ 2)
    = (n : ℝ) * ∑ i : Fin n, (a ^ 3)⁻¹ * ∫ x in Submission.BoseGases.abox n a,
        ‖Work.SmallBoxTBWord.tBamp χ q (Work.UBBInputs8.boxQInd volA Ac i Ψ) i x‖ ^ 2
  rw [← mul_add, ← Finset.sum_add_distrib]
  congr 1
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [← mul_add, hXY i]

/-! ## 1. The measure-theoretic core -/

/-- **The `q`-integration step.**  If the sharp pointwise (in `q`) slot bound holds for the
windowed mode content, and each `p`-integrand on the right is integrable, then the weighted
`q`-integral inequality follows with the slot count as constant. -/
theorem winModeContentLeWord_of_pointwise {n : ℕ} {a volA : ℝ} (ha : 0 < a)
    {Ac : Set E3} (hAcm : MeasurableSet Ac) (hAcsub : Ac ⊆ Submission.BoseGases.acube a)
    (hvol : volA = (volume Ac).toReal) (hvolpos : 0 < volA)
    {χ : E3 → ℝ} (hχc : Continuous χ)
    {c₀ : ℝ} (hc₀ : 0 < c₀)
    {Ψ : Submission.BoseGases.X n → ℝ} (hΨc : Continuous Ψ)
    (hpoint : ∀ q : E3, Work.BoseFixB1.boxWinModePGen a volA Ac χ Ψ q
      ≤ (n : ℝ) * ∑ i : Fin n, (a ^ 3)⁻¹ *
          ∫ x in Submission.BoseGases.abox n a,
            ‖Work.SmallBoxTBWord.tBamp χ q (Work.UBBInputs8.boxQInd volA Ac i Ψ) i x‖ ^ 2)
    (hint : ∀ i : Fin n, Integrable (fun p : E3 =>
      Submission.BoseGases.fsKinCoeff c₀ ‖p‖ * ((a ^ 3)⁻¹ *
        ∫ x in Submission.BoseGases.abox n a,
          ‖Work.SmallBoxTBWord.tBamp χ p (Work.UBBInputs8.boxQInd volA Ac i Ψ) i x‖ ^ 2))) :
    ((2 * Real.pi) ^ 3)⁻¹ * (∫ q : E3,
        Submission.BoseGases.fsKinCoeff c₀ ‖q‖ * Work.BoseFixB1.boxWinModePGen a volA Ac χ Ψ q)
      ≤ (n : ℝ) * Work.UBBInputs8.tBdiagFormInd a Ac volA χ
          (Submission.BoseGases.fsKinCoeff c₀) Ψ := by
  classical
  set F : E3 → ℝ := fun q => Submission.BoseGases.fsKinCoeff c₀ ‖q‖ with hF
  set P : E3 → ℝ := fun q => Work.BoseFixB1.boxWinModePGen a volA Ac χ Ψ q with hP
  have htwoπ : (0 : ℝ) < (2 * Real.pi) ^ 3 := by positivity
  have htwoπne : (2 * Real.pi) ^ 3 ≠ 0 := ne_of_gt htwoπ
  have hFnn : ∀ q : E3, 0 ≤ F q := fun q => Submission.BoseGases.fsKinCoeff_nonneg c₀ ‖q‖
  have hFcont : Continuous F := by
    rw [hF]
    simp only [Submission.BoseGases.fsKinCoeff]
    fun_prop
  have hPnn : ∀ q : E3, 0 ≤ P q := by
    intro q
    rw [hP]
    simp only [Work.BoseFixB1.boxWinModePGen, Work.BoseFixB1.boxModePGen]
    exact add_nonneg (integral_nonneg fun x => sq_nonneg _)
      (integral_nonneg fun x => sq_nonneg _)
  have hPmeas : AEStronglyMeasurable P (volume : Measure E3) := by
    rw [hP]
    exact aeStronglyMeasurable_boxWinModePGen hAcm hχc hΨc
  -- ### non-negativity of the slot terms
  have hApnn : ∀ (i : Fin n) (p : E3), 0 ≤ (a ^ 3)⁻¹ *
      ∫ x in Submission.BoseGases.abox n a,
        ‖Work.SmallBoxTBWord.tBamp χ p (Work.UBBInputs8.boxQInd volA Ac i Ψ) i x‖ ^ 2 :=
    fun i p => mul_nonneg (by positivity) (integral_nonneg fun x => sq_nonneg _)
  -- ### integrability of the right-hand integrand
  have hIntAp : ∀ i : Fin n, Integrable (fun p : E3 =>
      F p * ((a ^ 3)⁻¹ * ∫ x in Submission.BoseGases.abox n a,
        ‖Work.SmallBoxTBWord.tBamp χ p (Work.UBBInputs8.boxQInd volA Ac i Ψ) i x‖ ^ 2)) := by
    intro i
    rw [hF]
    exact hint i
  have hIntSum : Integrable (fun p : E3 => ∑ i : Fin n, F p * ((a ^ 3)⁻¹ *
      ∫ x in Submission.BoseGases.abox n a,
        ‖Work.SmallBoxTBWord.tBamp χ p (Work.UBBInputs8.boxQInd volA Ac i Ψ) i x‖ ^ 2)) :=
    integrable_finsetSum _ (fun i _ => hIntAp i)
  have hIntT : Integrable (fun p : E3 => F p * ∑ i : Fin n, (a ^ 3)⁻¹ *
      ∫ x in Submission.BoseGases.abox n a,
        ‖Work.SmallBoxTBWord.tBamp χ p (Work.UBBInputs8.boxQInd volA Ac i Ψ) i x‖ ^ 2) :=
    hIntSum.congr (Eventually.of_forall fun p =>
      (Finset.mul_sum Finset.univ
        (fun i : Fin n => (a ^ 3)⁻¹ * ∫ x in Submission.BoseGases.abox n a,
          ‖Work.SmallBoxTBWord.tBamp χ p (Work.UBBInputs8.boxQInd volA Ac i Ψ) i x‖ ^ 2)
        (F p)).symm)
  have hIntRight : Integrable (fun p : E3 => F p * ((n : ℝ) * ∑ i : Fin n, (a ^ 3)⁻¹ *
      ∫ x in Submission.BoseGases.abox n a,
        ‖Work.SmallBoxTBWord.tBamp χ p (Work.UBBInputs8.boxQInd volA Ac i Ψ) i x‖ ^ 2)) := by
    refine (hIntT.const_mul (n : ℝ)).congr (Eventually.of_forall fun p => ?_)
    show (n : ℝ) * (F p * ∑ i : Fin n, (a ^ 3)⁻¹ * ∫ x in Submission.BoseGases.abox n a,
        ‖Work.SmallBoxTBWord.tBamp χ p (Work.UBBInputs8.boxQInd volA Ac i Ψ) i x‖ ^ 2)
      = F p * ((n : ℝ) * ∑ i : Fin n, (a ^ 3)⁻¹ * ∫ x in Submission.BoseGases.abox n a,
        ‖Work.SmallBoxTBWord.tBamp χ p (Work.UBBInputs8.boxQInd volA Ac i Ψ) i x‖ ^ 2)
    ring
  -- ### integrability of the left-hand integrand
  have hpt : ∀ p : E3, P p ≤ (n : ℝ) * ∑ i : Fin n, (a ^ 3)⁻¹ *
      ∫ x in Submission.BoseGases.abox n a,
        ‖Work.SmallBoxTBWord.tBamp χ p (Work.UBBInputs8.boxQInd volA Ac i Ψ) i x‖ ^ 2 := by
    intro p
    rw [hP]
    exact hpoint p
  have hIntLeft : Integrable (fun p : E3 => F p * P p) :=
    Integrable.mono' hIntRight (hFcont.aestronglyMeasurable.mul hPmeas)
      (Eventually.of_forall fun p => by
        rw [Real.norm_of_nonneg (mul_nonneg (hFnn p) (hPnn p))]
        exact mul_le_mul_of_nonneg_left (hpt p) (hFnn p))
  -- ### monotonicity of the `q`-integral
  have hmono : (∫ p : E3, F p * P p)
      ≤ ∫ p : E3, F p * ((n : ℝ) * ∑ i : Fin n, (a ^ 3)⁻¹ *
          ∫ x in Submission.BoseGases.abox n a,
            ‖Work.SmallBoxTBWord.tBamp χ p (Work.UBBInputs8.boxQInd volA Ac i Ψ) i x‖ ^ 2) :=
    integral_mono hIntLeft hIntRight
      (fun p => mul_le_mul_of_nonneg_left (hpt p) (hFnn p))
  -- ### evaluation of the right-hand integral
  have hright : (∫ p : E3, F p * ((n : ℝ) * ∑ i : Fin n, (a ^ 3)⁻¹ *
        ∫ x in Submission.BoseGases.abox n a,
          ‖Work.SmallBoxTBWord.tBamp χ p (Work.UBBInputs8.boxQInd volA Ac i Ψ) i x‖ ^ 2))
      = (n : ℝ) * ((2 * Real.pi) ^ 3) * Work.UBBInputs8.tBdiagFormInd a Ac volA χ
          (Submission.BoseGases.fsKinCoeff c₀) Ψ := by
    have e1 : (fun p : E3 => F p * ((n : ℝ) * ∑ i : Fin n, (a ^ 3)⁻¹ *
          ∫ x in Submission.BoseGases.abox n a,
            ‖Work.SmallBoxTBWord.tBamp χ p (Work.UBBInputs8.boxQInd volA Ac i Ψ) i x‖ ^ 2))
        = fun p : E3 => (n : ℝ) * (F p * ∑ i : Fin n, (a ^ 3)⁻¹ *
          ∫ x in Submission.BoseGases.abox n a,
            ‖Work.SmallBoxTBWord.tBamp χ p (Work.UBBInputs8.boxQInd volA Ac i Ψ) i x‖ ^ 2) := by
      funext p
      ring
    rw [e1, MeasureTheory.integral_const_mul]
    have e2 : (fun p : E3 => F p * ∑ i : Fin n, (a ^ 3)⁻¹ *
          ∫ x in Submission.BoseGases.abox n a,
            ‖Work.SmallBoxTBWord.tBamp χ p (Work.UBBInputs8.boxQInd volA Ac i Ψ) i x‖ ^ 2)
        = fun p : E3 => ∑ i : Fin n, F p * ((a ^ 3)⁻¹ *
          ∫ x in Submission.BoseGases.abox n a,
            ‖Work.SmallBoxTBWord.tBamp χ p (Work.UBBInputs8.boxQInd volA Ac i Ψ) i x‖ ^ 2) := by
      funext p
      rw [Finset.mul_sum]
    rw [e2, MeasureTheory.integral_finsetSum _ (fun i _ => hIntAp i)]
    rw [Work.UBBInputs8.tBdiagFormInd]
    set X : Fin n → ℝ := fun i => ∫ p : E3, F p * ((a ^ 3)⁻¹ *
        ∫ x in Submission.BoseGases.abox n a,
          ‖Work.SmallBoxTBWord.tBamp χ p (Work.UBBInputs8.boxQInd volA Ac i Ψ) i x‖ ^ 2) with hX
    rw [Finset.mul_sum (s := Finset.univ) (f := X) (a := (n : ℝ))]
    rw [Finset.mul_sum (s := Finset.univ)
      (f := fun i : Fin n => ((2 * Real.pi) ^ 3)⁻¹ * X i)
      (a := (n : ℝ) * (2 * Real.pi) ^ 3)]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    field_simp
  -- ### assembly
  have hmain : (∫ p : E3, F p * P p)
      ≤ (n : ℝ) * ((2 * Real.pi) ^ 3) * Work.UBBInputs8.tBdiagFormInd a Ac volA χ
          (Submission.BoseGases.fsKinCoeff c₀) Ψ := hmono.trans (le_of_eq hright)
  have hgoal : ((2 * Real.pi) ^ 3)⁻¹ * (∫ q : E3, Submission.BoseGases.fsKinCoeff c₀ ‖q‖ *
        Work.BoseFixB1.boxWinModePGen a volA Ac χ Ψ q)
      = ((2 * Real.pi) ^ 3)⁻¹ * (∫ q : E3, F q * P q) := by
    rw [hF, hP]
  rw [hgoal]
  calc ((2 * Real.pi) ^ 3)⁻¹ * (∫ q : E3, F q * P q)
      ≤ ((2 * Real.pi) ^ 3)⁻¹ * ((n : ℝ) * ((2 * Real.pi) ^ 3) *
          Work.UBBInputs8.tBdiagFormInd a Ac volA χ (Submission.BoseGases.fsKinCoeff c₀) Ψ) :=
        mul_le_mul_of_nonneg_left hmain (by positivity)
    _ = (n : ℝ) * Work.UBBInputs8.tBdiagFormInd a Ac volA χ
          (Submission.BoseGases.fsKinCoeff c₀) Ψ := by
        field_simp

/-! ## 2. Integrability in `p` of the kinetic integrand -/

/-- The FS symbol is dominated by `2(r² + c₀²)`. -/
private lemma fsKinCoeff_le_two (c₀ r : ℝ) :
    Submission.BoseGases.fsKinCoeff c₀ r ≤ 2 * (r ^ 2 + c₀ ^ 2) := by
  rw [Submission.BoseGases.fsKinCoeff]
  by_cases h : r - c₀ ≤ 0
  · rw [max_eq_right h]
    nlinarith [sq_nonneg r, sq_nonneg c₀]
  · push_neg at h
    have hle : r - c₀ ≤ r + |c₀| := by
      have := neg_le_abs c₀
      linarith
    rw [max_eq_left h.le]
    calc (r - c₀) ^ 2 ≤ (r + |c₀|) ^ 2 := pow_le_pow_left₀ (by linarith) hle 2
      _ ≤ 2 * (r ^ 2 + c₀ ^ 2) := by nlinarith [sq_nonneg (r - |c₀|), sq_abs c₀]

/-- The model `(1+‖q‖)⁻⁴` is integrable in `ℝ³`. -/
private lemma integrable_one_add_norm_four_r3 :
    Integrable (fun q : E3 => (1 + ‖q‖) ^ (-(4 : ℝ))) volume :=
  integrable_one_add_norm (E := E3) (μ := volume) (r := 4)
    (by rw [finrank_euclideanSpace, Fintype.card_fin]; norm_num)

/-- **`p`-integrability of the kinetic integrand.**  With the FS support hypothesis `χ = 0` off
`Ac`, the windowed fibre of the box projection is the difference of two `(1+‖p‖)⁻³`-decaying
amplitudes (`Work.BoseBox.tBamp_boxQInd_eq_sub` + `Work.SmallBoxTBWord.tBamp_decay`); hence the
`p`-integrand is dominated by `(1+‖p‖)⁻⁴`, which is integrable in dimension three. -/
theorem integrableFsKinCoeff_tBamp_boxQIndN {n : ℕ} {a volA c₀ : ℝ} (ha : 0 < a)
    (hvolpos : 0 < volA) {Ac : Set E3} (hAcm : MeasurableSet Ac)
    (hAc : Ac ⊆ Submission.BoseGases.acube a) (hvol : volA = (volume Ac).toReal)
    {χ : E3 → ℝ} (hχc : ContDiff ℝ (⊤ : ℕ∞) χ) (hχs : HasCompactSupport χ)
    (hχsupp : ∀ z, z ∉ Ac → χ z = 0)
    {Ψ : Submission.BoseGases.X n → ℝ} (hΨc : ContDiff ℝ (⊤ : ℕ∞) Ψ) (i : Fin n) :
    Integrable (fun p : E3 => Submission.BoseGases.fsKinCoeff c₀ ‖p‖ * ((a ^ 3)⁻¹ *
      ∫ x in Submission.BoseGases.abox n a,
        ‖Work.SmallBoxTBWord.tBamp χ p (Work.UBBInputs8.boxQInd volA Ac i Ψ) i x‖ ^ 2)) := by
  classical
  obtain ⟨CΨ, hCΨ0, hCΨ⟩ := Work.BoseFixB1.exists_bound_abox_pos (ℓ := a) ha hΨc.continuous
  obtain ⟨C₁, hC₁0, hC₁⟩ := Work.SmallBoxTBWord.tBamp_decay (a := a) ha hχc hχs hΨc
  obtain ⟨C₂, hC₂0, hC₂⟩ := Work.SmallBoxTBWord.tBamp_decay (a := a) ha hχc hχs
    (Φ := fun _ : Submission.BoseGases.X n => (1 : ℝ)) contDiff_const
  -- ### the mean is bounded by `CΨ` on the box
  have hmeanx : ∀ x ∈ Submission.BoseGases.abox n a,
      |Work.SmallBoxTBWord.boxP volA Ac i Ψ x| ≤ CΨ := by
    intro x hx
    have hInt1 : |∫ z in Ac, (fun _ : E3 => (1 : ℝ)) z * Ψ (Function.update x i z)| ≤
        1 * CΨ * volA :=
      abs_slotAmp_le (n := n) ha hvolpos (by norm_num) hAcm hAc hvol
        measurable_const (fun z => by simp) hΨc.continuous hCΨ hCΨ0 hx i
    rw [Work.SmallBoxTBWord.boxP, one_div, abs_mul, abs_of_nonneg (inv_nonneg.mpr hvolpos.le)]
    calc volA⁻¹ * |∫ z in Ac, Ψ (Function.update x i z)|
        = volA⁻¹ * |∫ z in Ac, (fun _ : E3 => (1 : ℝ)) z * Ψ (Function.update x i z)| := by
          simp
      _ ≤ volA⁻¹ * (1 * CΨ * volA) := mul_le_mul_of_nonneg_left hInt1 (inv_nonneg.mpr hvolpos.le)
      _ = CΨ := by
          rw [inv_mul_eq_iff_eq_mul₀ (ne_of_gt hvolpos)]
          ring
  -- ### the uniform decay bound on the box
  have hdecay : ∀ x ∈ Submission.BoseGases.abox n a, ∀ p : E3,
      ‖Work.SmallBoxTBWord.tBamp χ p (Work.UBBInputs8.boxQInd volA Ac i Ψ) i x‖
        ≤ (C₁ + CΨ * C₂) / (1 + ‖p‖) ^ 3 := by
    intro x hx p
    have hsub := Work.BoseBox.tBamp_boxQInd_eq_sub (volA := volA) (A := Ac) (χ := χ) (N := n)
      Ψ i p x 0 hχsupp hχc.continuous hχs hΨc.continuous
    have hboxP : Work.SmallBoxTBWord.boxP volA Ac i Ψ (Function.update x i 0)
        = Work.SmallBoxTBWord.boxP volA Ac i Ψ x := by
      rw [Work.SmallBoxTBWord.boxP, Work.SmallBoxTBWord.boxP]
      congr 1
      apply MeasureTheory.integral_congr_ae
      filter_upwards with z
      rw [Function.update_idem]
    have h3 : ‖((Work.SmallBoxTBWord.boxP volA Ac i Ψ (Function.update x i 0) : ℝ) : ℂ)
        * Work.SmallBoxTBWord.tBamp χ p (fun _ : Submission.BoseGases.X n => (1 : ℝ)) i x‖
        ≤ CΨ * (C₂ / (1 + ‖p‖) ^ 3) := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, hboxP]
      exact mul_le_mul (hmeanx x hx) (hC₂ x hx i p) (norm_nonneg _) hCΨ0
    calc ‖Work.SmallBoxTBWord.tBamp χ p (Work.UBBInputs8.boxQInd volA Ac i Ψ) i x‖
        = ‖Work.SmallBoxTBWord.tBamp χ p Ψ i x
            - ((Work.SmallBoxTBWord.boxP volA Ac i Ψ (Function.update x i 0) : ℝ) : ℂ)
              * Work.SmallBoxTBWord.tBamp χ p
                  (fun _ : Submission.BoseGases.X n => (1 : ℝ)) i x‖ := by rw [hsub]
      _ ≤ ‖Work.SmallBoxTBWord.tBamp χ p Ψ i x‖
            + ‖((Work.SmallBoxTBWord.boxP volA Ac i Ψ (Function.update x i 0) : ℝ) : ℂ)
              * Work.SmallBoxTBWord.tBamp χ p
                  (fun _ : Submission.BoseGases.X n => (1 : ℝ)) i x‖ := norm_sub_le _ _
      _ ≤ C₁ / (1 + ‖p‖) ^ 3 + CΨ * (C₂ / (1 + ‖p‖) ^ 3) := add_le_add (hC₁ x hx i p) h3
      _ = (C₁ + CΨ * C₂) / (1 + ‖p‖) ^ 3 := by ring
  -- ### the `x`-integral is bounded by `C²(1+‖p‖)⁻⁶·|abox|`
  have hd : ∀ p : E3, (∫ x in Submission.BoseGases.abox n a,
        ‖Work.SmallBoxTBWord.tBamp χ p (Work.UBBInputs8.boxQInd volA Ac i Ψ) i x‖ ^ 2)
      ≤ (C₁ + CΨ * C₂) ^ 2 * (1 + ‖p‖) ^ (-(6 : ℝ))
        * (volume (Submission.BoseGases.abox n a)).toReal := by
    intro p
    have h1 : ‖∫ x in Submission.BoseGases.abox n a,
          ‖Work.SmallBoxTBWord.tBamp χ p (Work.UBBInputs8.boxQInd volA Ac i Ψ) i x‖ ^ 2‖
        ≤ (((C₁ + CΨ * C₂) / (1 + ‖p‖) ^ 3)) ^ 2
          * (volume (Submission.BoseGases.abox n a)).toReal :=
      norm_setIntegral_le_of_norm_le_const (Submission.BoseGases.abox_lt_top n a ha.le)
        (fun x hx => by
          rw [Real.norm_of_nonneg (sq_nonneg _)]
          exact pow_le_pow_left₀ (norm_nonneg _) (hdecay x hx p) 2)
    rwa [Real.norm_of_nonneg (integral_nonneg (fun x => sq_nonneg _)),
      Submission.BoseGases.div_cube_sq_eq (C₁ + CΨ * C₂) (1 + ‖p‖) (by positivity)] at h1
  -- ### the constant
  set K₂ : ℝ := (a ^ 3)⁻¹ * (volume (Submission.BoseGases.abox n a)).toReal
    * (C₁ + CΨ * C₂) ^ 2 with hK₂
  set K : ℝ := 2 * K₂ * (1 + c₀ ^ 2) with hK
  have hK₂0 : 0 ≤ K₂ := by
    rw [hK₂]
    refine mul_nonneg (mul_nonneg (inv_nonneg.mpr (by positivity)) ?_) (sq_nonneg _)
    exact ENNReal.toReal_nonneg
  have hK0 : 0 ≤ K := by rw [hK]; positivity
  have hpt : ∀ p : E3, Submission.BoseGases.fsKinCoeff c₀ ‖p‖ * ((a ^ 3)⁻¹ *
        ∫ x in Submission.BoseGases.abox n a,
          ‖Work.SmallBoxTBWord.tBamp χ p (Work.UBBInputs8.boxQInd volA Ac i Ψ) i x‖ ^ 2)
      ≤ K * (1 + ‖p‖) ^ (-(4 : ℝ)) := by
    intro p
    have hb : (0 : ℝ) < 1 + ‖p‖ := by positivity
    have hd' : (a ^ 3)⁻¹ * (∫ x in Submission.BoseGases.abox n a,
          ‖Work.SmallBoxTBWord.tBamp χ p (Work.UBBInputs8.boxQInd volA Ac i Ψ) i x‖ ^ 2)
        ≤ K₂ * (1 + ‖p‖) ^ (-(6 : ℝ)) := by
      rw [hK₂]
      calc (a ^ 3)⁻¹ * (∫ x in Submission.BoseGases.abox n a,
            ‖Work.SmallBoxTBWord.tBamp χ p (Work.UBBInputs8.boxQInd volA Ac i Ψ) i x‖ ^ 2)
          ≤ (a ^ 3)⁻¹ * ((C₁ + CΨ * C₂) ^ 2 * (1 + ‖p‖) ^ (-(6 : ℝ))
              * (volume (Submission.BoseGases.abox n a)).toReal) :=
            mul_le_mul_of_nonneg_left (hd p) (inv_nonneg.mpr (by positivity))
        _ = (a ^ 3)⁻¹ * (volume (Submission.BoseGases.abox n a)).toReal
              * (C₁ + CΨ * C₂) ^ 2 * (1 + ‖p‖) ^ (-(6 : ℝ)) := by ring
    have step1 : (‖p‖ ^ 2 + c₀ ^ 2) * (1 + ‖p‖) ^ (-(6 : ℝ))
        ≤ (1 + c₀ ^ 2) * (1 + ‖p‖) ^ (-(4 : ℝ)) := by
      have haux : ‖p‖ ^ 2 + c₀ ^ 2 ≤ (1 + c₀ ^ 2) * (1 + ‖p‖ ^ 2) := by
        nlinarith [sq_nonneg ‖p‖, sq_nonneg c₀, norm_nonneg p]
      have h3 : (1 + ‖p‖ ^ 2) * (1 + ‖p‖) ^ (-(6 : ℝ)) ≤ (1 + ‖p‖) ^ (-(4 : ℝ)) := by
        have h2 : (1 + ‖p‖ ^ 2 : ℝ) ≤ (1 + ‖p‖) ^ 2 := by nlinarith [norm_nonneg p]
        have hpow : (1 + ‖p‖) ^ 2 = (1 + ‖p‖) ^ ((2 : ℕ) : ℝ) := by rw [Real.rpow_natCast]
        calc (1 + ‖p‖ ^ 2) * (1 + ‖p‖) ^ (-(6 : ℝ))
            ≤ (1 + ‖p‖) ^ 2 * (1 + ‖p‖) ^ (-(6 : ℝ)) :=
              mul_le_mul_of_nonneg_right h2 (Real.rpow_nonneg hb.le _)
          _ = (1 + ‖p‖) ^ ((2 : ℕ) : ℝ) * (1 + ‖p‖) ^ (-(6 : ℝ)) := by rw [hpow]
          _ = (1 + ‖p‖) ^ (((2 : ℕ) : ℝ) + -(6 : ℝ)) := (Real.rpow_add hb _ _).symm
          _ = (1 + ‖p‖) ^ (-(4 : ℝ)) := by norm_num
      calc (‖p‖ ^ 2 + c₀ ^ 2) * (1 + ‖p‖) ^ (-(6 : ℝ))
          ≤ ((1 + c₀ ^ 2) * (1 + ‖p‖ ^ 2)) * (1 + ‖p‖) ^ (-(6 : ℝ)) :=
            mul_le_mul_of_nonneg_right haux (Real.rpow_nonneg hb.le _)
        _ = (1 + c₀ ^ 2) * ((1 + ‖p‖ ^ 2) * (1 + ‖p‖) ^ (-(6 : ℝ))) := by ring
        _ ≤ (1 + c₀ ^ 2) * (1 + ‖p‖) ^ (-(4 : ℝ)) :=
            mul_le_mul_of_nonneg_left h3 (by positivity)
    calc Submission.BoseGases.fsKinCoeff c₀ ‖p‖ * ((a ^ 3)⁻¹ *
          ∫ x in Submission.BoseGases.abox n a,
            ‖Work.SmallBoxTBWord.tBamp χ p (Work.UBBInputs8.boxQInd volA Ac i Ψ) i x‖ ^ 2)
        ≤ (2 * (‖p‖ ^ 2 + c₀ ^ 2)) * (K₂ * (1 + ‖p‖) ^ (-(6 : ℝ))) := by
          refine mul_le_mul (fsKinCoeff_le_two c₀ ‖p‖) hd' ?_ ?_
          · exact mul_nonneg (inv_nonneg.mpr (by positivity))
              (integral_nonneg (fun x => sq_nonneg _))
          · positivity
      _ = 2 * K₂ * ((‖p‖ ^ 2 + c₀ ^ 2) * (1 + ‖p‖) ^ (-(6 : ℝ))) := by ring
      _ ≤ 2 * K₂ * ((1 + c₀ ^ 2) * (1 + ‖p‖) ^ (-(4 : ℝ))) :=
          mul_le_mul_of_nonneg_left step1 (by positivity)
      _ = K * (1 + ‖p‖) ^ (-(4 : ℝ)) := by rw [hK]; ring
  -- ### the majorant is integrable, and so is the integrand
  refine Integrable.mono' (g := fun p : E3 => K * (1 + ‖p‖) ^ (-(4 : ℝ))) ?_ ?_ ?_
  · exact integrable_one_add_norm_four_r3.const_mul K
  · have hsm : StronglyMeasurable (fun p : E3 =>
        ∫ x in Submission.BoseGases.abox n a,
          ‖Work.SmallBoxTBWord.tBamp χ p (Work.UBBInputs8.boxQInd volA Ac i Ψ) i x‖ ^ 2) :=
      (Work.BoseFixB1.measurable_tBamp_boxQInd_pair (n := n) (A := Ac) (χ := χ) (volA := volA)
        (Ψ := Ψ) hAcm hχc.continuous hΨc.continuous.measurable i).stronglyMeasurable
        |>.integral_prod_right
    have hcont : Continuous (fun p : E3 => Submission.BoseGases.fsKinCoeff c₀ ‖p‖) := by
      simp only [Submission.BoseGases.fsKinCoeff]
      fun_prop
    exact (hcont.aestronglyMeasurable.mul (hsm.const_mul _).aestronglyMeasurable)
  · filter_upwards with p
    rw [Real.norm_of_nonneg (mul_nonneg (Submission.BoseGases.fsKinCoeff_nonneg c₀ ‖p‖)
      (mul_nonneg (inv_nonneg.mpr (by positivity)) (integral_nonneg (fun x => sq_nonneg _))))]
    exact hpt p

theorem winModeContentLeWord {n : ℕ} {a volA : ℝ} (ha : 0 < a)
    {Ac : Set (EuclideanSpace ℝ (Fin 3))} (hAcm : MeasurableSet Ac)
    (hAcsub : Ac ⊆ Submission.BoseGases.acube a)
    (hvol : volA = (MeasureTheory.volume Ac).toReal) (hvolpos : 0 < volA)
    {χ : EuclideanSpace ℝ (Fin 3) → ℝ} (hχc : ContDiff ℝ (⊤ : ℕ∞) χ)
    (hχs : HasCompactSupport χ) (hχsupp : ∀ z, z ∉ Ac → χ z = 0) (hχnn : ∀ z, 0 ≤ χ z)
    {c₀ : ℝ} (hc₀ : 0 < c₀)
    {Ψ : Submission.BoseGases.X n → ℝ} (hΨc : ContDiff ℝ (⊤ : ℕ∞) Ψ) :
    ((2 * Real.pi) ^ 3)⁻¹ * (∫ q : EuclideanSpace ℝ (Fin 3),
        Submission.BoseGases.fsKinCoeff c₀ ‖q‖ * Work.BoseFixB1.boxWinModePGen a volA Ac χ Ψ q)
      ≤ (n : ℝ) * Work.UBBInputs8.tBdiagFormInd a Ac volA χ
          (Submission.BoseGases.fsKinCoeff c₀) Ψ := by
  classical
  obtain ⟨Cχ, hCχ⟩ := (Submission.BoseGases.acube_compact ha).exists_bound_of_continuousOn
    hχc.continuous.continuousOn
  set κ : ℝ := max Cχ 0 with hκdef
  have hκ0 : 0 ≤ κ := le_max_right _ _
  have hκ : ∀ z : EuclideanSpace ℝ (Fin 3), χ z ≤ κ := by
    intro z
    by_cases hz : z ∈ Submission.BoseGases.acube a
    · exact le_trans (le_trans (le_abs_self (χ z)) (hCχ z hz)) (le_max_left _ _)
    · rw [hχsupp z (fun h => hz (hAcsub h))]
      exact hκ0
  obtain ⟨CΨ, hCΨ0, hCΨ⟩ := Work.BoseFixB1.exists_bound_abox_pos (ℓ := a) ha hΨc.continuous
  refine winModeContentLeWord_of_pointwise ha hAcm hAcsub hvol hvolpos hχc.continuous hc₀
    hΨc.continuous ?_ ?_
  · intro q
    exact boxWinModePGen_le_slotSum_clean ha hvolpos hκ0 hAcm hAcsub hvol hχc.continuous hχs
      hχnn hκ hΨc.continuous hCΨ hCΨ0 q
  · intro i
    exact integrableFsKinCoeff_tBamp_boxQIndN ha hvolpos hAcm hAcsub hvol hχc hχs hχsupp hΨc i

end Work.BoseFixB1B.pairRung
