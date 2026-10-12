import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.Work.BoseFixB1.BoxFrameBackup
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB1B.pairRung.frameXIntegral`

The `x`-integral of the Cauchy–Schwarz frame bound.  At every configuration `x` the Cauchy–Schwarz
step of the frame bound produces the (slot-summed) weight

  `Σ_i 1_Ac(x_i)·∫_{Ac}(Q_{Ac,i}Ψ)(x_{i↦z})² dz`

and this module computes its integral over the box: the slot swap
`Work.BoseFixB1.slotSwap_abox'` (a Fubini/peel identity for the mean-free fibre) together with the
pointwise collapse `1_Ac(x_i)·(Q_{Ac,i}Ψ x)² = (Q_{Ac,i}Ψ x)²` gives, slot by slot,

  `∫_{abox n a} 1_Ac(x_i)·∫_{Ac}(Q_{Ac,i}Ψ)(x_{i↦z})² dz = volA·∫_{abox n a}(Q_{Ac,i}Ψ x)²`,

so that summing over the slots and multiplying by the constant `volA⁻¹ n κ² (2π)³` yields

  `∫_{abox n a} volA⁻¹ n κ² (2π)³ Σ_i 1_Ac(x_i)∫_{Ac}(Q_{Ac,i}Ψ)(x_{i↦z})²
      = (2π)³ volA⁻¹ n κ² volA · cnPlusBoxInd a Ac volA Ψ`.

The integrability of the integrand (a finite sum of bounded measurable functions on the compact box)
is proved alongside.

Everything is done inside the import cone of `Work.BoseFixB1.BoxFrameBackup` (plus
`Work.UBBInputs8.Defs` for `cnPlusBoxInd`), so that the file stays compatible with the clash-free
`pairRung` cone, which must **not** import `Work.BoseFixB1.boxFramePGen` (duplicate
`Work.BoseFixB1.exists_bound_abox`).
-/

noncomputable section

open MeasureTheory Filter
open scoped Real BigOperators ENNReal

namespace Work.BoseFixB1B.pairRung

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-! ## 0. Elementary bounds -/

/-- The restricted box measure is finite, since `Ac ⊆ acube a`. -/
lemma isFiniteMeasure_restrict_acube {a : ℝ} (ha : 0 < a) {Ac : Set E3}
    (hAc : Ac ⊆ Submission.BoseGases.acube a) :
    IsFiniteMeasure ((volume : Measure E3).restrict Ac) := by
  refine ⟨?_⟩
  rw [Measure.restrict_apply_univ]
  exact lt_of_le_of_lt (measure_mono hAc) (Submission.BoseGases.acube_lt_top a ha.le)

/-- **The mean-free fibre is bounded.**  On the box, and for `z ∈ Ac`, the mean-free fibre is the
deviation of `Ψ` from its box mean along the slot `i`, hence bounded by `2CΨ`. -/
lemma abs_slotFibre_le {n : ℕ} {a volA CΨ : ℝ} (ha : 0 < a) (hvolpos : 0 < volA)
    {Ac : Set E3} (hAcm : MeasurableSet Ac) (hAc : Ac ⊆ Submission.BoseGases.acube a)
    (hvol : volA = (MeasureTheory.volume Ac).toReal)
    {Ψ : Submission.BoseGases.X n → ℝ} (hΨ : Continuous Ψ)
    (hCΨ : ∀ x ∈ Submission.BoseGases.abox n a, |Ψ x| ≤ CΨ)
    {x : Submission.BoseGases.X n} (hx : x ∈ Submission.BoseGases.abox n a) (i : Fin n) :
    ∀ z ∈ Ac, |Work.BoseFixB1.slotFibre volA Ac i Ψ x z| ≤ 2 * CΨ := by
  haveI : IsFiniteMeasure ((volume : Measure E3).restrict Ac) :=
    isFiniteMeasure_restrict_acube ha hAc
  have hmem : ∀ z ∈ Ac, Function.update x i z ∈ Submission.BoseGases.abox n a :=
    fun z hz => Work.BoseFixB1.update_mem_abox' hAc hx i hz
  have hmean : |volA⁻¹ * ∫ w in Ac, Ψ (Function.update x i w)| ≤ CΨ := by
    have h1 : |∫ w in Ac, Ψ (Function.update x i w)| ≤ CΨ * volA := by
      refine (abs_integral_le_integral_abs).trans ?_
      have hmono := integral_mono_of_nonneg
        (μ := (volume : Measure E3).restrict Ac)
        (f := fun w : E3 => |Ψ (Function.update x i w)|) (g := fun _ : E3 => CΨ)
        (Eventually.of_forall fun w => abs_nonneg _) (integrable_const CΨ)
        (ae_restrict_iff' hAcm |>.mpr (ae_of_all _ (fun w hw => hCΨ _ (hmem w hw))))
      refine hmono.trans (le_of_eq ?_)
      rw [MeasureTheory.setIntegral_const, Measure.real_def, ← hvol, smul_eq_mul, mul_comm]
    rw [abs_mul, abs_of_nonneg (inv_nonneg.mpr hvolpos.le)]
    calc volA⁻¹ * |∫ w in Ac, Ψ (Function.update x i w)| ≤ volA⁻¹ * (CΨ * volA) :=
          mul_le_mul_of_nonneg_left h1 (inv_nonneg.mpr hvolpos.le)
      _ = CΨ := by
          rw [inv_mul_eq_iff_eq_mul₀ (ne_of_gt hvolpos)]
          ring
  intro z hz
  rw [Work.BoseFixB1.slotFibre_eq volA x z hz]
  calc |Ψ (Function.update x i z) - volA⁻¹ * ∫ w in Ac, Ψ (Function.update x i w)|
      ≤ |Ψ (Function.update x i z)|
        + |volA⁻¹ * ∫ w in Ac, Ψ (Function.update x i w)| := abs_sub _ _
    _ ≤ CΨ + CΨ := add_le_add (hCΨ _ (hmem z hz)) hmean
    _ = 2 * CΨ := by ring

/-- The box projection is bounded by `2CΨ` on the box. -/
lemma abs_boxQInd_le {n : ℕ} {a volA CΨ : ℝ} (ha : 0 < a) (hvolpos : 0 < volA)
    (hCΨ0 : 0 ≤ CΨ)
    {Ac : Set E3} (hAcm : MeasurableSet Ac) (hAc : Ac ⊆ Submission.BoseGases.acube a)
    (hvol : volA = (MeasureTheory.volume Ac).toReal)
    {Ψ : Submission.BoseGases.X n → ℝ} (hΨ : Continuous Ψ)
    (hCΨ : ∀ x ∈ Submission.BoseGases.abox n a, |Ψ x| ≤ CΨ)
    {x : Submission.BoseGases.X n} (hx : x ∈ Submission.BoseGases.abox n a) (i : Fin n) :
    |Work.UBBInputs8.boxQInd volA Ac i Ψ x| ≤ 2 * CΨ := by
  by_cases h : x i ∈ Ac
  · have hupd : Function.update x i (x i) = x := Function.update_eq_self i x
    have hb := abs_slotFibre_le ha hvolpos hAcm hAc hvol hΨ hCΨ hx i (x i) h
    simpa [Work.BoseFixB1.slotFibre, hupd] using hb
  · have hzero : Work.UBBInputs8.boxQInd volA Ac i Ψ x = 0 := by
      rw [Work.UBBInputs8.boxQInd, Work.UBBInputs8.boxPInd, Set.indicator_of_notMem h]
      ring
    rw [hzero, abs_zero]
    linarith

/-- The box projection already carries its indicator. -/
lemma indicator_mul_boxQInd_sq {n : ℕ} (volA : ℝ) {Ac : Set E3} (i : Fin n)
    (Ψ : Submission.BoseGases.X n → ℝ) (x : Submission.BoseGases.X n) :
    Ac.indicator (fun _ => (1 : ℝ)) (x i) * (Work.UBBInputs8.boxQInd volA Ac i Ψ x) ^ 2
      = (Work.UBBInputs8.boxQInd volA Ac i Ψ x) ^ 2 := by
  by_cases h : x i ∈ Ac
  · rw [Set.indicator_of_mem h, one_mul]
  · have hzero : Work.UBBInputs8.boxQInd volA Ac i Ψ x = 0 := by
      rw [Work.UBBInputs8.boxQInd, Work.UBBInputs8.boxPInd, Set.indicator_of_notMem h]
      ring
    rw [Set.indicator_of_notMem h, zero_mul, hzero]
    ring

/-! ## 1. Measurability and integrability of the slot weight -/

/-- Measurability of the slot weight `x ↦ 1_Ac(x_i)·∫_{Ac}(Q_{Ac,i}Ψ)(x_{i↦z})² dz`: the fibre is
measurable on the product and `integral_prod_right` gives the measurability of the `z`-integral. -/
lemma measurable_slotWeight {n : ℕ} {volA : ℝ} {Ac : Set E3} (hAcm : MeasurableSet Ac)
    {Ψ : Submission.BoseGases.X n → ℝ} (hΨ : Continuous Ψ) (i : Fin n) :
    Measurable (fun x : Submission.BoseGases.X n =>
      Ac.indicator (fun _ => (1 : ℝ)) (x i)
        * ∫ z in Ac, (Work.BoseFixB1.slotFibre volA Ac i Ψ x z) ^ 2) := by
  have hsm : StronglyMeasurable (Function.uncurry (fun (x : Submission.BoseGases.X n) (z : E3) =>
      (Work.BoseFixB1.slotFibre volA Ac i Ψ x z) ^ 2)) := by
    have h1 : Measurable (fun p : Submission.BoseGases.X n × E3 =>
        Work.BoseFixB1.slotFibre volA Ac i Ψ p.1 p.2) := by
      have heq : (fun p : Submission.BoseGases.X n × E3 =>
          Work.BoseFixB1.slotFibre volA Ac i Ψ p.1 p.2)
          = fun p => Work.UBBInputs8.boxQInd volA Ac i Ψ (Function.update p.1 i p.2) := rfl
      rw [heq]
      exact (SlotWord.measurable_boxQInd volA Ac hAcm i hΨ.measurable).comp measurable_update'
    exact (h1.pow_const 2).stronglyMeasurable
  have h := hsm.integral_prod_right (ν := (volume : Measure E3).restrict Ac)
  refine Measurable.mul ((measurable_const.indicator hAcm).comp (measurable_pi_apply i)) ?_
  simpa only [Function.uncurry_apply_pair] using h.measurable

/-- **Pointwise bound for the slot weight.** -/
lemma abs_slotWeight_le {n : ℕ} {a volA CΨ : ℝ} (ha : 0 < a) (hvolpos : 0 < volA)
    {Ac : Set E3} (hAcm : MeasurableSet Ac) (hAc : Ac ⊆ Submission.BoseGases.acube a)
    (hvol : volA = (MeasureTheory.volume Ac).toReal)
    {Ψ : Submission.BoseGases.X n → ℝ} (hΨ : Continuous Ψ)
    (hCΨ : ∀ x ∈ Submission.BoseGases.abox n a, |Ψ x| ≤ CΨ)
    {x : Submission.BoseGases.X n} (hx : x ∈ Submission.BoseGases.abox n a) (i : Fin n) :
    |Ac.indicator (fun _ => (1 : ℝ)) (x i)
        * ∫ z in Ac, (Work.BoseFixB1.slotFibre volA Ac i Ψ x z) ^ 2| ≤
      (2 * CΨ) ^ 2 * volA := by
  haveI : IsFiniteMeasure ((volume : Measure E3).restrict Ac) :=
    isFiniteMeasure_restrict_acube ha hAc
  rw [abs_mul]
  have hind : |Ac.indicator (fun _ => (1 : ℝ)) (x i)| ≤ (1 : ℝ) := by
    by_cases h : x i ∈ Ac
    · rw [Set.indicator_of_mem h, abs_one]
    · rw [Set.indicator_of_notMem h, abs_zero]; norm_num
  have hbound : (∫ z in Ac, |(Work.BoseFixB1.slotFibre volA Ac i Ψ x z) ^ 2|) ≤
      (2 * CΨ) ^ 2 * volA := by
    calc (∫ z in Ac, |(Work.BoseFixB1.slotFibre volA Ac i Ψ x z) ^ 2|)
        ≤ ∫ _z in Ac, ((2 * CΨ) ^ 2) := by
          refine integral_mono_of_nonneg (Eventually.of_forall fun z => abs_nonneg _)
            (integrable_const _) (ae_restrict_iff' hAcm |>.mpr (ae_of_all _ fun z hz => ?_))
          show |(Work.BoseFixB1.slotFibre volA Ac i Ψ x z) ^ 2| ≤ (2 * CΨ) ^ 2
          calc |(Work.BoseFixB1.slotFibre volA Ac i Ψ x z) ^ 2|
              = (Work.BoseFixB1.slotFibre volA Ac i Ψ x z) ^ 2 := by
                rw [abs_of_nonneg (sq_nonneg _)]
            _ ≤ (2 * CΨ) ^ 2 := by
                rw [← sq_abs]
                exact pow_le_pow_left₀ (abs_nonneg _)
                  (abs_slotFibre_le ha hvolpos hAcm hAc hvol hΨ hCΨ hx i z hz) 2
      _ = (2 * CΨ) ^ 2 * volA := by
          rw [MeasureTheory.setIntegral_const, Measure.real_def, ← hvol, smul_eq_mul, mul_comm]
  have hsq : |∫ z in Ac, (Work.BoseFixB1.slotFibre volA Ac i Ψ x z) ^ 2| ≤
      (2 * CΨ) ^ 2 * volA :=
    (abs_integral_le_integral_abs).trans hbound
  calc |Ac.indicator (fun _ => (1 : ℝ)) (x i)|
        * |∫ z in Ac, (Work.BoseFixB1.slotFibre volA Ac i Ψ x z) ^ 2|
      ≤ 1 * ((2 * CΨ) ^ 2 * volA) := mul_le_mul hind hsq (abs_nonneg _) (by norm_num)
    _ = (2 * CΨ) ^ 2 * volA := one_mul _

/-- Integrability of the slot weight on the box. -/
lemma integrableOn_slotWeight {n : ℕ} {a volA CΨ : ℝ} (ha : 0 < a) (hvolpos : 0 < volA)
    {Ac : Set E3} (hAcm : MeasurableSet Ac) (hAc : Ac ⊆ Submission.BoseGases.acube a)
    (hvol : volA = (MeasureTheory.volume Ac).toReal)
    {Ψ : Submission.BoseGases.X n → ℝ} (hΨ : Continuous Ψ)
    (hCΨ : ∀ x ∈ Submission.BoseGases.abox n a, |Ψ x| ≤ CΨ) (i : Fin n) :
    IntegrableOn (fun x : Submission.BoseGases.X n =>
      Ac.indicator (fun _ => (1 : ℝ)) (x i)
        * ∫ z in Ac, (Work.BoseFixB1.slotFibre volA Ac i Ψ x z) ^ 2)
      (Submission.BoseGases.abox n a) volume := by
  refine IntegrableOn.of_bound (Submission.BoseGases.abox_compact n ha).measure_lt_top
    (measurable_slotWeight (volA := volA) hAcm hΨ i).aestronglyMeasurable
    ((2 * CΨ) ^ 2 * volA) ?_
  rw [ae_restrict_iff' (Submission.BoseGases.abox_measurable n a)]
  exact ae_of_all _ (fun x hx => by
    rw [Real.norm_eq_abs]
    exact abs_slotWeight_le ha hvolpos hAcm hAc hvol hΨ hCΨ hx i)

/-! ## 2. The slot swap, slot by slot -/

/-- **The `x`-integral of one slot weight.**  The slot swap applied to `(Q_{Ac,i}Ψ)²` turns the
double integral `∫_x 1_Ac(x_i)∫_{Ac}(Q_{Ac,i}Ψ)(x_{i↦z})²` into `volA·∫_x (Q_{Ac,i}Ψ x)²`. -/
lemma integral_slotWeight {n : ℕ} {a volA CΨ : ℝ} (ha : 0 < a) (hvolpos : 0 < volA)
    (hCΨ0 : 0 ≤ CΨ)
    {Ac : Set E3} (hAcm : MeasurableSet Ac) (hAc : Ac ⊆ Submission.BoseGases.acube a)
    (hvol : volA = (MeasureTheory.volume Ac).toReal)
    {Ψ : Submission.BoseGases.X n → ℝ} (hΨ : Continuous Ψ)
    (hCΨ : ∀ x ∈ Submission.BoseGases.abox n a, |Ψ x| ≤ CΨ) (i : Fin n) :
    (∫ x in Submission.BoseGases.abox n a,
        Ac.indicator (fun _ => (1 : ℝ)) (x i)
          * ∫ z in Ac, (Work.BoseFixB1.slotFibre volA Ac i Ψ x z) ^ 2)
      = volA * ∫ x in Submission.BoseGases.abox n a,
          (Work.UBBInputs8.boxQInd volA Ac i Ψ x) ^ 2 := by
  have hH : Measurable (fun y : Submission.BoseGases.X n =>
      (Work.UBBInputs8.boxQInd volA Ac i Ψ y) ^ 2) :=
    (SlotWord.measurable_boxQInd volA Ac hAcm i hΨ.measurable).pow_const 2
  have hb := Work.BoseFixB1.slotSwap_abox' ha hAcm hAc hvol hvolpos i
    (H := fun y : Submission.BoseGases.X n => (Work.UBBInputs8.boxQInd volA Ac i Ψ y) ^ 2)
    hH (K := (2 * CΨ) ^ 2) (by positivity) (fun x hx => by
      rw [abs_of_nonneg (sq_nonneg _), ← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _)
        (abs_boxQInd_le ha hvolpos hCΨ0 hAcm hAc hvol hΨ hCΨ hx i) 2)
  rw [show (∫ x in Submission.BoseGases.abox n a,
        Ac.indicator (fun _ => (1 : ℝ)) (x i)
          * ∫ z in Ac, (Work.BoseFixB1.slotFibre volA Ac i Ψ x z) ^ 2)
      = ∫ x in Submission.BoseGases.abox n a,
          Ac.indicator (fun _ => (1 : ℝ)) (x i)
            * ∫ z in Ac, (Work.UBBInputs8.boxQInd volA Ac i Ψ (Function.update x i z)) ^ 2
      from rfl]
  rw [hb]
  congr 1
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  exact indicator_mul_boxQInd_sq volA i Ψ x

/-! ## 3. The integrability and the `x`-integral of the frame bound -/

/-- **Integrability of the frame integrand over the box.** -/
lemma frameX_integrable {n : ℕ} {a volA κ CΨ : ℝ} (ha : 0 < a) (hvolpos : 0 < volA)
    {Ac : Set E3} (hAcm : MeasurableSet Ac) (hAc : Ac ⊆ Submission.BoseGases.acube a)
    (hvol : volA = (MeasureTheory.volume Ac).toReal)
    {Ψ : Submission.BoseGases.X n → ℝ} (hΨ : Continuous Ψ)
    (hCΨ : ∀ x ∈ Submission.BoseGases.abox n a, |Ψ x| ≤ CΨ) :
    MeasureTheory.IntegrableOn
        (fun x : Submission.BoseGases.X n => volA⁻¹ * (n : ℝ) * κ ^ 2 * (2 * Real.pi) ^ 3 *
            ∑ i : Fin n, Ac.indicator (fun _ => (1 : ℝ)) (x i)
              * ∫ z in Ac, (Work.BoseFixB1.slotFibre volA Ac i Ψ x z) ^ 2)
        (Submission.BoseGases.abox n a) MeasureTheory.volume := by
  have hS : IntegrableOn (fun x : Submission.BoseGases.X n =>
      ∑ i : Fin n, Ac.indicator (fun _ => (1 : ℝ)) (x i)
        * ∫ z in Ac, (Work.BoseFixB1.slotFibre volA Ac i Ψ x z) ^ 2)
      (Submission.BoseGases.abox n a) volume := by
    have hmeas : AEStronglyMeasurable (fun x : Submission.BoseGases.X n =>
        ∑ i : Fin n, Ac.indicator (fun _ => (1 : ℝ)) (x i)
          * ∫ z in Ac, (Work.BoseFixB1.slotFibre volA Ac i Ψ x z) ^ 2)
        ((volume : Measure (Submission.BoseGases.X n)).restrict
          (Submission.BoseGases.abox n a)) :=
      (Finset.measurable_sum Finset.univ
        (fun i _ => measurable_slotWeight (volA := volA) hAcm hΨ i)).aestronglyMeasurable
    refine IntegrableOn.of_bound (Submission.BoseGases.abox_compact n ha).measure_lt_top hmeas
      ((n : ℝ) * ((2 * CΨ) ^ 2 * volA)) ?_
    rw [ae_restrict_iff' (Submission.BoseGases.abox_measurable n a)]
    refine ae_of_all _ (fun x hx => ?_)
    calc ‖∑ i : Fin n, Ac.indicator (fun _ => (1 : ℝ)) (x i)
            * ∫ z in Ac, (Work.BoseFixB1.slotFibre volA Ac i Ψ x z) ^ 2‖
        ≤ ∑ i : Fin n, ‖Ac.indicator (fun _ => (1 : ℝ)) (x i)
            * ∫ z in Ac, (Work.BoseFixB1.slotFibre volA Ac i Ψ x z) ^ 2‖ :=
          norm_sum_le _ _
      _ ≤ ∑ _i : Fin n, ((2 * CΨ) ^ 2 * volA) :=
          Finset.sum_le_sum (fun i _ => by
            rw [Real.norm_eq_abs]
            exact abs_slotWeight_le ha hvolpos hAcm hAc hvol hΨ hCΨ hx i)
      _ = (n : ℝ) * ((2 * CΨ) ^ 2 * volA) := by
          simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  exact hS.const_mul _

/-- **The `x`-integral of the frame bound.** -/
lemma frameX_integral {n : ℕ} {a volA κ CΨ : ℝ} (ha : 0 < a) (hvolpos : 0 < volA)
    (hCΨ0 : 0 ≤ CΨ)
    {Ac : Set E3} (hAcm : MeasurableSet Ac) (hAc : Ac ⊆ Submission.BoseGases.acube a)
    (hvol : volA = (MeasureTheory.volume Ac).toReal)
    {Ψ : Submission.BoseGases.X n → ℝ} (hΨ : Continuous Ψ)
    (hCΨ : ∀ x ∈ Submission.BoseGases.abox n a, |Ψ x| ≤ CΨ) :
    (∫ x in Submission.BoseGases.abox n a,
          volA⁻¹ * (n : ℝ) * κ ^ 2 * (2 * Real.pi) ^ 3 *
            ∑ i : Fin n, Ac.indicator (fun _ => (1 : ℝ)) (x i)
              * ∫ z in Ac, (Work.BoseFixB1.slotFibre volA Ac i Ψ x z) ^ 2)
        = (2 * Real.pi) ^ 3 * volA⁻¹ * (n : ℝ) * κ ^ 2 * volA
          * Work.UBBInputs8.cnPlusBoxInd a Ac volA Ψ := by
  have hInt : ∀ i : Fin n, IntegrableOn (fun x : Submission.BoseGases.X n =>
      Ac.indicator (fun _ => (1 : ℝ)) (x i)
        * ∫ z in Ac, (Work.BoseFixB1.slotFibre volA Ac i Ψ x z) ^ 2)
      (Submission.BoseGases.abox n a) volume :=
    fun i => integrableOn_slotWeight ha hvolpos hAcm hAc hvol hΨ hCΨ i
  have hslot : ∀ i : Fin n,
      (∫ x in Submission.BoseGases.abox n a,
          Ac.indicator (fun _ => (1 : ℝ)) (x i)
            * ∫ z in Ac, (Work.BoseFixB1.slotFibre volA Ac i Ψ x z) ^ 2)
        = volA * ∫ x in Submission.BoseGases.abox n a,
            (Work.UBBInputs8.boxQInd volA Ac i Ψ x) ^ 2 :=
    fun i => integral_slotWeight ha hvolpos hCΨ0 hAcm hAc hvol hΨ hCΨ i
  rw [MeasureTheory.integral_const_mul,
    MeasureTheory.integral_finsetSum _ (fun i _ => hInt i)]
  rw [Finset.sum_congr rfl (fun i _ => hslot i), ← Finset.mul_sum]
  rw [Work.UBBInputs8.cnPlusBoxInd]
  ring

/-! ## 4. The target -/

theorem frameXIntegral {n : ℕ} {a volA κ CΨ : ℝ} (ha : 0 < a)
    {Ac : Set (EuclideanSpace ℝ (Fin 3))} (hAcm : MeasurableSet Ac)
    (hAc : Ac ⊆ Submission.BoseGases.acube a)
    (hvol : volA = (MeasureTheory.volume Ac).toReal) (hvolpos : 0 < volA)
    {Ψ : Submission.BoseGases.X n → ℝ} (hΨ : Continuous Ψ)
    (hCΨ : ∀ x ∈ Submission.BoseGases.abox n a, |Ψ x| ≤ CΨ) (hCΨ0 : 0 ≤ CΨ) :
    MeasureTheory.IntegrableOn
        (fun x : Submission.BoseGases.X n => volA⁻¹ * (n : ℝ) * κ ^ 2 * (2 * Real.pi) ^ 3 *
            ∑ i : Fin n, Ac.indicator (fun _ => (1 : ℝ)) (x i)
              * ∫ z in Ac, (Work.BoseFixB1.slotFibre volA Ac i Ψ x z) ^ 2)
        (Submission.BoseGases.abox n a) MeasureTheory.volume
      ∧ (∫ x in Submission.BoseGases.abox n a,
            volA⁻¹ * (n : ℝ) * κ ^ 2 * (2 * Real.pi) ^ 3 *
              ∑ i : Fin n, Ac.indicator (fun _ => (1 : ℝ)) (x i)
                * ∫ z in Ac, (Work.BoseFixB1.slotFibre volA Ac i Ψ x z) ^ 2)
          = (2 * Real.pi) ^ 3 * volA⁻¹ * (n : ℝ) * κ ^ 2 * volA
            * Work.UBBInputs8.cnPlusBoxInd a Ac volA Ψ :=
  ⟨frameX_integrable ha hvolpos hAcm hAc hvol hΨ hCΨ,
    frameX_integral ha hvolpos hCΨ0 hAcm hAc hvol hΨ hCΨ⟩

end Work.BoseFixB1B.pairRung
