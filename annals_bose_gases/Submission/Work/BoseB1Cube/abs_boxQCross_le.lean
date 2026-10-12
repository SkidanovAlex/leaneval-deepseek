import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB1S.BoxPotOper
import Submission.Work.BoseFixB1S.csIntegralSqLe
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseB1Cube.abs_boxQCross_le`

The **weighted `QQ`/`QP` box-projection cross-line bound** at the sliding box `B(u)`: for a
continuous `n`-body state `Φ` and a cutoff `χ = chiSmallB M ℓ d u` whose square is bounded by
`Ξ` pointwise,

  `|Σᵢ∫_{abox} (χ(xᵢ)QᵢΦ)² + 2Σᵢ∫_{abox} χ(xᵢ)²(QᵢΦ)(PᵢΦ)|`
      `≤ Ξ (2√(S·Q) + Q)`,   `S = boxFlatCount`, `Q = boxQCount`,

where `Pᵢ = boxPInd V A i` is FS's box condensate projection (`P_{B,i}ψ = |B|⁻¹⟨1_B,ψ⟩1_B`)
and `Qᵢ = boxQInd V A i = 1_A(·ᵢ)Φ − PᵢΦ` the mean-free projection of `Work.UBBInputs8.Defs`.

## Mathematics

Write `fᵢ = χ(xᵢ)·QᵢΦ`, `gᵢ = χ(xᵢ)·PᵢΦ`, `qᵢ = ∫(QᵢΦ)²`, `pᵢ = ∫(PᵢΦ)²`.  Pointwise
`fᵢ² ≤ Ξ Qᵢ²`, so the first sum is `≤ Ξ Σᵢqᵢ = ΞQ`.  For the cross sum Cauchy–Schwarz on the
box (`Work.BoseFixB1S.csIntegralSqLe`) gives `|∫fᵢgᵢ| ≤ √(∫fᵢ²)·√(∫gᵢ²) ≤ Ξ√(qᵢpᵢ)`, and
Cauchy–Schwarz over the slot index (`Real.sum_sqrt_mul_sqrt_le`) gives
`ΣᵢΞ√(qᵢpᵢ) ≤ Ξ√(Σᵢpᵢ)·√(Σᵢqᵢ) = Ξ√(S·Q)`.  The triangle inequality assembles the two rows.

All functions are bounded on the compact box `abox n ℓ` (continuity of `Φ`, boundedness of the
projections `Work.BoseFixB1S.boxBounds`), which supplies the `L²` integrability witnesses.
-/

noncomputable section

open MeasureTheory
open scoped Real BigOperators

namespace Work.BoseB1Cube

set_option linter.unusedVariables false

/-- Pure real assembly: from the per-slot rows `Aᵢ ≤ Ξaᵢ` and `|Bᵢ| ≤ Ξ√(aᵢbᵢ)`,
`|ΣA + 2ΣB| ≤ Ξ(2√((Σb)(Σa)) + Σa)`. -/
private theorem sum_slot_bound {ι : Type*} [Fintype ι] {Ξ : ℝ} (hΞ0 : 0 ≤ Ξ)
    {A B a b : ι → ℝ} (hA : ∀ i, 0 ≤ A i) (ha : ∀ i, 0 ≤ a i) (hb : ∀ i, 0 ≤ b i)
    (h1 : ∀ i, A i ≤ Ξ * a i) (h2 : ∀ i, |B i| ≤ Ξ * Real.sqrt (a i * b i)) :
    |(∑ i, A i) + 2 * (∑ i, B i)|
      ≤ Ξ * (2 * Real.sqrt ((∑ i, b i) * (∑ i, a i)) + ∑ i, a i) := by
  have hsumA : (∑ i, A i) ≤ Ξ * ∑ i, a i := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum (fun i _ => h1 i)
  have hsumBabs : |∑ i, B i| ≤ Ξ * Real.sqrt ((∑ i, b i) * (∑ i, a i)) := by
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
    refine le_trans (Finset.sum_le_sum (fun i _ => h2 i)) ?_
    rw [← Finset.mul_sum]
    refine mul_le_mul_of_nonneg_left ?_ hΞ0
    have hcs : (∑ i, Real.sqrt (a i) * Real.sqrt (b i))
        ≤ Real.sqrt (∑ i, a i) * Real.sqrt (∑ i, b i) :=
      Real.sum_sqrt_mul_sqrt_le Finset.univ (fun i => ha i) (fun i => hb i)
    calc (∑ i, Real.sqrt (a i * b i)) = ∑ i, Real.sqrt (a i) * Real.sqrt (b i) :=
          Finset.sum_congr rfl (fun i _ => Real.sqrt_mul (ha i) (b i))
      _ ≤ Real.sqrt (∑ i, a i) * Real.sqrt (∑ i, b i) := hcs
      _ = Real.sqrt ((∑ i, b i) * (∑ i, a i)) := by
          rw [Real.sqrt_mul (Finset.sum_nonneg (fun i _ => hb i)) (∑ i, a i)]
          ring
  have hA0 : 0 ≤ ∑ i, A i := Finset.sum_nonneg (fun i _ => hA i)
  calc |(∑ i, A i) + 2 * (∑ i, B i)|
      ≤ |(∑ i, A i)| + |2 * (∑ i, B i)| := abs_add_le _ _
    _ = (∑ i, A i) + 2 * |∑ i, B i| := by
        rw [abs_of_nonneg hA0, abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2)]
    _ ≤ Ξ * ∑ i, a i + 2 * (Ξ * Real.sqrt ((∑ i, b i) * (∑ i, a i))) :=
        add_le_add hsumA (by linarith [hsumBabs])
    _ = Ξ * (2 * Real.sqrt ((∑ i, b i) * (∑ i, a i)) + ∑ i, a i) := by ring

/-- Per-slot square bound: `∫(χ(xᵢ)QᵢΦ)² ≤ Ξ ∫(QᵢΦ)²`. -/
private theorem slot_sq_le {n : ℕ} {ℓ V Ξ : ℝ} {A : Set (EuclideanSpace ℝ (Fin 3))}
    (hℓ : 0 < ℓ) (hΞ0 : 0 ≤ Ξ)
    {ch : EuclideanSpace ℝ (Fin 3) → ℝ} (hchm : Measurable ch)
    (hchb : ∀ z, (ch z) ^ 2 ≤ Ξ)
    {Φ : Submission.BoseGases.X n → ℝ} (hΦc : Continuous Φ)
    (hA : MeasurableSet A) (hV : 0 < V) (hVeq : V = (volume A).toReal)
    (hAc : A ⊆ Submission.BoseGases.acube ℓ) (i : Fin n) :
    (∫ x in Submission.BoseGases.abox n ℓ,
        (ch (x i) * Work.UBBInputs8.boxQInd V A i Φ x) ^ 2)
      ≤ Ξ * ∫ x in Submission.BoseGases.abox n ℓ,
          (Work.UBBInputs8.boxQInd V A i Φ x) ^ 2 := by
  obtain ⟨C, hC0, hΦb, hPb, hQb⟩ := Work.BoseFixB1S.boxBounds hℓ hV hA hVeq hAc hΦc
  have hQm : Measurable (Work.UBBInputs8.boxQInd V A i Φ) :=
    Work.SlotWord.measurable_boxQInd V A hA i hΦc.measurable
  have hchi : Measurable (fun x : Submission.BoseGases.X n => ch (x i)) :=
    hchm.comp (measurable_pi_apply i)
  have hQ2 : ∀ x ∈ Submission.BoseGases.abox n ℓ,
      (Work.UBBInputs8.boxQInd V A i Φ x) ^ 2 ≤ (2 * C) ^ 2 := by
    intro x hx
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) (hQb i x hx) 2
  have hf2 : Integrable (fun x : Submission.BoseGases.X n =>
      (ch (x i) * Work.UBBInputs8.boxQInd V A i Φ x) ^ 2)
      ((volume : Measure (Submission.BoseGases.X n)).restrict (Submission.BoseGases.abox n ℓ)) := by
    refine Integrable.congr (f := fun x : Submission.BoseGases.X n =>
      (ch (x i)) ^ 2 * (Work.UBBInputs8.boxQInd V A i Φ x) ^ 2) ?_ ?_
    · refine IntegrableOn.of_bound (Submission.BoseGases.abox_lt_top n ℓ hℓ.le)
        ((hchi.pow_const 2).mul (hQm.pow_const 2)).aestronglyMeasurable (Ξ * (2 * C) ^ 2) ?_
      rw [ae_restrict_iff' (Submission.BoseGases.abox_measurable n ℓ)]
      refine Filter.Eventually.of_forall (fun x hx => ?_)
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _))]
      exact mul_le_mul (hchb (x i)) (hQ2 x hx) (sq_nonneg _) hΞ0
    · filter_upwards with x
      ring
  have hQint : Integrable (fun x : Submission.BoseGases.X n =>
      (Work.UBBInputs8.boxQInd V A i Φ x) ^ 2)
      ((volume : Measure (Submission.BoseGases.X n)).restrict (Submission.BoseGases.abox n ℓ)) :=
    IntegrableOn.of_bound (Submission.BoseGases.abox_lt_top n ℓ hℓ.le)
      (hQm.pow_const 2).aestronglyMeasurable ((2 * C) ^ 2) (by
        rw [ae_restrict_iff' (Submission.BoseGases.abox_measurable n ℓ)]
        exact Filter.Eventually.of_forall (fun x hx => by
          rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]; exact hQ2 x hx))
  have hmono := integral_mono_ae hf2 (hQint.const_mul Ξ) (Filter.Eventually.of_forall (fun x => by
    show (ch (x i) * Work.UBBInputs8.boxQInd V A i Φ x) ^ 2
      ≤ Ξ * (Work.UBBInputs8.boxQInd V A i Φ x) ^ 2
    nlinarith [hchb (x i), sq_nonneg (Work.UBBInputs8.boxQInd V A i Φ x)]))
  rwa [integral_const_mul] at hmono

/-- Per-slot cross bound: `|∫χ(xᵢ)²(QᵢΦ)(PᵢΦ)| ≤ Ξ√(qᵢpᵢ)`. -/
private theorem slot_cross_le {n : ℕ} {ℓ V Ξ : ℝ}
    {A : Set (EuclideanSpace ℝ (Fin 3))}
    (hℓ : 0 < ℓ) (hΞ0 : 0 ≤ Ξ)
    {ch : EuclideanSpace ℝ (Fin 3) → ℝ} (hchm : Measurable ch)
    (hchb : ∀ z, (ch z) ^ 2 ≤ Ξ)
    {Φ : Submission.BoseGases.X n → ℝ} (hΦc : Continuous Φ)
    (hA : MeasurableSet A) (hV : 0 < V) (hVeq : V = (volume A).toReal)
    (hAc : A ⊆ Submission.BoseGases.acube ℓ) (i : Fin n) :
    |∫ x in Submission.BoseGases.abox n ℓ,
        (ch (x i)) ^ 2 * Work.UBBInputs8.boxQInd V A i Φ x * Work.UBBInputs8.boxPInd V A i Φ x|
      ≤ Ξ * Real.sqrt ((∫ x in Submission.BoseGases.abox n ℓ,
            (Work.UBBInputs8.boxQInd V A i Φ x) ^ 2)
          * (∫ x in Submission.BoseGases.abox n ℓ,
            (Work.UBBInputs8.boxPInd V A i Φ x) ^ 2)) := by
  obtain ⟨C, hC0, hΦb, hPb, hQb⟩ := Work.BoseFixB1S.boxBounds hℓ hV hA hVeq hAc hΦc
  have hQm : Measurable (Work.UBBInputs8.boxQInd V A i Φ) :=
    Work.SlotWord.measurable_boxQInd V A hA i hΦc.measurable
  have hPm : Measurable (Work.UBBInputs8.boxPInd V A i Φ) :=
    Work.BoseFixB1S.measurable_boxPInd V A hA i hΦc.measurable
  have hchi : Measurable (fun x : Submission.BoseGases.X n => ch (x i)) :=
    hchm.comp (measurable_pi_apply i)
  have hQ2 : ∀ x ∈ Submission.BoseGases.abox n ℓ,
      (Work.UBBInputs8.boxQInd V A i Φ x) ^ 2 ≤ (2 * C) ^ 2 := by
    intro x hx
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) (hQb i x hx) 2
  have hP2 : ∀ x ∈ Submission.BoseGases.abox n ℓ,
      (Work.UBBInputs8.boxPInd V A i Φ x) ^ 2 ≤ C ^ 2 := by
    intro x hx
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) (hPb i x hx) 2
  have hf2 : Integrable (fun x : Submission.BoseGases.X n =>
      (ch (x i) * Work.UBBInputs8.boxQInd V A i Φ x) ^ 2)
      ((volume : Measure (Submission.BoseGases.X n)).restrict (Submission.BoseGases.abox n ℓ)) := by
    refine Integrable.congr (f := fun x : Submission.BoseGases.X n =>
      (ch (x i)) ^ 2 * (Work.UBBInputs8.boxQInd V A i Φ x) ^ 2) ?_ ?_
    · refine IntegrableOn.of_bound (Submission.BoseGases.abox_lt_top n ℓ hℓ.le)
        ((hchi.pow_const 2).mul (hQm.pow_const 2)).aestronglyMeasurable (Ξ * (2 * C) ^ 2) ?_
      rw [ae_restrict_iff' (Submission.BoseGases.abox_measurable n ℓ)]
      refine Filter.Eventually.of_forall (fun x hx => ?_)
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _))]
      exact mul_le_mul (hchb (x i)) (hQ2 x hx) (sq_nonneg _) hΞ0
    · filter_upwards with x
      ring
  have hg2 : Integrable (fun x : Submission.BoseGases.X n =>
      (ch (x i) * Work.UBBInputs8.boxPInd V A i Φ x) ^ 2)
      ((volume : Measure (Submission.BoseGases.X n)).restrict (Submission.BoseGases.abox n ℓ)) := by
    refine Integrable.congr (f := fun x : Submission.BoseGases.X n =>
      (ch (x i)) ^ 2 * (Work.UBBInputs8.boxPInd V A i Φ x) ^ 2) ?_ ?_
    · refine IntegrableOn.of_bound (Submission.BoseGases.abox_lt_top n ℓ hℓ.le)
        ((hchi.pow_const 2).mul (hPm.pow_const 2)).aestronglyMeasurable (Ξ * C ^ 2) ?_
      rw [ae_restrict_iff' (Submission.BoseGases.abox_measurable n ℓ)]
      refine Filter.Eventually.of_forall (fun x hx => ?_)
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _))]
      exact mul_le_mul (hchb (x i)) (hP2 x hx) (sq_nonneg _) hΞ0
    · filter_upwards with x
      ring
  have hCS := Work.BoseFixB1S.csIntegralSqLe
    (μ := (volume : Measure (Submission.BoseGases.X n)).restrict (Submission.BoseGases.abox n ℓ))
    (f := fun x : Submission.BoseGases.X n => ch (x i) * Work.UBBInputs8.boxQInd V A i Φ x)
    (g := fun x : Submission.BoseGases.X n => ch (x i) * Work.UBBInputs8.boxPInd V A i Φ x)
    (hchi.mul hQm).aestronglyMeasurable (hchi.mul hPm).aestronglyMeasurable hf2 hg2
  have h0f : (0:ℝ) ≤ ∫ x, (ch (x i) * Work.UBBInputs8.boxQInd V A i Φ x) ^ 2
      ∂((volume : Measure (Submission.BoseGases.X n)).restrict (Submission.BoseGases.abox n ℓ)) :=
    integral_nonneg_of_ae (Filter.Eventually.of_forall (fun x => sq_nonneg _))
  have h0Q : (0:ℝ) ≤ ∫ x in Submission.BoseGases.abox n ℓ,
      (Work.UBBInputs8.boxQInd V A i Φ x) ^ 2 :=
    integral_nonneg_of_ae (Filter.Eventually.of_forall (fun x => sq_nonneg _))
  have hcross : (∫ x, (ch (x i) * Work.UBBInputs8.boxQInd V A i Φ x)
        * (ch (x i) * Work.UBBInputs8.boxPInd V A i Φ x)
      ∂((volume : Measure (Submission.BoseGases.X n)).restrict (Submission.BoseGases.abox n ℓ)))
      = ∫ x in Submission.BoseGases.abox n ℓ,
          (ch (x i)) ^ 2 * Work.UBBInputs8.boxQInd V A i Φ x * Work.UBBInputs8.boxPInd V A i Φ x := by
    apply integral_congr_ae
    filter_upwards with x
    ring
  have hsqQ : (∫ x, (ch (x i) * Work.UBBInputs8.boxQInd V A i Φ x) ^ 2
      ∂((volume : Measure (Submission.BoseGases.X n)).restrict (Submission.BoseGases.abox n ℓ)))
      ≤ Ξ * ∫ x in Submission.BoseGases.abox n ℓ,
          (Work.UBBInputs8.boxQInd V A i Φ x) ^ 2 := by
    have hQint : Integrable (fun x : Submission.BoseGases.X n =>
        (Work.UBBInputs8.boxQInd V A i Φ x) ^ 2)
        ((volume : Measure (Submission.BoseGases.X n)).restrict (Submission.BoseGases.abox n ℓ)) :=
      IntegrableOn.of_bound (Submission.BoseGases.abox_lt_top n ℓ hℓ.le)
        (hQm.pow_const 2).aestronglyMeasurable ((2*C)^2) (by
          rw [ae_restrict_iff' (Submission.BoseGases.abox_measurable n ℓ)]
          exact Filter.Eventually.of_forall (fun x hx => by
            rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]; exact hQ2 x hx))
    have hmono := integral_mono_ae hf2 (hQint.const_mul Ξ) (Filter.Eventually.of_forall (fun x => by
      show (ch (x i) * Work.UBBInputs8.boxQInd V A i Φ x) ^ 2
        ≤ Ξ * (Work.UBBInputs8.boxQInd V A i Φ x) ^ 2
      nlinarith [hchb (x i), sq_nonneg (Work.UBBInputs8.boxQInd V A i Φ x)]))
    rwa [integral_const_mul] at hmono
  have hsqP : (∫ x, (ch (x i) * Work.UBBInputs8.boxPInd V A i Φ x) ^ 2
      ∂((volume : Measure (Submission.BoseGases.X n)).restrict (Submission.BoseGases.abox n ℓ)))
      ≤ Ξ * ∫ x in Submission.BoseGases.abox n ℓ,
          (Work.UBBInputs8.boxPInd V A i Φ x) ^ 2 := by
    have hPint : Integrable (fun x : Submission.BoseGases.X n =>
        (Work.UBBInputs8.boxPInd V A i Φ x) ^ 2)
        ((volume : Measure (Submission.BoseGases.X n)).restrict (Submission.BoseGases.abox n ℓ)) :=
      IntegrableOn.of_bound (Submission.BoseGases.abox_lt_top n ℓ hℓ.le)
        (hPm.pow_const 2).aestronglyMeasurable (C^2) (by
          rw [ae_restrict_iff' (Submission.BoseGases.abox_measurable n ℓ)]
          exact Filter.Eventually.of_forall (fun x hx => by
            rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]; exact hP2 x hx))
    have hmono := integral_mono_ae hg2 (hPint.const_mul Ξ) (Filter.Eventually.of_forall (fun x => by
      show (ch (x i) * Work.UBBInputs8.boxPInd V A i Φ x) ^ 2
        ≤ Ξ * (Work.UBBInputs8.boxPInd V A i Φ x) ^ 2
      nlinarith [hchb (x i), sq_nonneg (Work.UBBInputs8.boxPInd V A i Φ x)]))
    rwa [integral_const_mul] at hmono
  have h1 : Real.sqrt (∫ x, (ch (x i) * Work.UBBInputs8.boxQInd V A i Φ x) ^ 2
        ∂((volume : Measure (Submission.BoseGases.X n)).restrict (Submission.BoseGases.abox n ℓ)))
      ≤ Real.sqrt Ξ * Real.sqrt (∫ x in Submission.BoseGases.abox n ℓ,
          (Work.UBBInputs8.boxQInd V A i Φ x) ^ 2) := by
    calc Real.sqrt (∫ x, (ch (x i) * Work.UBBInputs8.boxQInd V A i Φ x) ^ 2 ∂((volume : Measure (Submission.BoseGases.X n)).restrict (Submission.BoseGases.abox n ℓ)))
        ≤ Real.sqrt (Ξ * ∫ x in Submission.BoseGases.abox n ℓ,
            (Work.UBBInputs8.boxQInd V A i Φ x) ^ 2) := Real.sqrt_le_sqrt hsqQ
      _ = Real.sqrt Ξ * Real.sqrt (∫ x in Submission.BoseGases.abox n ℓ,
            (Work.UBBInputs8.boxQInd V A i Φ x) ^ 2) := Real.sqrt_mul hΞ0 _
  have h2 : Real.sqrt (∫ x, (ch (x i) * Work.UBBInputs8.boxPInd V A i Φ x) ^ 2
        ∂((volume : Measure (Submission.BoseGases.X n)).restrict (Submission.BoseGases.abox n ℓ)))
      ≤ Real.sqrt Ξ * Real.sqrt (∫ x in Submission.BoseGases.abox n ℓ,
          (Work.UBBInputs8.boxPInd V A i Φ x) ^ 2) := by
    calc Real.sqrt (∫ x, (ch (x i) * Work.UBBInputs8.boxPInd V A i Φ x) ^ 2 ∂((volume : Measure (Submission.BoseGases.X n)).restrict (Submission.BoseGases.abox n ℓ)))
        ≤ Real.sqrt (Ξ * ∫ x in Submission.BoseGases.abox n ℓ,
            (Work.UBBInputs8.boxPInd V A i Φ x) ^ 2) := Real.sqrt_le_sqrt hsqP
      _ = Real.sqrt Ξ * Real.sqrt (∫ x in Submission.BoseGases.abox n ℓ,
            (Work.UBBInputs8.boxPInd V A i Φ x) ^ 2) := Real.sqrt_mul hΞ0 _
  calc |∫ x in Submission.BoseGases.abox n ℓ,
        (ch (x i)) ^ 2 * Work.UBBInputs8.boxQInd V A i Φ x * Work.UBBInputs8.boxPInd V A i Φ x|
      = |∫ x, (ch (x i) * Work.UBBInputs8.boxQInd V A i Φ x)
          * (ch (x i) * Work.UBBInputs8.boxPInd V A i Φ x)
          ∂((volume : Measure (Submission.BoseGases.X n)).restrict (Submission.BoseGases.abox n ℓ))| := by
        rw [hcross]
    _ = Real.sqrt ((∫ x, (ch (x i) * Work.UBBInputs8.boxQInd V A i Φ x)
          * (ch (x i) * Work.UBBInputs8.boxPInd V A i Φ x)
          ∂((volume : Measure (Submission.BoseGases.X n)).restrict (Submission.BoseGases.abox n ℓ))) ^ 2) :=
        (Real.sqrt_sq_eq_abs _).symm
    _ ≤ Real.sqrt ((∫ x, (ch (x i) * Work.UBBInputs8.boxQInd V A i Φ x) ^ 2
          ∂((volume : Measure (Submission.BoseGases.X n)).restrict (Submission.BoseGases.abox n ℓ)))
        * ∫ x, (ch (x i) * Work.UBBInputs8.boxPInd V A i Φ x) ^ 2
          ∂((volume : Measure (Submission.BoseGases.X n)).restrict (Submission.BoseGases.abox n ℓ))) :=
        Real.sqrt_le_sqrt hCS
    _ = Real.sqrt (∫ x, (ch (x i) * Work.UBBInputs8.boxQInd V A i Φ x) ^ 2
          ∂((volume : Measure (Submission.BoseGases.X n)).restrict (Submission.BoseGases.abox n ℓ)))
        * Real.sqrt (∫ x, (ch (x i) * Work.UBBInputs8.boxPInd V A i Φ x) ^ 2
          ∂((volume : Measure (Submission.BoseGases.X n)).restrict (Submission.BoseGases.abox n ℓ))) :=
        Real.sqrt_mul h0f _
    _ ≤ (Real.sqrt Ξ * Real.sqrt (∫ x in Submission.BoseGases.abox n ℓ,
            (Work.UBBInputs8.boxQInd V A i Φ x) ^ 2))
        * (Real.sqrt Ξ * Real.sqrt (∫ x in Submission.BoseGases.abox n ℓ,
            (Work.UBBInputs8.boxPInd V A i Φ x) ^ 2)) :=
        mul_le_mul h1 h2 (Real.sqrt_nonneg _) (le_trans (Real.sqrt_nonneg _) h1)
    _ = Ξ * Real.sqrt ((∫ x in Submission.BoseGases.abox n ℓ,
            (Work.UBBInputs8.boxQInd V A i Φ x) ^ 2)
          * (∫ x in Submission.BoseGases.abox n ℓ,
            (Work.UBBInputs8.boxPInd V A i Φ x) ^ 2)) := by
        have hregroup : Real.sqrt Ξ * Real.sqrt (∫ x in Submission.BoseGases.abox n ℓ, (Work.UBBInputs8.boxQInd V A i Φ x) ^ 2)
            * (Real.sqrt Ξ * Real.sqrt (∫ x in Submission.BoseGases.abox n ℓ, (Work.UBBInputs8.boxPInd V A i Φ x) ^ 2))
            = (Real.sqrt Ξ * Real.sqrt Ξ) * (Real.sqrt (∫ x in Submission.BoseGases.abox n ℓ, (Work.UBBInputs8.boxQInd V A i Φ x) ^ 2) * Real.sqrt (∫ x in Submission.BoseGases.abox n ℓ, (Work.UBBInputs8.boxPInd V A i Φ x) ^ 2)) := by ring
        rw [hregroup, Real.mul_self_sqrt hΞ0,
          Real.sqrt_mul h0Q (∫ x in Submission.BoseGases.abox n ℓ, (Work.UBBInputs8.boxPInd V A i Φ x) ^ 2)]

theorem abs_boxQCross_le {M : ℕ} (hM : 1 ≤ M) {ℓ d : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d) (u : EuclideanSpace ℝ (Fin 3)) {n : ℕ} {Φ : Submission.BoseGases.X n → ℝ} (hΦc : Continuous Φ) (hV : 0 < Work.SmallBoxSliding.boxMass ℓ d u) {Ξ : ℝ} (hΞ0 : 0 ≤ Ξ) (hΞ : ∀ z : EuclideanSpace ℝ (Fin 3), (Submission.BoseGases.chiSmallB M ℓ d u z) ^ 2 ≤ Ξ) : |(∑ i : Fin n, ∫ x in Submission.BoseGases.abox n ℓ, (Submission.BoseGases.chiSmallB M ℓ d u (x i) * Work.UBBInputs8.boxQInd (Work.SmallBoxSliding.boxMass ℓ d u) (Submission.BoseGases.dlBox ℓ d u) i Φ x) ^ 2) + 2 * (∑ i : Fin n, ∫ x in Submission.BoseGases.abox n ℓ, (Submission.BoseGases.chiSmallB M ℓ d u (x i)) ^ 2 * Work.UBBInputs8.boxQInd (Work.SmallBoxSliding.boxMass ℓ d u) (Submission.BoseGases.dlBox ℓ d u) i Φ x * Work.UBBInputs8.boxPInd (Work.SmallBoxSliding.boxMass ℓ d u) (Submission.BoseGases.dlBox ℓ d u) i Φ x)| ≤ Ξ * (2 * Real.sqrt (Work.BoseFixB1S.boxFlatCount (Work.SmallBoxSliding.boxMass ℓ d u) ℓ (Submission.BoseGases.dlBox ℓ d u) Φ * Work.BoseFixB1S.boxQCount (Work.SmallBoxSliding.boxMass ℓ d u) ℓ (Submission.BoseGases.dlBox ℓ d u) Φ) + Work.BoseFixB1S.boxQCount (Work.SmallBoxSliding.boxMass ℓ d u) ℓ (Submission.BoseGases.dlBox ℓ d u) Φ) := by
  have hA : MeasurableSet (Submission.BoseGases.dlBox ℓ d u) :=
    Work.SmallBoxSliding.measurableSet_dlBox ℓ d u
  have hAc : Submission.BoseGases.dlBox ℓ d u ⊆ Submission.BoseGases.acube ℓ :=
    Work.SmallBoxSliding.dlBox_subset_acube ℓ d u
  have hVeq : Work.SmallBoxSliding.boxMass ℓ d u
      = (volume (Submission.BoseGases.dlBox ℓ d u)).toReal := by
    rw [Work.SmallBoxSliding.boxMass_eq_measureReal, Measure.real_def]
  have hchm : Measurable (fun z : EuclideanSpace ℝ (Fin 3) =>
      Submission.BoseGases.chiSmallB M ℓ d u z) := by
    have hcont : Continuous (fun z : EuclideanSpace ℝ (Fin 3) =>
        Submission.BoseGases.chiSmallB M ℓ d u z) := by
      unfold Submission.BoseGases.chiSmallB
      exact (Submission.BoseGases.chiScale_continuous ℓ).mul
        (((Submission.BoseGases.chiSmallBase_continuous M).div_const _).comp
          ((continuous_id.const_smul ((ℓ * d)⁻¹)).sub continuous_const))
    exact hcont.measurable
  rw [Work.BoseFixB1S.boxFlatCount, Work.BoseFixB1S.boxQCount]
  refine sum_slot_bound hΞ0
    (A := fun i : Fin n => ∫ x in Submission.BoseGases.abox n ℓ, (Submission.BoseGases.chiSmallB M ℓ d u (x i) * Work.UBBInputs8.boxQInd (Work.SmallBoxSliding.boxMass ℓ d u) (Submission.BoseGases.dlBox ℓ d u) i Φ x) ^ 2)
    (B := fun i : Fin n => ∫ x in Submission.BoseGases.abox n ℓ, (Submission.BoseGases.chiSmallB M ℓ d u (x i)) ^ 2 * Work.UBBInputs8.boxQInd (Work.SmallBoxSliding.boxMass ℓ d u) (Submission.BoseGases.dlBox ℓ d u) i Φ x * Work.UBBInputs8.boxPInd (Work.SmallBoxSliding.boxMass ℓ d u) (Submission.BoseGases.dlBox ℓ d u) i Φ x)
    (a := fun i : Fin n => ∫ x in Submission.BoseGases.abox n ℓ, (Work.UBBInputs8.boxQInd (Work.SmallBoxSliding.boxMass ℓ d u) (Submission.BoseGases.dlBox ℓ d u) i Φ x) ^ 2)
    (b := fun i : Fin n => ∫ x in Submission.BoseGases.abox n ℓ, (Work.UBBInputs8.boxPInd (Work.SmallBoxSliding.boxMass ℓ d u) (Submission.BoseGases.dlBox ℓ d u) i Φ x) ^ 2)
    ?_ ?_ ?_ ?_ ?_
  · intro i
    exact integral_nonneg_of_ae (Filter.Eventually.of_forall (fun x => sq_nonneg _))
  · intro i
    exact integral_nonneg_of_ae (Filter.Eventually.of_forall (fun x => sq_nonneg _))
  · intro i
    exact integral_nonneg_of_ae (Filter.Eventually.of_forall (fun x => sq_nonneg _))
  · intro i
    exact slot_sq_le hℓ hΞ0 hchm hΞ hΦc hA hV hVeq hAc i
  · intro i
    exact slot_cross_le hℓ hΞ0 hchm hΞ hΦc hA hV hVeq hAc i

end Work.BoseB1Cube
