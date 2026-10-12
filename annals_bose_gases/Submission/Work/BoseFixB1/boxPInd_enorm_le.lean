import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB1S.BoxPIndFlat
import Submission.Work.BoseFixB1S.BoxQIndCore
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

noncomputable section

open MeasureTheory
open scoped ENNReal BigOperators

namespace Work.BoseFixB1

open Submission.BoseGases

set_option maxHeartbeats 800000

namespace PIndAux

/-! ## 1. The peel of a `lintegral` along the slot insertion `kcInsN` -/

/-- Transport of a `lintegral` over the box `abox (n+1) ℓ` to the product of the `i`-th slot and
the remaining coordinates, along the measure-preserving insertion `kcInsN`. -/
theorem lintegral_abox_peel {n : ℕ} {ℓ : ℝ} (i : Fin (n + 1)) {g : X (n + 1) → ENNReal}
    (hg : Measurable g) :
    ∫⁻ x in abox (n + 1) ℓ, g x =
      ∫⁻ q : EuclideanSpace ℝ (Fin 3) × X n, g ((kcInsN n i) q) ∂
        (((volume : Measure (EuclideanSpace ℝ (Fin 3))).restrict (acube ℓ)).prod
          ((volume : Measure (X n)).restrict (abox n ℓ))) := by
  have hmp := abox_peel_mp (n := n) ℓ i
  have h := hmp.lintegral_comp (f := fun q : EuclideanSpace ℝ (Fin 3) × X n => g ((kcInsN n i) q))
    (hg.comp (kcInsN n i).measurable)
  have hfun : (fun x : X (n + 1) => g ((kcInsN n i)
      ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => EuclideanSpace ℝ (Fin 3)) i) x)))
      = g := by
    funext x
    simp only [kcInsN, MeasurableEquiv.symm_apply_apply]
  rw [hfun] at h
  rw [h]

/-! ## 2. The pointwise bound at an inserted configuration -/

/-- At an inserted configuration the box projection is the box indicator times the (slot
independent) fibre mean, and the fibre mean is bounded in `L¹` by the integrand of the `z`-mean
over the whole cube. -/
theorem enorm_boxPInd_kcInsN_le {n : ℕ} {ℓ V : ℝ} (hV : 0 < V)
    {A : Set (EuclideanSpace ℝ (Fin 3))} (hAc : A ⊆ acube ℓ) (i : Fin (n + 1))
    (Ψ : X (n + 1) → ℝ) (t : EuclideanSpace ℝ (Fin 3)) (r : X n) :
    ‖UBBInputs8.boxPInd V A i Ψ (kcInsN n i (t, r))‖ₑ ≤
      ENNReal.ofReal (A.indicator (fun _ => (1 : ℝ)) t) *
        (ENNReal.ofReal (1 / V) *
          ∫⁻ z in acube ℓ, ‖Ψ (kcInsN n i (z, r))‖ₑ) := by
  rw [BoseFixB1S.Q0C.boxPInd_kcInsN V A i Ψ t r, enorm_mul, enorm_mul]
  have h1 : ‖A.indicator (fun _ => (1 : ℝ)) t‖ₑ
      = ENNReal.ofReal (A.indicator (fun _ => (1 : ℝ)) t) := by
    rw [Real.enorm_eq_ofReal_abs,
      abs_of_nonneg (Set.indicator_nonneg (fun _ _ => zero_le_one) t)]
  have h2 : ‖(1 / V : ℝ)‖ₑ = ENNReal.ofReal (1 / V) := by
    rw [Real.enorm_eq_ofReal_abs, abs_of_pos (one_div_pos.mpr hV)]
  rw [h1, h2]
  refine mul_le_mul' le_rfl (mul_le_mul' le_rfl ?_)
  refine le_trans (enorm_integral_le_lintegral_enorm (fun z : EuclideanSpace ℝ (Fin 3) =>
    Ψ (kcInsN n i (z, r)))) (lintegral_mono_set hAc)

/-! ## 3. The product-measure computation -/

/-- The product-measure integral of the indicator times the (slot-independent) `z`-mean: the
indicator integrates to `volA = V`, which cancels the `V⁻¹` of the fibre mean. -/
theorem lintegral_prod_indicator_mul {n : ℕ} {ℓ V : ℝ} (hℓ : 0 < ℓ) (hV : 0 < V)
    {A : Set (EuclideanSpace ℝ (Fin 3))} (hA : MeasurableSet A) (hAc : A ⊆ acube ℓ)
    (hVeq : V = (volume A).toReal)
    {G : X n → ENNReal} (hG : Measurable G) :
    ∫⁻ q : EuclideanSpace ℝ (Fin 3) × X n,
        ENNReal.ofReal (A.indicator (fun _ => (1 : ℝ)) q.1) *
          (ENNReal.ofReal (1 / V) * G q.2) ∂
        (((volume : Measure (EuclideanSpace ℝ (Fin 3))).restrict (acube ℓ)).prod
          ((volume : Measure (X n)).restrict (abox n ℓ)))
      = ∫⁻ r in abox n ℓ, G r := by
  have hσeq : (fun t : EuclideanSpace ℝ (Fin 3) =>
        ENNReal.ofReal (A.indicator (fun _ => (1 : ℝ)) t))
      = A.indicator (fun _ => (1 : ENNReal)) := by
    funext t
    by_cases ht : t ∈ A <;> simp [Set.indicator_of_mem, Set.indicator_of_notMem, ht]
  have hσmeas : AEMeasurable (fun t : EuclideanSpace ℝ (Fin 3) =>
      ENNReal.ofReal (A.indicator (fun _ => (1 : ℝ)) t))
      ((volume : Measure (EuclideanSpace ℝ (Fin 3))).restrict (acube ℓ)) :=
    ((ENNReal.measurable_ofReal.comp (measurable_const.indicator hA))).aemeasurable
  have hGmeas : AEMeasurable (fun r : X n => ENNReal.ofReal (1 / V) * G r)
      ((volume : Measure (X n)).restrict (abox n ℓ)) :=
    (Measurable.mul (measurable_const (a := ENNReal.ofReal (1 / V))) hG).aemeasurable
  have hfirst : ∫⁻ t, ENNReal.ofReal (A.indicator (fun _ => (1 : ℝ)) t)
      ∂((volume : Measure (EuclideanSpace ℝ (Fin 3))).restrict (acube ℓ))
      = ENNReal.ofReal V := by
    have h1 : (∫⁻ t, ENNReal.ofReal (A.indicator (fun _ => (1 : ℝ)) t)
        ∂((volume : Measure (EuclideanSpace ℝ (Fin 3))).restrict (acube ℓ)))
        = ((volume : Measure (EuclideanSpace ℝ (Fin 3))).restrict (acube ℓ)) A := by
      rw [← lintegral_indicator_one (μ := (volume : Measure (EuclideanSpace ℝ (Fin 3))).restrict
        (acube ℓ)) hA]
      exact lintegral_congr (fun t => congrFun hσeq t)
    rw [h1, Measure.restrict_apply hA, Set.inter_eq_left.mpr hAc, hVeq,
      ENNReal.ofReal_toReal (ne_of_lt (BoseFixB1S.volume_A_lt_top hℓ hAc))]
  have hsecond : ∫⁻ r, ENNReal.ofReal (1 / V) * G r
      ∂((volume : Measure (X n)).restrict (abox n ℓ))
      = ENNReal.ofReal (1 / V) * ∫⁻ r, G r
        ∂((volume : Measure (X n)).restrict (abox n ℓ)) :=
    lintegral_const_mul _ hG
  rw [lintegral_prod_mul hσmeas hGmeas, hfirst, hsecond]
  have hV1 : ENNReal.ofReal V * ENNReal.ofReal (1 / V) = 1 := by
    rw [← ENNReal.ofReal_mul hV.le, mul_one_div, div_self hV.ne', ENNReal.ofReal_one]
  rw [← mul_assoc, hV1, one_mul]

end PIndAux

/-! ## 4. The contraction -/

theorem boxPInd_enorm_le {N : ℕ} {ℓ V : ℝ} (hℓ : 0 < ℓ) (hV : 0 < V)
    {A : Set (EuclideanSpace ℝ (Fin 3))} (hA : MeasurableSet A)
    (hVeq : V = (MeasureTheory.volume A).toReal) (hAc : A ⊆ Submission.BoseGases.acube ℓ)
    (i : Fin N) {Ψ : Submission.BoseGases.X N → ℝ} (hΨm : Measurable Ψ) :
    ∫⁻ x in Submission.BoseGases.abox N ℓ, ‖Work.UBBInputs8.boxPInd V A i Ψ x‖ₑ ≤
      ∫⁻ x in Submission.BoseGases.abox N ℓ, ‖Ψ x‖ₑ := by
  cases N with
  | zero => exact i.elim0
  | succ n =>
    -- the slot-independent `z`-mean of `‖Ψ‖` over the cube
    set G : X n → ENNReal := fun r => ∫⁻ z in acube ℓ, ‖Ψ (kcInsN n i (z, r))‖ₑ with hGdef
    have hG : Measurable G := by
      have hjoint : Measurable (fun p : X n × EuclideanSpace ℝ (Fin 3) =>
          (acube ℓ).indicator (fun _ => (1 : ENNReal)) p.2 *
            ‖Ψ (kcInsN n i (p.2, p.1))‖ₑ) := by
        refine Measurable.mul ?_ ?_
        · exact (measurable_const.indicator (acube_measurable ℓ)).comp measurable_snd
        · exact hΨm.enorm.comp (by fun_prop)
      have hl := hjoint.lintegral_prod_right' (ν := (volume : Measure (EuclideanSpace ℝ (Fin 3))))
      have hfun : (fun r : X n => ∫⁻ z,
          (acube ℓ).indicator (fun _ => (1 : ENNReal)) z * ‖Ψ (kcInsN n i (z, r))‖ₑ) = G := by
        funext r
        show (∫⁻ z, (acube ℓ).indicator (fun _ => (1 : ENNReal)) z *
            ‖Ψ (kcInsN n i (z, r))‖ₑ) = ∫⁻ z in acube ℓ, ‖Ψ (kcInsN n i (z, r))‖ₑ
        rw [← lintegral_indicator (acube_measurable ℓ)]
        refine lintegral_congr (fun z => ?_)
        by_cases hz : z ∈ acube ℓ <;> simp [Set.indicator_of_mem, Set.indicator_of_notMem, hz]
      rwa [hfun] at hl
    -- peel both sides to the product of the `i`-th slot and the remaining coordinates
    rw [PIndAux.lintegral_abox_peel (ℓ := ℓ) i
        (BoseFixB1S.measurable_boxPInd V A hA i hΨm).enorm,
      PIndAux.lintegral_abox_peel (ℓ := ℓ) i hΨm.enorm]
    have hmono : (∫⁻ q : EuclideanSpace ℝ (Fin 3) × X n,
          ‖UBBInputs8.boxPInd V A i Ψ ((kcInsN n i) q)‖ₑ ∂
          (((volume : Measure (EuclideanSpace ℝ (Fin 3))).restrict (acube ℓ)).prod
            ((volume : Measure (X n)).restrict (abox n ℓ))))
        ≤ ∫⁻ q : EuclideanSpace ℝ (Fin 3) × X n,
            ENNReal.ofReal (A.indicator (fun _ => (1 : ℝ)) q.1) *
              (ENNReal.ofReal (1 / V) * G q.2) ∂
          (((volume : Measure (EuclideanSpace ℝ (Fin 3))).restrict (acube ℓ)).prod
            ((volume : Measure (X n)).restrict (abox n ℓ))) :=
      lintegral_mono (fun q => PIndAux.enorm_boxPInd_kcInsN_le hV hAc i Ψ q.1 q.2)
    refine le_trans hmono ?_
    rw [PIndAux.lintegral_prod_indicator_mul hℓ hV hA hAc hVeq hG]
    -- the remaining inequality is Tonelli in the two peeled variables
    have hfinal : (∫⁻ q : EuclideanSpace ℝ (Fin 3) × X n, ‖Ψ ((kcInsN n i) q)‖ₑ ∂
          (((volume : Measure (EuclideanSpace ℝ (Fin 3))).restrict (acube ℓ)).prod
            ((volume : Measure (X n)).restrict (abox n ℓ))))
        = ∫⁻ r in abox n ℓ, G r := by
      rw [lintegral_prod_symm (fun q : EuclideanSpace ℝ (Fin 3) × X n =>
        ‖Ψ ((kcInsN n i) q)‖ₑ) ((hΨm.enorm.comp (kcInsN n i).measurable).aemeasurable)]
    rw [← hfinal]

end Work.BoseFixB1
