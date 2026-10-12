import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB1S.BoxPotOper
import Submission.Work.BoseFixB1S.integrableOn_boxQInd_sq
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB1S.mfFewFlatCornerStep1` — step 1 of `(CORNER)`

`(CORNER)` (see `FINDING_mfSection10FewB1_session3.md` §8) is the `n₊ → 0` corner of the
target's ledger, at the target's data with `∫Φ² = 1`:

    ½(M₁/V²)(mfS² − mfS) ≤ mfSig      when  mfQ = 0 .

Its sharp route has three steps; **step 1** is here: the excited count vanishing forces the box
projections to collapse, i.e. with `Qᵢ := Work.UBBInputs8.boxQInd V A i Φ`,

    (Σᵢ∫(QᵢΦ)² = 0)  ⟹  ∀ᵐ x, ∀ i, QᵢΦ x = 0  ⟹  ∀ᵐ x, ∀ i, 1_A(xᵢ)·Φ x = PᵢΦ x ,

(the last step being the *definition* of `boxQInd`).  Consequently `1_A(xᵢ)1_A(xⱼ)Φ = PᵢPⱼΦ`
a.e. for all ordered pairs `(i,j)`, which is what lets `Work.BoseFixB1S.boxWeightedPairMass`
turn `mfSig` into `½(∬_{A×A}w/V²)·Pc` (steps 2–3 then finish `(CORNER)`).
-/

noncomputable section

open MeasureTheory
open scoped Real BigOperators

namespace Work.BoseFixB1S

open Submission.BoseGases

set_option autoImplicit false
set_option linter.unusedVariables false

/-- `∫Φ²` is integrable on the analysis box for a continuous state. -/
private theorem integrableOn_sq_of_continuous {N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ)
    {Φ : Submission.BoseGases.X N → ℝ} (hΦc : Continuous Φ) :
    MeasureTheory.IntegrableOn (fun x : Submission.BoseGases.X N => (Φ x) ^ 2)
      (Submission.BoseGases.abox N ℓ) MeasureTheory.volume := by
  obtain ⟨C, hC0, hC⟩ := Work.BoseFixB1S.exists_abox_bound hℓ hΦc
  exact MeasureTheory.IntegrableOn.of_bound (Submission.BoseGases.abox_lt_top N ℓ hℓ.le)
    (hΦc.measurable.aestronglyMeasurable.pow 2) (C ^ 2) (by
      rw [MeasureTheory.ae_restrict_iff' (Submission.BoseGases.abox_measurable N ℓ)]
      refine Filter.Eventually.of_forall (fun x hx => ?_)
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), sq_le_sq, abs_of_nonneg hC0]
      exact hC x hx)

/-- **Step 1 of `(CORNER)`.**  If the box excited count vanishes then every `QᵢΦ` vanishes
a.e. on the analysis box. -/
theorem boxQInd_ae_zero_of_boxQCount_eq_zero {N : ℕ} {ℓ V : ℝ} (hℓ : 0 < ℓ) (hV : 0 < V)
    {A : Set (EuclideanSpace ℝ (Fin 3))} (hA : MeasurableSet A)
    (hVeq : V = (MeasureTheory.volume A).toReal)
    (hAc : A ⊆ Submission.BoseGases.acube ℓ)
    {Φ : Submission.BoseGases.X N → ℝ} (hΦc : Continuous Φ)
    (hQ : Work.BoseFixB1S.boxQCount V ℓ A Φ = 0) :
    ∀ i : Fin N, ∀ᵐ x ∂(MeasureTheory.volume.restrict (Submission.BoseGases.abox N ℓ)),
      Work.UBBInputs8.boxQInd V A i Φ x = 0 := by
  have hΦ2 := integrableOn_sq_of_continuous (N := N) (ℓ := ℓ) hℓ hΦc
  have hint : ∀ i : Fin N, MeasureTheory.Integrable
      (fun x : Submission.BoseGases.X N => (Work.UBBInputs8.boxQInd V A i Φ x) ^ 2)
      ((MeasureTheory.volume : MeasureTheory.Measure (Submission.BoseGases.X N)).restrict
        (Submission.BoseGases.abox N ℓ)) := fun i =>
    Work.BoseFixB1S.integrableOn_boxQInd_sq hVeq hV hA hAc i Φ
      hΦc.aestronglyMeasurable hΦ2
  have hsum : (∑ i : Fin N, ∫ x in Submission.BoseGases.abox N ℓ,
      (Work.UBBInputs8.boxQInd V A i Φ x) ^ 2) = 0 := by
    simpa only [Work.BoseFixB1S.boxQCount] using hQ
  have hterm : ∀ i : Fin N, (∫ x in Submission.BoseGases.abox N ℓ,
      (Work.UBBInputs8.boxQInd V A i Φ x) ^ 2) = 0 := fun i =>
    (Finset.sum_eq_zero_iff_of_nonneg
      (fun j _ => MeasureTheory.integral_nonneg fun x => sq_nonneg _)).mp hsum i
      (Finset.mem_univ i)
  intro i
  have hz : (fun x : Submission.BoseGases.X N => (Work.UBBInputs8.boxQInd V A i Φ x) ^ 2)
      =ᵐ[((MeasureTheory.volume : MeasureTheory.Measure (Submission.BoseGases.X N)).restrict
        (Submission.BoseGases.abox N ℓ))] 0 :=
    (MeasureTheory.integral_eq_zero_iff_of_nonneg (fun x => sq_nonneg _) (hint i)).mp
      (hterm i)
  filter_upwards [hz] with x hx
  simpa using pow_eq_zero_iff (n := 2) (by norm_num) |>.mp hx

/-- **Step 1 of `(CORNER)`, collapsed form**: if the box excited count vanishes then
`1_A(xᵢ)·Φ = PᵢΦ` a.e. for every slot. -/
theorem indicator_mul_eq_boxPInd_of_boxQCount_eq_zero {N : ℕ} {ℓ V : ℝ} (hℓ : 0 < ℓ) (hV : 0 < V)
    {A : Set (EuclideanSpace ℝ (Fin 3))} (hA : MeasurableSet A)
    (hVeq : V = (MeasureTheory.volume A).toReal)
    (hAc : A ⊆ Submission.BoseGases.acube ℓ)
    {Φ : Submission.BoseGases.X N → ℝ} (hΦc : Continuous Φ)
    (hQ : Work.BoseFixB1S.boxQCount V ℓ A Φ = 0) :
    ∀ i : Fin N, ∀ᵐ x ∂(MeasureTheory.volume.restrict (Submission.BoseGases.abox N ℓ)),
      A.indicator (fun _ => (1 : ℝ)) (x i) * Φ x
        = Work.UBBInputs8.boxPInd V A i Φ x := by
  intro i
  filter_upwards [boxQInd_ae_zero_of_boxQCount_eq_zero hℓ hV hA hVeq hAc hΦc hQ i] with x hx
  have hx' : A.indicator (fun _ => (1 : ℝ)) (x i) * Φ x
      - Work.UBBInputs8.boxPInd V A i Φ x = 0 := hx
  linarith

end Work.BoseFixB1S
