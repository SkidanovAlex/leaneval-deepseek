import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB1P.boxQ1_pair_replace
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

noncomputable section

open MeasureTheory
open scoped Real BigOperators ENNReal

namespace Work.BoseFixB1

open Submission.BoseGases

set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

theorem boxQ1_pair_replace_fibre {N : ℕ} {ℓ V : ℝ} (hℓ : 0 < ℓ) (hV : 0 < V)
    {A : Set (EuclideanSpace ℝ (Fin 3))} (hA : MeasurableSet A)
    (hAc : A ⊆ Submission.BoseGases.acube ℓ)
    (hVeq : V = (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))).real A)
    {fib : EuclideanSpace ℝ (Fin 3) → ℝ}
    (hFm : MeasureTheory.AEStronglyMeasurable fib
      (MeasureTheory.volume.restrict (Submission.BoseGases.acube ℓ)))
    {C : ℝ} (hC : ∀ z ∈ Submission.BoseGases.acube ℓ, |fib z| ≤ C)
    {Φ : Submission.BoseGases.X N → ℝ} (hΦc : Continuous Φ)
    {s t : Fin N} (hst : s ≠ t) :
    (∫ x in Submission.BoseGases.abox N ℓ,
        (Work.UBBInputs8.boxPInd V A s (Work.UBBInputs8.boxQInd V A t Φ) x)
          * (Work.UBBInputs8.boxPInd V A s (Work.UBBInputs8.boxPInd V A t Φ) x) * fib (x t))
      = (∫ x in Submission.BoseGases.abox N ℓ,
          (Work.UBBInputs8.boxQInd V A t Φ x) * fib (x t)
            * (Work.UBBInputs8.boxPInd V A s (Work.UBBInputs8.boxPInd V A t Φ) x)) := by
  -- a global bound for the continuous state on the compact box
  obtain ⟨B, hB⟩ := (abox_compact N hℓ).exists_bound_of_continuousOn
    (s := abox N ℓ) (f := Φ) hΦc.continuousOn
  have hΦb : ∀ x ∈ abox N ℓ, |Φ x| ≤ |B| := by
    intro x hx
    have h1 : |Φ x| ≤ B := by simpa [Real.norm_eq_abs] using hB x hx
    exact le_trans h1 (le_abs_self B)
  have hmP : Measurable (Work.UBBInputs8.boxPInd V A t Φ) :=
    Work.BoseFixB1S.measurable_boxPInd V A hA t hΦc.measurable
  have hmQ : Measurable (Work.UBBInputs8.boxQInd V A t Φ) :=
    Work.BoseFixB1S.measurable_boxQInd V hA t hΦc.measurable
  have hPb : ∀ x ∈ abox N ℓ, |Work.UBBInputs8.boxPInd V A t Φ x| ≤ |B| :=
    Work.BoseFixB1S.abs_boxPInd_le hℓ hV hA hVeq hAc t hΦb
  have hQb : ∀ x ∈ abox N ℓ, |Work.UBBInputs8.boxQInd V A t Φ x| ≤ 2 * |B| :=
    Work.BoseFixB1S.abs_boxQInd_le_two hℓ hV hA hVeq hAc t hΦb
  -- the weight `fib (· t)`, which does not see slot `s`
  have hwm : MeasureTheory.AEStronglyMeasurable
      (fun x : Submission.BoseGases.X N => fib (x t))
      (MeasureTheory.volume.restrict (Submission.BoseGases.abox N ℓ)) :=
    Submission.BoseGases.aem_comp_coord' (N := N) (ℓ := ℓ) t hFm
  have hwb : ∀ x ∈ abox N ℓ, |(fun x : Submission.BoseGases.X N => fib (x t)) x| ≤ |C| := by
    intro x hx
    exact le_trans (hC (x t) (hx t)) (le_abs_self C)
  have hw : ∀ (x : Submission.BoseGases.X N) (y : EuclideanSpace ℝ (Fin 3)),
      (fun x : Submission.BoseGases.X N => fib (x t)) (Function.update x s y)
        = (fun x : Submission.BoseGases.X N => fib (x t)) x := by
    intro x y
    show fib ((Function.update x s y) t) = fib (x t)
    rw [Function.update_of_ne hst.symm y x]
  -- the weighted collapse, with the two factors in the order `(P_sP_t Φ)`, `(P_sQ_t Φ)`
  have hcoll := Work.BoseFixB1P.boxPInd_mulWeight (hℓ := hℓ) (hvol := hV) (hA := hA)
    (hvolA := hVeq) (hAc := hAc) (i := s)
    (Θ := Work.UBBInputs8.boxPInd V A t Φ) (Λ := Work.UBBInputs8.boxQInd V A t Φ)
    (hΘm := hmP) (hΘb := hPb) (hΛm := hmQ) (hΛb := hQb)
    (hwm := hwm) (hwb := hwb) (hw := hw)
  have hcoll' : (∫ x in abox N ℓ,
        Work.UBBInputs8.boxPInd V A s (Work.UBBInputs8.boxPInd V A t Φ) x
          * Work.UBBInputs8.boxPInd V A s (Work.UBBInputs8.boxQInd V A t Φ) x * fib (x t))
      = ∫ x in abox N ℓ,
        Work.UBBInputs8.boxPInd V A s (Work.UBBInputs8.boxPInd V A t Φ) x
          * Work.UBBInputs8.boxQInd V A t Φ x * fib (x t) := by
    simpa only [] using hcoll
  -- both integrands are pointwise rearrangements of the collapsed ones
  have hL : (∫ x in abox N ℓ,
        Work.UBBInputs8.boxPInd V A s (Work.UBBInputs8.boxQInd V A t Φ) x
          * Work.UBBInputs8.boxPInd V A s (Work.UBBInputs8.boxPInd V A t Φ) x * fib (x t))
      = ∫ x in abox N ℓ,
        Work.UBBInputs8.boxPInd V A s (Work.UBBInputs8.boxPInd V A t Φ) x
          * Work.UBBInputs8.boxPInd V A s (Work.UBBInputs8.boxQInd V A t Φ) x * fib (x t) :=
    MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun x => by ring))
  have hR : (∫ x in abox N ℓ,
        Work.UBBInputs8.boxPInd V A s (Work.UBBInputs8.boxPInd V A t Φ) x
          * Work.UBBInputs8.boxQInd V A t Φ x * fib (x t))
      = ∫ x in abox N ℓ,
        Work.UBBInputs8.boxQInd V A t Φ x * fib (x t)
          * Work.UBBInputs8.boxPInd V A s (Work.UBBInputs8.boxPInd V A t Φ) x :=
    MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun x => by ring))
  rw [hL, hcoll', hR]

end Work.BoseFixB1
