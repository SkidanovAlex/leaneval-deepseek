import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB1.Defs
import Submission.Work.BoseFixB1B.integral_abox_indep_mul_coord
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseFixB1

theorem sumAPsqMulFibre {N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ)
    {Φ : Submission.BoseGases.X N → ℝ} (hΦc : Continuous Φ)
    {f : EuclideanSpace ℝ (Fin 3) → ℝ}
    (hfm : MeasureTheory.AEStronglyMeasurable f
      (MeasureTheory.volume.restrict (Submission.BoseGases.acube ℓ)))
    {B : ℝ} (hB0 : 0 ≤ B)
    (hfb : ∀ z ∈ Submission.BoseGases.acube ℓ, |f z| ≤ B) :
    (∑ i : Fin N, ∫ x in Submission.BoseGases.abox N ℓ,
        (Submission.BoseGases.aP ℓ i Φ x) ^ 2 * f (x i))
      = (Submission.BoseGases.cS1 ℓ Φ / ℓ ^ 3)
          * (∫ z in Submission.BoseGases.acube ℓ, f z) := by
  -- `f` is integrable on the centred cube: measurable and bounded there, finite volume.
  have hIntf : MeasureTheory.IntegrableOn f (Submission.BoseGases.acube ℓ) MeasureTheory.volume := by
    refine MeasureTheory.IntegrableOn.of_bound ?hs hfm B ?hbnd
    · rw [Submission.BoseGases.acube_volume ℓ hℓ.le]
      exact ENNReal.ofReal_lt_top
    · rw [MeasureTheory.ae_restrict_iff' (Submission.BoseGases.acube_measurable ℓ)]
      exact Filter.Eventually.of_forall fun z hz => by
        rw [Real.norm_eq_abs]; exact hfb z hz
  -- per-slot identity: peel coordinate `i` out of the box integral
  have hslot : ∀ i : Fin N,
      (∫ x in Submission.BoseGases.abox N ℓ,
          (Submission.BoseGases.aP ℓ i Φ x) ^ 2 * f (x i))
        = ((∫ x in Submission.BoseGases.abox N ℓ, (Submission.BoseGases.aP ℓ i Φ x) ^ 2) / ℓ ^ 3)
            * (∫ z in Submission.BoseGases.acube ℓ, f z) := by
    intro i
    refine Work.BoseFixB1B.integral_abox_indep_mul_coord (ℓ := ℓ)
      (g := fun x : Submission.BoseGases.X N => (Submission.BoseGases.aP ℓ i Φ x) ^ 2)
      (h := f) hℓ i ?_ ?_ ?_ hIntf
    · intro x a
      show (Submission.BoseGases.aP ℓ i Φ (Function.update x i a)) ^ 2
          = (Submission.BoseGases.aP ℓ i Φ x) ^ 2
      rw [Submission.BoseGases.aP_const_in_coord hℓ i hΦc x a]
    · exact Submission.BoseGases.integrableOn_slot_fibre hℓ i hfm hfb
        ((Submission.BoseGases.aP_continuous hℓ i hΦc).pow 2)
    · exact Submission.BoseGases.integrableOn_sq_aP hℓ i hΦc
  calc (∑ i : Fin N, ∫ x in Submission.BoseGases.abox N ℓ,
          (Submission.BoseGases.aP ℓ i Φ x) ^ 2 * f (x i))
      = ∑ i : Fin N, (((∫ x in Submission.BoseGases.abox N ℓ,
            (Submission.BoseGases.aP ℓ i Φ x) ^ 2) / ℓ ^ 3)
          * (∫ z in Submission.BoseGases.acube ℓ, f z)) :=
        Finset.sum_congr rfl fun i _ => hslot i
    _ = (∑ i : Fin N, ((∫ x in Submission.BoseGases.abox N ℓ,
            (Submission.BoseGases.aP ℓ i Φ x) ^ 2) / ℓ ^ 3))
          * (∫ z in Submission.BoseGases.acube ℓ, f z) := by
        rw [Finset.sum_mul]
    _ = ((∑ i : Fin N, ∫ x in Submission.BoseGases.abox N ℓ,
            (Submission.BoseGases.aP ℓ i Φ x) ^ 2) / ℓ ^ 3)
          * (∫ z in Submission.BoseGases.acube ℓ, f z) := by
        rw [Finset.sum_div]
    _ = (Submission.BoseGases.cS1 ℓ Φ / ℓ ^ 3)
          * (∫ z in Submission.BoseGases.acube ℓ, f z) := rfl

end Work.BoseFixB1
