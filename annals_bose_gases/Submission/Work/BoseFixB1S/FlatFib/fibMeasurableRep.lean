import ChallengeDeps
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Submission.Work.BoseFixR.w1FibreSlotIntegrableOfSupport
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Global measurability of the localised one-body fibre `wSmall1Pair`

The fibre of the localised kernel `w_{1,B} = wSmallPair M ℓ d u (g₀ v h)` is the function

    z ↦ ∫ y in acube ℓ, wSmall1Pair h M ℓ d u z y.

`g₀ v h = v(1−w₀)` is only *a.e.* strongly measurable (`IsScatteringSolution.rhs_integrable`
gives `LocallyIntegrable (v * (1 - w₀))`), so we replace it by its measurable representative
`f' = AEMeasurable.mk (g₀ v h) ·`.  The two fibres with numerators `g₀` and `f'` agree
*everywhere* (for fixed `z`, the null set where the numerators differ is pulled back to a null
set under the measure-preserving reflection `y ↦ z − y`), so the fibre of the measurable
numerator is a globally measurable representative of the requested fibre.
-/

namespace Work.BoseFixB1S.FlatFib

open MeasureTheory
open scoped MeasureTheory ENNReal

/-- A globally measurable representative of the localised one-body fibre
`z ↦ ∫_{acube ℓ} wSmall1Pair h M ℓ d u z y`. -/
theorem fibMeasurableRep {v : EuclideanSpace ℝ (Fin 3) → ℝ} (h : Work.UBB.ScatSol v)
    {M : ℕ} (hM : 1 ≤ M) {ℓ d : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d)
    (u : EuclideanSpace ℝ (Fin 3)) :
    ∃ fib' : EuclideanSpace ℝ (Fin 3) → ℝ, Measurable fib' ∧
      ∀ z : EuclideanSpace ℝ (Fin 3), fib' z
        = ∫ y in Submission.BoseGases.acube ℓ,
            Submission.BoseGases.wSmall1Pair h M ℓ d u z y := by
  have hw0 : BoseGases.IsScatteringSolution (Classical.choose h) v := (Classical.choose_spec h).2
  -- `g₀ v h = v * (1 − w₀)` is locally integrable, hence a.e. strongly measurable
  have hg0ae : AEMeasurable (Submission.BoseGases.g0 v h) (MeasureTheory.volume) :=
    hw0.rhs_integrable.aestronglyMeasurable.aemeasurable
  set f' : EuclideanSpace ℝ (Fin 3) → ℝ :=
    AEMeasurable.mk (Submission.BoseGases.g0 v h) hg0ae with hf'def
  have hf'meas : Measurable f' := AEMeasurable.measurable_mk hg0ae
  have hf'eq : Submission.BoseGases.g0 v h =ᵐ[MeasureTheory.volume] f' :=
    AEMeasurable.ae_eq_mk hg0ae
  refine ⟨fun z => ∫ y in Submission.BoseGases.acube ℓ,
      Submission.BoseGases.wSmallPair M ℓ d u f' z y, ?_, ?_⟩
  · exact Work.BoseFixR.measurable_fibre_wSmallPair hM hℓ hd u hf'meas
  · intro z
    -- the two fibres (numerators `f'` and `g₀`) agree everywhere
    have hFibEq : (∫ y in Submission.BoseGases.acube ℓ,
          Submission.BoseGases.wSmallPair M ℓ d u f' z y)
        = (∫ y in Submission.BoseGases.acube ℓ,
            Submission.BoseGases.wSmallPair M ℓ d u (Submission.BoseGases.g0 v h) z y) := by
      refine MeasureTheory.integral_congr_ae ?_
      have hmp : MeasureTheory.MeasurePreserving (fun t : EuclideanSpace ℝ (Fin 3) => z - t)
          (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3)))
          (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))) :=
        MeasureTheory.Measure.measurePreserving_sub_left MeasureTheory.volume z
      have hae : ∀ᵐ y ∂(MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))),
          Submission.BoseGases.g0 v h (z - y) = f' (z - y) :=
        hmp.quasiMeasurePreserving.tendsto_ae.eventually hf'eq
      filter_upwards [MeasureTheory.ae_restrict_of_ae hae] with y hy
      simp only [Submission.BoseGases.wSmallPair, Submission.BoseGases.wSmallScaled]
      rw [hy]
    show (∫ y in Submission.BoseGases.acube ℓ,
        Submission.BoseGases.wSmallPair M ℓ d u f' z y) = _
    rw [hFibEq]
    rfl

end Work.BoseFixB1S.FlatFib
