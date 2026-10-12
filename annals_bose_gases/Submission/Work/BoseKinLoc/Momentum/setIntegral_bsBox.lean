import Mathlib.MeasureTheory.Group.Integral
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseKinLoc.Momentum.momDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseKinLoc.Momentum.setIntegral_bsBox` — translation of the sliding box integral

The sliding (moving) box of FS's localisation is `Λ(u) = ℓu + acube ℓ`, i.e.
`Work.BSKinetic.bsBox ℓ u = {x | x − ℓ•u ∈ acube ℓ}` (definitionally
`Work.UBBInputs9.bigBox ℓ u`).  Lebesgue measure on `ℝ³` is translation invariant, so an integral
over the moving box is the integral over the *centred* cube `acube ℓ` of the translated integrand:

    `∫_{Λ(u)} g = ∫_{acube ℓ} g (ℓ•u + ·)`.

This is the complex-valued form used when the integrand is a Fourier amplitude (`kinFT` of a box
state); the real-valued instance for `ℝ`-valued integrands is
`Work.BSKinetic.setIntegral_bigBox_eq_translate` / `setIntegral_bigBox_eq_add`.
-/

namespace Work.BoseKinLoc.Momentum

open MeasureTheory

theorem setIntegral_bsBox (ℓ : ℝ) (u : EuclideanSpace ℝ (Fin 3)) (g : EuclideanSpace ℝ (Fin 3) → ℂ) : (∫ x in Work.BSKinetic.bsBox ℓ u, g x) = ∫ z in Submission.BoseGases.acube ℓ, g (ℓ • u + z) := by
  classical
  -- the moving box is the translate by `ℓ • u` of the centred cube, hence measurable
  have hmeasB : MeasurableSet (Work.BSKinetic.bsBox ℓ u) := by
    have h : Work.BSKinetic.bsBox ℓ u
        = (fun x : EuclideanSpace ℝ (Fin 3) => x - ℓ • u) ⁻¹'
            Submission.BoseGases.acube ℓ := rfl
    rw [h]
    exact (Submission.BoseGases.acube_measurable ℓ).preimage (by fun_prop)
  -- replace both set integrals by integrals of indicators
  rw [← integral_indicator hmeasB,
      ← integral_indicator (Submission.BoseGases.acube_measurable ℓ)]
  -- translate the argument of the indicator of the moving box by `ℓ • u`
  rw [← integral_add_left_eq_self
        ((Work.BSKinetic.bsBox ℓ u).indicator g) (ℓ • u)]
  apply integral_congr_ae
  filter_upwards with z
  rw [Set.indicator_apply, Set.indicator_apply]
  by_cases hz : z ∈ Submission.BoseGases.acube ℓ
  · have hz' : ℓ • u + z ∈ Work.BSKinetic.bsBox ℓ u := by
      show ℓ • u + z - ℓ • u ∈ Submission.BoseGases.acube ℓ
      rwa [add_sub_cancel_left]
    rw [if_pos hz', if_pos hz]
  · have hz' : ℓ • u + z ∉ Work.BSKinetic.bsBox ℓ u := by
      show ¬ (ℓ • u + z - ℓ • u ∈ Submission.BoseGases.acube ℓ)
      rwa [add_sub_cancel_left]
    rw [if_neg hz', if_neg hz]

end Work.BoseKinLoc.Momentum
