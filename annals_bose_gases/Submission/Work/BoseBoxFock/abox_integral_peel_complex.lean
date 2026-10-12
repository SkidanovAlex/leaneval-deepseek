import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.Q0Sector
import Submission.Work.BoseDict.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.abox_integral_peel_complex`

The complex-valued version of the measure-preserving peel of the centred box
`abox (n+1) ℓ` isolating the particle `i : Fin (n+1)`:

  `∫_{abox (n+1) ℓ} F = ∫_{r ∈ abox n ℓ} (∫_{y ∈ acube ℓ} F (kcInsN n i (y, r)))`.

The proof is the verbatim complex transcription of `Submission.BoseGases.abox_integral_peel`
(`Submission/Q0Sector.lean`), which is the `ℝ`-valued case: the measure-preserving
identification `Submission.BoseGases.abox_peel_mp` transports the box measure to the product of
the `i`-th slot measure `volume.restrict (acube ℓ)` and the remaining-coordinates measure
`volume.restrict (abox n ℓ)`, and Fubini (`MeasureTheory.integral_prod_symm`) finishes.
Nothing in the argument uses the codomain, so the same proof runs for `ℂ`.
-/

namespace Work.BoseBoxFock

open MeasureTheory

theorem abox_integral_peel_complex {n : ℕ} {ℓ : ℝ} (i : Fin (n + 1))
    (F : Submission.BoseGases.X (n + 1) → ℂ)
    (hF : MeasureTheory.IntegrableOn F (Submission.BoseGases.abox (n + 1) ℓ) MeasureTheory.volume) :
    (∫ x in Submission.BoseGases.abox (n + 1) ℓ, F x)
      = ∫ r : Submission.BoseGases.X n,
          (∫ y : EuclideanSpace ℝ (Fin 3) in Submission.BoseGases.acube ℓ,
            F (Submission.BoseGases.kcInsN n i (y, r)))
          ∂(MeasureTheory.volume.restrict (Submission.BoseGases.abox n ℓ)) := by
  let μ' : Measure (EuclideanSpace ℝ (Fin 3)) := volume.restrict (Submission.BoseGases.acube ℓ)
  let ν : Measure (Submission.BoseGases.X n) := volume.restrict (Submission.BoseGases.abox n ℓ)
  have hmp2 : MeasurePreserving (⇑(Submission.BoseGases.kcInsN n i)) (μ'.prod ν)
      (volume.restrict (Submission.BoseGases.abox (n + 1) ℓ)) := by
    have h := MeasurePreserving.symm
      (e := (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => EuclideanSpace ℝ (Fin 3)) i))
      (Submission.BoseGases.abox_peel_mp (n := n) ℓ i)
    simpa [Submission.BoseGases.kcInsN, μ', ν] using h
  have hpeel : Integrable
      (fun p : EuclideanSpace ℝ (Fin 3) × Submission.BoseGases.X n =>
        F (Submission.BoseGases.kcInsN n i p)) (μ'.prod ν) := by
    exact (hmp2.integrable_comp (hg := hF.aestronglyMeasurable)).mpr hF
  calc
    (∫ x in Submission.BoseGases.abox (n + 1) ℓ, F x)
        = ∫ x : Submission.BoseGases.X (n + 1), F x
            ∂(volume.restrict (Submission.BoseGases.abox (n + 1) ℓ)) := rfl
    _ = ∫ p : EuclideanSpace ℝ (Fin 3) × Submission.BoseGases.X n,
          F (Submission.BoseGases.kcInsN n i p) ∂(μ'.prod ν) := by
      simpa [μ', ν] using (hmp2.integral_comp' F).symm
    _ = ∫ r : Submission.BoseGases.X n,
          (∫ y : EuclideanSpace ℝ (Fin 3),
            F (Submission.BoseGases.kcInsN n i (y, r)) ∂μ') ∂ν := by
      exact MeasureTheory.integral_prod_symm
        (f := fun p : EuclideanSpace ℝ (Fin 3) × Submission.BoseGases.X n =>
          F (Submission.BoseGases.kcInsN n i p)) hpeel
    _ = ∫ r : Submission.BoseGases.X n,
          (∫ y : EuclideanSpace ℝ (Fin 3) in Submission.BoseGases.acube ℓ,
            F (Submission.BoseGases.kcInsN n i (y, r)))
          ∂(volume.restrict (Submission.BoseGases.abox n ℓ)) := rfl

end Work.BoseBoxFock
