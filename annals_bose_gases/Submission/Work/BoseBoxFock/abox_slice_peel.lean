import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.Work.BoseBoxFock.PB3Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.abox_slice_peel`

The one-slot slice identity for the box `Λ(ℓ) = boxL ℓ` (the centred cube of side `ℓ`), in the
**measurable-bounded** form needed by the corpus:

    ∫_{x ∈ Λ(ℓ)^n} g x
      = ∫_{w ∈ Λ(ℓ)} ∫_{x' ∈ Λ(ℓ)^{{k // k ≠ j}}} g (insertCoord j w x') .

This is the sibling `Work.BoseBoxFock.setIntegral_insertCoord_slice`, which states the same
identity (with the two sides interchanged) for a **continuous real-valued** integrand, upgraded to
a complex-valued integrand that is only assumed measurable and bounded.  The upgrade is exactly the
integrability bookkeeping:

* the whole proof of the slice identity runs through the measure-preserving equivalence
  `insertSliceEquiv j : E3 × ({k // k ≠ j} → E3) ≃ᵐ (Fin n → E3)`, Fubini, and
  `MeasurePreserving.integral_comp'` — none of which uses continuity, only integrability;
* for a continuous `f` on the compact box integrability came from
  `ContinuousOn.integrableOn_compact`; for a bounded measurable `g` on the box (a *finite* measure
  space, `volume (boxL ℓ) = ℓ³ < ∞`) it comes from `IntegrableOn.of_bound` against the compact box
  `abox n ℓ`.

`sorry`-free.
-/

noncomputable section

open MeasureTheory

namespace Work.BoseBoxFock

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "Xn" => Work.BoseDict.Xn
local notation "boxL" => Work.BoseK15.corpusBox.boxL

theorem abox_slice_peel {n : ℕ} (j : Fin n) {ℓ : ℝ} (hℓ : 0 < ℓ)
    {g : (Fin n → EuclideanSpace ℝ (Fin 3)) → ℂ}
    (gm : Measurable g) (gb : ∃ C : ℝ, ∀ x, ‖g x‖ ≤ C) :
    (∫ x in Submission.BoseGases.abox n ℓ, g x)
      = ∫ w in Work.BoseK15.corpusBox.boxL ℓ,
          ∫ x' in Work.BoseBoxFock.boxPiSet ({k : Fin n // k ≠ j}) ℓ,
            g (Work.BoseBoxFock.insertCoord j w x') := by
  obtain ⟨C, hC⟩ := gb
  -- the slice measure is the product of the restricted cube measures
  have hν : (volume : Measure ({k : Fin n // k ≠ j} → E3)).restrict
        (boxPiSet ({k : Fin n // k ≠ j}) ℓ)
      = Measure.pi (fun _ : {k : Fin n // k ≠ j} => (volume : Measure E3).restrict (boxL ℓ)) := by
    rw [show (volume : Measure ({k : Fin n // k ≠ j} → E3))
          = Measure.pi (fun _ : {k : Fin n // k ≠ j} => (volume : Measure E3)) from volume_pi]
    show (Measure.pi (fun _ : {k : Fin n // k ≠ j} => (volume : Measure E3))).restrict
        (Set.univ.pi (fun _ : {k : Fin n // k ≠ j} => boxL ℓ)) = _
    rw [Measure.restrict_pi_pi]
  have hbox : Submission.BoseGases.abox n ℓ = Set.univ.pi (fun _ : Fin n => boxL ℓ) := by
    rw [Submission.BoseGases.abox_eq_pi_acube]
    simp only [← corpusBox_boxL_eq_acube hℓ]
  -- the full measure is the product of the restricted cube measures
  have hμn : (volume : Measure (Xn n)).restrict (Submission.BoseGases.abox n ℓ)
      = Measure.pi (fun _ : Fin n => (volume : Measure E3).restrict (boxL ℓ)) := by
    rw [hbox, show (volume : Measure (Xn n))
          = Measure.pi (fun _ : Fin n => (volume : Measure E3)) from volume_pi]
    rw [Measure.restrict_pi_pi]
  -- integrability of the bounded measurable integrand against the finite box measure
  have hK : IsCompact (Submission.BoseGases.abox n ℓ) := by
    rw [Submission.BoseGases.abox_eq_pi_acube]
    exact isCompact_univ_pi (fun _ => Submission.BoseGases.acube_compact hℓ)
  have hFb : Integrable g
      (Measure.pi (fun _ : Fin n => (volume : Measure E3).restrict (boxL ℓ))) := by
    rw [← hμn]
    exact IntegrableOn.of_bound hK.measure_lt_top gm.aestronglyMeasurable C
      (Filter.Eventually.of_forall hC)
  have hmp := measurePreserving_insertSliceEquiv (n := n) j ℓ
  have hInt : Integrable (fun z : E3 × ({k : Fin n // k ≠ j} → E3) =>
      g (insertCoord j z.1 z.2))
      (((volume : Measure E3).restrict (boxL ℓ)).prod
        (Measure.pi (fun _ : {k : Fin n // k ≠ j} => (volume : Measure E3).restrict (boxL ℓ)))) :=
    (hmp.integrable_comp hFb.aestronglyMeasurable).mpr hFb
  calc
    (∫ x in Submission.BoseGases.abox n ℓ, g x)
        = ∫ x : Xn n, g x
            ∂(Measure.pi (fun _ : Fin n => (volume : Measure E3).restrict (boxL ℓ))) := by
          rw [← hμn]
    _ = ∫ z : E3 × ({k : Fin n // k ≠ j} → E3), g (insertCoord j z.1 z.2)
            ∂(((volume : Measure E3).restrict (boxL ℓ)).prod
              (Measure.pi (fun _ : {k : Fin n // k ≠ j} =>
                (volume : Measure E3).restrict (boxL ℓ)))) :=
          (MeasureTheory.MeasurePreserving.integral_comp' (f := insertSliceEquiv j) hmp
            (fun x : Xn n => g x)).symm
    _ = ∫ w : E3, (∫ x' : ({k : Fin n // k ≠ j} → E3), g (insertCoord j w x')
            ∂(Measure.pi (fun _ : {k : Fin n // k ≠ j} =>
              (volume : Measure E3).restrict (boxL ℓ))))
            ∂((volume : Measure E3).restrict (boxL ℓ)) :=
          MeasureTheory.integral_prod _ hInt
    _ = ∫ w in boxL ℓ, ∫ x' in boxPiSet ({k : Fin n // k ≠ j}) ℓ,
            g (insertCoord j w x') := by
          rw [← hν]

end Work.BoseBoxFock
