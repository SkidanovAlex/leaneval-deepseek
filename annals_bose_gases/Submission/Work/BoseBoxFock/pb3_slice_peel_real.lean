import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.Work.BoseBoxFock.abox_slice_peel
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.pb3_slice_peel_real`

The one-slot slice identity for the box `Λ(ℓ) = boxL ℓ`, in the **real-valued `IntegrableOn`**
form:

    ∫_{x ∈ abox n ℓ} g x
      = ∫_{w ∈ boxL ℓ} ∫_{x' ∈ boxPiSet ({k // k ≠ j}) ℓ} g (insertCoord j w x') .

This is the real counterpart of `Work.BoseBoxFock.abox_slice_peel` (which treats a bounded
measurable *complex*-valued integrand).  Nothing in that proof used the complex structure or
boundedness beyond producing integrability of the integrand with respect to the restricted box
measure, and here that integrability *is* the hypothesis `hg`.  The proof is therefore the same
chain:

* `volume` on `Fin n → E3` is the product measure (`volume_pi`), so restricting to the box turns
  it into `Measure.pi` of the restricted cube measures (`Measure.restrict_pi_pi`) — this is
  `hμn` for the full box and `hν` for the slice;
* the coordinate-insertion map `insertSliceEquiv j : E3 × ({k // k ≠ j} → E3) ≃ᵐ (Fin n → E3)` is
  measure preserving for the appropriate product measures
  (`measurePreserving_insertSliceEquiv`), whence integrability of the composed integrand
  (`MeasurePreserving.integrable_comp`) and the transport of the integral
  (`MeasurePreserving.integral_comp'`);
* `MeasureTheory.integral_prod` is Fubini for the Bochner integral.

`sorry`-free.
-/

noncomputable section

open MeasureTheory

namespace Work.BoseBoxFock

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "Xn" => Work.BoseDict.Xn
local notation "boxL" => Work.BoseK15.corpusBox.boxL

theorem pb3_slice_peel_real {n : ℕ} (j : Fin n) {ℓ : ℝ} (hℓ : 0 < ℓ)
    {g : (Fin n → EuclideanSpace ℝ (Fin 3)) → ℝ}
    (hg : MeasureTheory.IntegrableOn g (Submission.BoseGases.abox n ℓ) MeasureTheory.volume) :
    (∫ x in Submission.BoseGases.abox n ℓ, g x)
      = ∫ w in Work.BoseK15.corpusBox.boxL ℓ,
          ∫ x' in Work.BoseBoxFock.boxPiSet ({k : Fin n // k ≠ j}) ℓ,
            g (Work.BoseBoxFock.insertCoord j w x') := by
  -- the slice measure is the product of the restricted cube measures
  have hν : (volume : Measure ({k : Fin n // k ≠ j} → E3)).restrict
        (boxPiSet ({k : Fin n // k ≠ j}) ℓ)
      = Measure.pi (fun _ : {k : Fin n // k ≠ j} => (volume : Measure E3).restrict (boxL ℓ)) := by
    rw [show (volume : Measure ({k : Fin n // k ≠ j} → E3))
          = Measure.pi (fun _ : {k : Fin n // k ≠ j} => (volume : Measure E3)) from volume_pi]
    show (Measure.pi (fun _ : {k : Fin n // k ≠ j} => (volume : Measure E3))).restrict
        (Set.univ.pi (fun _ : {k : Fin n // k ≠ j} => boxL ℓ)) = _
    rw [Measure.restrict_pi_pi]
  -- the full measure is the product of the restricted cube measures
  have hμn : (volume : Measure (Xn n)).restrict (Submission.BoseGases.abox n ℓ)
      = Measure.pi (fun _ : Fin n => (volume : Measure E3).restrict (boxL ℓ)) := by
    have hbox : Submission.BoseGases.abox n ℓ = Set.univ.pi (fun _ : Fin n => boxL ℓ) := by
      rw [Submission.BoseGases.abox_eq_pi_acube]
      simp only [← corpusBox_boxL_eq_acube hℓ]
    rw [hbox, show (volume : Measure (Xn n))
          = Measure.pi (fun _ : Fin n => (volume : Measure E3)) from volume_pi]
    rw [Measure.restrict_pi_pi]
  -- integrability against the product of restricted cube measures is the hypothesis
  have hFb : Integrable g
      (Measure.pi (fun _ : Fin n => (volume : Measure E3).restrict (boxL ℓ))) := by
    rw [← hμn]
    exact hg
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
