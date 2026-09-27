import Mathlib
import Submission.Work.EKLC6Core.growth_le_HcondSig
import Submission.Work.EKLC6Core.aemeasurable_atomInfo
import Submission.Work.EKLContract.All

/-!
# `EKLC6Core.atomInfo_aemeasurable`

The general (non-ergodic, arbitrary-horospherical-subgroup) form of the measurability of the atom
information

`atomInfo A U ν t x = - log ( (ν x (shape A U x)).toReal / (ν x (shape (comap (aDiag t ·) A) U x)).toReal )`.

The `U = Uminus t` version with an ergodicity hypothesis is `aemeasurable_atomInfo`; here we run the
same argument with an arbitrary `IsHoro U` (all that is used of it is that `U` is closed, so that
the graph of the shape map is Borel).  The two ingredients are recalled in `aemeasurable_atomInfo`:
`aemeasurable_shape_mass_of_seq` (mass of the shape, via the Borel shape graph and the section
evaluation of a weakly measurable family finite on compacta) and the σ-algebra bookkeeping
`exists_generating_sequence`, `comap_le_borel_of_le`.
-/

open MeasureTheory Filter Topology
open scoped ENNReal

noncomputable section

namespace Work.EKLC6Core

open Work.EKLContract

theorem atomInfo_aemeasurable {μ : MeasureTheory.Measure Work.EKLContract.X3}
    [MeasureTheory.IsProbabilityMeasure μ] {U : Subgroup Work.EKLContract.SL3}
    {ν : Work.EKLContract.X3 → MeasureTheory.Measure Work.EKLContract.SL3}
    {X' : Set Work.EKLContract.X3} (t : Fin 3 → ℝ)
    (hL : Work.EKLContract.IsLeafwise μ U ν X') (hU : Work.EKLContract.IsHoro U)
    {A : MeasurableSpace Work.EKLContract.X3} {Z : Set Work.EKLContract.X3}
    (hplaq : Work.EKLContract.IsPlaqueAlgebra U Z A) :
    AEMeasurable (Work.EKLC6Core.atomInfo A U ν t) μ := by
  classical
  have hUclosed : IsClosed ((U : Subgroup SL3) : Set SL3) := hU.1
  -- a Borel generating sequence for `A`
  obtain ⟨E, hEmeas, hAgen⟩ := exists_generating_sequence hplaq.1 hplaq.2.1
  have hV : @AEMeasurable X3 ℝ≥0∞ _ (borel X3)
      (fun x => ν x (shape A U x)) μ := by
    have h := aemeasurable_shape_mass_of_seq (μ := μ) (U := U) hUclosed hL hEmeas
    rw [← hAgen] at h
    exact h
  -- the pull-back σ-algebra is again countably generated over a Borel sub-σ-algebra
  have hA' : MeasurableSpace.comap (fun y : X3 => aDiag t • y) A ≤ borel X3 :=
    comap_le_borel_of_le hplaq.1 t
  have hcount' : ∃ b' : Set (Set X3), b'.Countable ∧
      MeasurableSpace.comap (fun y : X3 => aDiag t • y) A = MeasurableSpace.generateFrom b' := by
    obtain ⟨b, hbc, hbA⟩ := hplaq.2.1
    exact ⟨Set.preimage (fun y : X3 => aDiag t • y) '' b, hbc.image _, by
      rw [hbA, MeasurableSpace.comap_generateFrom]⟩
  obtain ⟨E', hE'meas, hA'gen⟩ := exists_generating_sequence hA' hcount'
  have hW : @AEMeasurable X3 ℝ≥0∞ _ (borel X3)
      (fun x => ν x (shape (MeasurableSpace.comap (fun y : X3 => aDiag t • y) A) U x)) μ := by
    have h := aemeasurable_shape_mass_of_seq (μ := μ) (U := U) hUclosed hL hE'meas
    rw [← hA'gen] at h
    exact h
  -- combine: real-valued masses, quotient, logarithm, negation
  have hVr : @AEMeasurable X3 ℝ _ (borel X3)
      (fun x => (ν x (shape A U x)).toReal) μ := hV.ennreal_toReal
  have hWr : @AEMeasurable X3 ℝ _ (borel X3)
      (fun x => (ν x (shape (MeasurableSpace.comap (fun y : X3 => aDiag t • y) A) U x)).toReal) μ :=
    hW.ennreal_toReal
  have hratio := hVr.div hWr
  have hlog := Real.measurable_log.comp_aemeasurable hratio
  exact hlog.neg

end Work.EKLC6Core
