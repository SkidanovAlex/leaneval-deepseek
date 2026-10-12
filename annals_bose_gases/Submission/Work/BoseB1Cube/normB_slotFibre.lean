import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB1B.slotMassFibre
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseB1Cube

open MeasureTheory

theorem normB_slotFibre {N : ℕ} {L d : ℝ} (hL : 0 < L) (hd : 0 < d)
    (u : EuclideanSpace ℝ (Fin 3))
    {Φ : Submission.BoseGases.X N → ℝ} (hΦ : Measurable Φ)
    (hfin : (∫⁻ x in Submission.BoseGases.abox N L, ENNReal.ofReal ((Φ x) ^ 2)) ≠ ⊤)
    (S : Finset (Fin N)) (e : Work.PerSector.SlotIn N S ≃ Fin S.card) :
    MeasureTheory.Integrable
        (fun y : Work.PerSector.SlotOut N S → EuclideanSpace ℝ (Fin 3) =>
          ∫ x in Submission.BoseGases.abox S.card L,
            (Work.BoseFixB1B.sharpBoxState (Submission.BoseGases.dlBox L d u)
              (Work.PerSector.slotFibreState S e Φ y) x) ^ 2)
        ((MeasureTheory.volume : MeasureTheory.Measure
          (Work.PerSector.SlotOut N S → EuclideanSpace ℝ (Fin 3))).restrict
          (Work.PerSector.slotOutside L (Submission.BoseGases.dlBox L d u) S))
      ∧ (∫ x in Submission.BoseGases.abox N L,
            (Work.PerSector.slotPiece (Submission.BoseGases.dlBox L d u) S Φ x) ^ 2)
        = ∫ y in Work.PerSector.slotOutside L (Submission.BoseGases.dlBox L d u) S,
            ∫ x in Submission.BoseGases.abox S.card L,
              (Work.BoseFixB1B.sharpBoxState (Submission.BoseGases.dlBox L d u)
                (Work.PerSector.slotFibreState S e Φ y) x) ^ 2 := by
  classical
  set B : Set (EuclideanSpace ℝ (Fin 3)) := Submission.BoseGases.dlBox L d u with hBdef
  have hBmeas : MeasurableSet B := by
    rw [hBdef]
    exact Work.SmallBoxSliding.measurableSet_dlBox L d u
  have hBL : B ⊆ Submission.BoseGases.acube L := by
    rw [hBdef]
    exact Work.SmallBoxSliding.dlBox_subset_acube L d u
  -- the a.e. identification of the target fibre integrand with the fibre mass of the slot piece
  have hae := Work.BoseFixB1B.ae_slotFibreMassReal_slotPiece_eq_sharp (N := N) L (B := B)
    hBL hBmeas (S := S) (Φ := Φ) hΦ e
  -- the real box mass of the slot piece is its slot mass
  have hpiece : (∫ x in Submission.BoseGases.abox N L,
        (Work.PerSector.slotPiece B S Φ x) ^ 2) = Work.PerSector.slotMass L B S Φ := by
    rw [Work.PerSector.slotMass,
      ← Work.SlotWord.lintegral_slotPiece_sq_eq_slotMassENN L B S Φ]
    exact MeasureTheory.integral_eq_lintegral_of_nonneg_ae
      (Filter.Eventually.of_forall (fun x => sq_nonneg _))
      ((Work.PerSector.slotPiece_measurable B hBmeas S hΦ).pow_const 2).aestronglyMeasurable
  -- the fibre side, by the mass identity of the slot piece times `a.e.`-congruence
  have hRHS : (∫ y in Work.PerSector.slotOutside L B S,
        ∫ x in Submission.BoseGases.abox S.card L,
          (Work.BoseFixB1B.sharpBoxState B (Work.PerSector.slotFibreState S e Φ y) x) ^ 2)
      = Work.PerSector.slotMass L B S Φ := by
    rw [← Work.SlotWord.integral_slotFibreMassReal_piece_eq_slotMass (N := N) L (B := B) S
      hBL hBmeas hΦ hfin]
    exact MeasureTheory.integral_congr_ae (hae.mono (fun y hy => hy.symm))
  refine ⟨?_, ?_⟩
  · exact (Work.SlotWord.integrable_slotFibreMassReal_piece (N := N) L (B := B) S hBL hBmeas
      hΦ hfin).congr hae
  · rw [hpiece, hRHS]

end Work.BoseB1Cube
