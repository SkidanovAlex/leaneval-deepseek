import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Measure.Haar.Unique

namespace Commons.Analysis.Measure

open MeasureTheory MeasureTheory.Measure
open scoped ENNReal

theorem lintegral_lintegral_sub_mul {d : ℕ} (s : Set (EuclideanSpace ℝ (Fin d)))
    (hs : MeasurableSet s) {G H : EuclideanSpace ℝ (Fin d) → ENNReal}
    (hG : AEMeasurable G (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin d))))
    (hH : AEMeasurable H (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin d)))) :
    MeasureTheory.lintegral (MeasureTheory.volume.restrict s)
        (fun η => MeasureTheory.lintegral MeasureTheory.volume (fun ξ => G (ξ - η) * H ξ))
      = MeasureTheory.lintegral MeasureTheory.volume
        (fun ξ => H ξ * MeasureTheory.lintegral (MeasureTheory.volume.restrict s) (fun η => G (ξ - η))) := by
  have hφ : QuasiMeasurePreserving
      (fun p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) => p.2 - p.1)
      (MeasureTheory.volume.prod MeasureTheory.volume) MeasureTheory.volume := by
    have hT : MeasurePreserving
        (fun z : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) => (z.1 - z.2, z.2))
        (MeasureTheory.volume.prod MeasureTheory.volume)
        (MeasureTheory.volume.prod MeasureTheory.volume) :=
      measurePreserving_sub_prod MeasureTheory.volume MeasureTheory.volume
    have hψ : QuasiMeasurePreserving
        (fun z : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) => z.1 - z.2)
        (MeasureTheory.volume.prod MeasureTheory.volume) MeasureTheory.volume :=
      (Measure.quasiMeasurePreserving_fst (μ := MeasureTheory.volume) (ν := MeasureTheory.volume)).comp hT.quasiMeasurePreserving
    have hswap : QuasiMeasurePreserving
        (Prod.swap : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) →
          EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d))
        (MeasureTheory.volume.prod MeasureTheory.volume)
        (MeasureTheory.volume.prod MeasureTheory.volume) :=
      (Measure.measurePreserving_swap (μ := MeasureTheory.volume) (ν := MeasureTheory.volume)).quasiMeasurePreserving
    have h := hψ.comp hswap
    simpa [Function.comp_def] using h
  have hφM : QuasiMeasurePreserving
      (fun p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) => p.2 - p.1)
      ((MeasureTheory.volume.restrict s).prod MeasureTheory.volume) MeasureTheory.volume :=
    hφ.mono_left (Measure.prod_mono Measure.restrict_le_self le_rfl).absolutelyContinuous
  have hK : AEMeasurable
      (Function.uncurry (fun η ξ : EuclideanSpace ℝ (Fin d) => G (ξ - η) * H ξ))
      ((MeasureTheory.volume.restrict s).prod MeasureTheory.volume) := by
    show AEMeasurable
      (fun p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) => G (p.2 - p.1) * H p.2) _
    exact (hG.comp_quasiMeasurePreserving hφM).mul
      (hH.comp_quasiMeasurePreserving (Measure.quasiMeasurePreserving_snd (μ := MeasureTheory.volume.restrict s) (ν := MeasureTheory.volume)))
  rw [lintegral_lintegral_swap hK]
  apply lintegral_congr
  intro ξ
  have hmeas : AEMeasurable (fun η : EuclideanSpace ℝ (Fin d) => G (ξ - η))
      (MeasureTheory.volume.restrict s) := by
    have hmp : MeasurePreserving (fun η : EuclideanSpace ℝ (Fin d) => ξ - η)
        MeasureTheory.volume MeasureTheory.volume := by
      have heq : (fun η : EuclideanSpace ℝ (Fin d) => ξ - η) =
          (fun x => ξ + x) ∘ (fun η => -η) := by
        ext η; simp [sub_eq_add_neg]
      rw [heq]
      exact (measurePreserving_add_left MeasureTheory.volume ξ).comp
        (measurePreserving_neg MeasureTheory.volume)
    exact (hG.comp_quasiMeasurePreserving hmp.quasiMeasurePreserving).mono_measure
      Measure.restrict_le_self
  rw [lintegral_mul_const'' (H ξ) hmeas, mul_comm]

end Commons.Analysis.Measure