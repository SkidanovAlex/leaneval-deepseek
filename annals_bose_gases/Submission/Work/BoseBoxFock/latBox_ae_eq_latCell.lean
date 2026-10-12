import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Submission.Work.BoseBoxFock.LatFourierDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.latBox_ae_eq_latCell`

The closed cube `latBox ℓ = [0,ℓ]³` and the half-open cube `latCell ℓ = [0,ℓ)³` differ only on the
union of the three faces `{x | x i = ℓ}`, which is Lebesgue-null; hence the two sets are equal
almost everywhere with respect to `volume` on `ℝ³`.

The proof reduces to the equality of the two volumes: `latCell ℓ ⊆ latBox ℓ`, and both have volume
`ℓ³` (the closed-cube version is the auxiliary `volume_latBox`, proved exactly as the corpus's
`volume_latCell` via the measure-preserving `WithLp.toLp 2` and `Real.volume_Icc_pi`), so the
difference `latBox ℓ \ latCell ℓ` has measure zero (`MeasureTheory.measure_sdiff`), while the
reverse difference is empty.
-/

open MeasureTheory

namespace Work.BoseBoxFock

namespace LatFourier

/-- The volume of the **closed** cube `latBox ℓ = [0,ℓ]³`, the twin of `volume_latCell`. -/
lemma volume_latBox {ℓ : ℝ} (hℓ : 0 ≤ ℓ) :
    volume (latBox ℓ) = ENNReal.ofReal (ℓ ^ 3) := by
  have hpre : (WithLp.toLp 2 : (Fin 3 → ℝ) → EuclideanSpace ℝ (Fin 3)) ⁻¹' (latBox ℓ)
      = Set.Icc (fun _ : Fin 3 => (0 : ℝ)) (fun _ : Fin 3 => ℓ) := by
    ext x
    simp only [Set.mem_preimage, latBox, Set.mem_ofPred_eq, Set.mem_Icc, Pi.le_def]
    exact forall_and
  have hmp := PiLp.volume_preserving_toLp (Fin 3)
  rw [← MeasureTheory.MeasurePreserving.measure_preimage hmp
      (measurableSet_latBox ℓ).nullMeasurableSet, hpre, Real.volume_Icc_pi]
  simp [Finset.prod_const, ENNReal.ofReal_pow hℓ]

end LatFourier

theorem latBox_ae_eq_latCell {ℓ : ℝ} (hℓ : 0 ≤ ℓ) :
    Work.BoseBoxFock.LatFourier.latBox ℓ =ᵐ[MeasureTheory.volume]
      Work.BoseBoxFock.LatFourier.latCell ℓ := by
  rw [MeasureTheory.ae_eq_set]
  refine ⟨?_, ?_⟩
  · -- the only difference is the union of the three faces `{x | x i = ℓ}`, which is null
    rw [MeasureTheory.measure_sdiff LatFourier.latCell_subset_latBox
        (LatFourier.measurableSet_latCell ℓ).nullMeasurableSet
        (by rw [LatFourier.volume_latCell hℓ]; exact ENNReal.ofReal_ne_top),
      LatFourier.volume_latBox hℓ, LatFourier.volume_latCell hℓ, tsub_self]
  · rw [Set.sdiff_eq_empty.mpr LatFourier.latCell_subset_latBox, measure_empty]

end Work.BoseBoxFock
