import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseKinLoc.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

set_option linter.unusedVariables false

namespace Work.BoseKinLoc.Gap

/-- Translation change of variables for set integrals on `ℝ³`: the integral of `G`
over the translate `v + s` of a set is the integral of `z ↦ G (z + v)` over `s`.

This is `MeasureTheory.MeasurePreserving.setIntegral_image_emb` for the measure
preserving embedding `z ↦ z + v` of Lebesgue measure. -/
lemma setIntegral_image_add_right (s : Set (EuclideanSpace ℝ (Fin 3)))
    (v : EuclideanSpace ℝ (Fin 3)) (G : EuclideanSpace ℝ (Fin 3) → ℝ) :
    (∫ z in (fun y => y + v) '' s, G z) = ∫ z in s, G (z + v) :=
  MeasureTheory.MeasurePreserving.setIntegral_image_emb
    (MeasureTheory.measurePreserving_add_right MeasureTheory.volume v)
    (Homeomorph.addRight v).measurableEmbedding G s

/-- The moving box `Λ(u) = ℓu + [−ℓ/2,ℓ/2]³` is the translate by `ℓu` of the
centred cube `acube ℓ`. -/
lemma lamBox_eq_image_acube (ℓ : ℝ) (u : EuclideanSpace ℝ (Fin 3)) :
    Work.BoseKinLoc.lamBox ℓ u
      = (fun y : EuclideanSpace ℝ (Fin 3) => y + ℓ • u) '' Submission.BoseGases.acube ℓ := by
  ext x
  constructor
  · intro hx
    exact ⟨x - ℓ • u, hx, sub_add_cancel x (ℓ • u)⟩
  · rintro ⟨y, hy, rfl⟩
    show (y + ℓ • u) - ℓ • u ∈ Submission.BoseGases.acube ℓ
    rwa [add_sub_cancel_right]

/-- **Change of variables for the moving box.** Since `Λ(u) = ℓu + acube ℓ`, the
Lebesgue integral of `G` over the box `Λ(u)` equals the integral over the centred
cube `acube ℓ` of the translate `z ↦ G (ℓu + z)`. -/
theorem integral_lamBox_eq_acube (ℓ : ℝ) (hℓ : 0 < ℓ)
    (G : EuclideanSpace ℝ (Fin 3) → ℝ) (u : EuclideanSpace ℝ (Fin 3)) :
    (∫ z in Work.BoseKinLoc.lamBox ℓ u, G z)
      = ∫ z in Submission.BoseGases.acube ℓ, G (ℓ • u + z) := by
  rw [lamBox_eq_image_acube ℓ u]
  rw [setIntegral_image_add_right (Submission.BoseGases.acube ℓ) (ℓ • u) G]
  exact MeasureTheory.setIntegral_congr_fun (Submission.BoseGases.acube_measurable ℓ)
    fun z _ => by rw [add_comm]

end Work.BoseKinLoc.Gap
