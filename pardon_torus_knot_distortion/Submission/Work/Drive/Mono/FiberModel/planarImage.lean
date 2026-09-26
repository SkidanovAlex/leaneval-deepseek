import Mathlib
import Submission.Work.Drive.Mono.FiberModel.planar_basic

/-!
# The planar image of the removed level is the shadow chamber

The removal condition of `tiltedLevelRemoved` depends on `π y = (⟪v,y⟫, ℓ y)` alone, so the planar
image of the removed set is `π '' PBox ∩ chamber = interior W ∩ chamber`.
-/

open LeanEval.KnotTheory.PardonDistortion Set

namespace Work.Drive.Mono.FiberModel

noncomputable section

/-- **The removed set is the box cut by the `π`-saturated chamber condition.** -/
theorem tiltedLevelRemoved_eq (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ) (v : R3)
    (h lam : ℝ) (ℓ : R3 →L[ℝ] ℝ) :
    Work.Drive.Mono.tiltedLevelRemoved s c σ u v h ℓ lam
      = Submission.PBox s c σ ∩ (levPair v ℓ) ⁻¹' chamber (slabA u c v) h lam := by
  ext y
  simp only [Work.Drive.Mono.tiltedLevelRemoved, slabA, chamber, levPair,
    Work.Drive.EpsForm.tiltedSlabClosed, Set.mem_sdiff, Set.mem_inter_iff,
    Set.mem_ofPred_eq, Set.mem_preimage]
  constructor
  · rintro ⟨hyB, hyc⟩
    refine ⟨hyB, ?_⟩
    by_cases h1 : h < |inner ℝ v y - (inner ℝ v c + u)|
    · exact Or.inl h1
    · exact Or.inr (le_of_not_gt fun h2 => hyc ⟨le_of_not_gt h1, h2⟩)
  · rintro ⟨hyB, h1 | h1⟩
    · exact ⟨hyB, fun hc => absurd hc.1 (not_le.mpr h1)⟩
    · exact ⟨hyB, fun hc => absurd hc.2 (not_lt.mpr h1)⟩

/-- **The planar image of the removed level is the shadow chamber inside the shadow.** -/
theorem planarImage_eq (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ) (v : R3) (h lam : ℝ)
    (ℓ : R3 →L[ℝ] ℝ) (hv : v ≠ 0) (hℓv : ℓ v = 0) (hℓne : ℓ ≠ 0) :
    planarImage s c σ u v h ℓ lam
      = interior (boxShadow s c σ v ℓ) ∩ chamber (slabA u c v) h lam := by
  rw [planarImage, shadow, tiltedLevelRemoved_eq s c σ u v h lam ℓ,
    Set.image_inter_preimage, image_PBox_eq_interior_boxShadow (s := s) c σ hv hℓv hℓne]

end

end Work.Drive.Mono.FiberModel
