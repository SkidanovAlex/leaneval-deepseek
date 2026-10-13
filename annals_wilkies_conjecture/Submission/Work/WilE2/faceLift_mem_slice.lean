import Mathlib
import Submission.Work.WilE2.FaceDefs

namespace Work.WilE2

open WilkiesDesign.E

/-- The lifted point of a slice point lies in the cube at its `j`-th coordinate. -/
theorem faceLift_mem_cube {n : ℕ} (j : Fin (n+1)) {σ : ℝ} (hσ : |σ| ≤ 1)
    {y : Fin n → ℝ} (hy : y ∈ cubeC n) : faceLift j σ y ∈ cubeC (n+1) := by
  intro i
  by_cases hi : i = j
  · subst hi
    rw [faceLift_apply_same]
    exact hσ
  · rw [faceLift_apply_of_ne j σ y hi]
    exact hy _

/-- The lifted point of a slice point satisfies all the original equations. -/
theorem faceLift_mem_Zset {n r : ℕ} (c : EAChain (n+1) r) (j : Fin (n+1)) (σ : ℝ)
    (g : Finset (EAPoly (n+1) r)) {y : Fin n → ℝ}
    (hy : y ∈ Zset (chainFace c j σ) (g.image (faceSub j σ))) :
    faceLift j σ y ∈ Zset c g := by
  intro f hf
  have hmem : faceSub j σ f ∈ g.image (faceSub j σ) :=
    Finset.mem_image.mpr ⟨f, hf, rfl⟩
  have h := hy _ hmem
  rw [faceSub_eval] at h
  exact h

theorem faceLift_mem_slice {n r : ℕ} (c : WilkiesDesign.E.EAChain (n+1) r) (j : Fin (n+1)) (σ : ℝ)
    (hσ : |σ| ≤ 1) (g : Finset (WilkiesDesign.E.EAPoly (n+1) r)) (y : Fin n → ℝ)
    (hy : y ∈ WilkiesDesign.E.cubeC n ∩ Work.WilE2.Zset (Work.WilE2.chainFace c j σ)
      (g.image (Work.WilE2.faceSub j σ))) :
    Work.WilE2.faceLift j σ y ∈ WilkiesDesign.E.cubeC (n+1) ∩ Work.WilE2.Zset c g ∩
      {x : Fin (n+1) → ℝ | x j = σ} := by
  obtain ⟨hyc, hyz⟩ := hy
  exact ⟨⟨faceLift_mem_cube j hσ hyc, faceLift_mem_Zset c j σ g hyz⟩, faceLift_apply_same j σ y⟩

end Work.WilE2
