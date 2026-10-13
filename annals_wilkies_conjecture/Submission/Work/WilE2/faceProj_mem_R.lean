import Mathlib
import Submission.Work.WilE2.FaceDefs

namespace Work.WilE2

theorem faceProj_mem_R {n r : ℕ} (c : WilkiesDesign.E.EAChain (n+1) r) (j : Fin (n+1)) (σ : ℝ)
    (g : Finset (WilkiesDesign.E.EAPoly (n+1) r)) (x : Fin (n+1) → ℝ)
    (hx : x ∈ WilkiesDesign.E.cubeC (n+1) ∩ Work.WilE2.Zset c g ∩
      {x : Fin (n+1) → ℝ | x j = σ}) :
    Work.WilE2.faceProj j x ∈ WilkiesDesign.E.cubeC n ∩
      Work.WilE2.Zset (Work.WilE2.chainFace c j σ) (g.image (Work.WilE2.faceSub j σ)) := by
  -- `x` lies in the cube, in the zero set of `g`, and on the hyperplane `x j = σ`.
  have hcube : x ∈ WilkiesDesign.E.cubeC (n+1) := hx.1.1
  have hz : x ∈ Work.WilE2.Zset c g := hx.1.2
  have hxj : x j = σ := hx.2
  constructor
  · -- The projection stays in the cube: the surviving coordinates are coordinates of `x`.
    intro i
    rw [Work.WilE2.faceProj_apply]
    exact hcube (j.succAbove i)
  · -- Every polynomial of the image vanishes at the projection.
    intro Q hQ
    obtain ⟨f, hf, rfl⟩ := Finset.mem_image.mp hQ
    rw [Work.WilE2.faceSub_eval, Work.WilE2.faceLift_faceProj j σ x hxj]
    exact hz f hf

end Work.WilE2
