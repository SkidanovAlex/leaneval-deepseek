import Mathlib
import Submission.Work.Drive.FamBox.Flow
import Submission.Work.Drive.FamBox.finite_boxBMeet
import Submission.Work.Drive.FamBox.boxMapsTo_flowV_boxMeet

/-!
# The same-box parity engine

Combines `exists_tangential_field_box` (Defs), the flow invariance (`boxMapsTo_flowV_boxMeet`), the
finite chart cover (`exists_flowCover_box`) and the abstract pairing of the boundary points of a
tangentially flowed set (`Work.Drive.even_ncard_boundary`) into the engine:

**if two smooth maps `F G : ℝ⁵ → M` into a smooth `4`-manifold meet transversally on the box (the
derivative of the difference surjective at every meet) and every boundary meet lies on exactly one
face transversally, then the boundary meet set is finite and has even cardinality.**
-/

namespace Work.Drive.FamBox

open scoped Manifold ContDiff Topology
open Manifold Set

noncomputable section

variable {M : Type*} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M] [IsManifold (𝓡 4) Ctop M]

/-- **The same-box boundary parity engine.** -/
theorem even_ncard_boxBMeet (F G : Amb 4 → M)
    (hF : ContMDiff (𝓡 5) (𝓡 4) Ctop F) (hG : ContMDiff (𝓡 5) (𝓡 4) Ctop G)
    (htrans : ∀ x : Amb 4, x ∈ Submission.Drive.unitBox 4 → F x = G x →
      Function.Surjective (Lf F G x))
    (hface : ∀ b : Amb 4, b ∈ Submission.Drive.unitBox 4 → F b = G b →
      b ∈ Submission.Drive.unitBoxBdry 4 →
      ∃ i : Fin 5, (b i = 0 ∨ b i = 1) ∧ (∀ j : Fin 5, j ≠ i → b j ∈ Set.Ioo (0 : ℝ) 1) ∧
        ∃ σ : Amb 4, Lf F G b σ = 0 ∧ σ i ≠ 0) :
    (boxBMeet F G).Finite ∧ Even (boxBMeet F G).ncard := by
  obtain ⟨V, hV, hVsupp, hVne, hVtan⟩ := exists_tangential_field_box F G hF hG htrans
  have hfaceV := face_data_box F G hF hG htrans V hVtan hVne hface
  have hmapsTo := boxMapsTo_flowV_boxMeet F G hF hG htrans V hV hVsupp hVtan hfaceV
  obtain ⟨Cov⟩ := exists_flowCover_box F G hF hG htrans V hV hVsupp hVtan hVne hmapsTo
  have hset : boxBMeet F G = boxMeet F G ∩ Submission.Drive.unitBoxBdry 4 := by
    ext x
    simp only [boxBMeet, boxMeet, Set.mem_setOf_eq, Set.mem_inter_iff]
    tauto
  refine ⟨finite_boxBMeet F G hF hG htrans hface, ?_⟩
  rw [hset]
  exact even_ncard_boundary (boxFlowSetup F G V hV hVsupp hmapsTo) Cov
    (fun b hb => hfaceV b hb.1 hb.2)

end

end Work.Drive.FamBox
