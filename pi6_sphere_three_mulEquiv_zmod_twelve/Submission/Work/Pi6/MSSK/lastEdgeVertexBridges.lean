import Mathlib
import Submission.Work.Pi6.MSSK.LastEdge
set_option backward.isDefEq.respectTransparency false  -- v435port
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

set_option autoImplicit false
set_option maxHeartbeats 1600000

open CategoryTheory CategoryTheory.Limits Simplicial Opposite

namespace Work.Pi6.MSSK

noncomputable section

/-- The last vertex of `Δ[1]`, followed by the last edge `{t, t+1}` of `Δ[t+1]`, is the last
vertex of `Δ[t+1]`. -/
lemma lastEdgeVertexBridges_fst (t : ℕ) :
    CategoryTheory.CategoryStruct.comp (lastV 1) (lastEdge t) = lastV (t+1) := by
  simp only [lastV, lastEdge, ← SSet.stdSimplex.map_comp]
  apply congrArg SSet.stdSimplex.map
  rw [SimplexCategory.const_comp]
  congr 1

/-- The first vertex of `Δ[1]`, followed by the last edge `{t, t+1}` of `Δ[t+1]`, equals the last
vertex of `Δ[t]` followed by the last coface `δ_{t+1} : Δ[t] ⟶ Δ[t+1]`. -/
lemma lastEdgeVertexBridges_snd (t : ℕ) :
    CategoryTheory.CategoryStruct.comp (firstV 1) (lastEdge t)
      = CategoryTheory.CategoryStruct.comp (lastV t)
          (SSet.stdSimplex.δ (n := t) (Fin.last (t+1))) := by
  have hδ : SSet.stdSimplex.δ (n := t) (Fin.last (t+1))
      = SSet.stdSimplex.map (SimplexCategory.δ (Fin.last (t+1))) := rfl
  simp only [firstV, lastV, lastEdge]
  rw [hδ]
  simp only [← SSet.stdSimplex.map_comp]
  apply congrArg SSet.stdSimplex.map
  rw [SimplexCategory.const_comp, SimplexCategory.const_comp]
  congr 1
  simp only [SimplexCategory.δ, SimplexCategory.mkHom, SimplexCategory.Hom.toOrderHom_mk,
    OrderEmbedding.toOrderHom_coe, Fin.succAboveOrderEmb_apply, lastEdgeHom]
  rw [Fin.succAbove_of_castSucc_lt (Fin.last (t+1)) (Fin.last t)
    (by simp [Fin.castSucc, Fin.last])]
  rfl

theorem lastEdgeVertexBridges (t : ℕ) :
    (CategoryTheory.CategoryStruct.comp (Work.Pi6.MSSK.lastV 1) (Work.Pi6.MSSK.lastEdge t)
        = Work.Pi6.MSSK.lastV (t+1))
    ∧ (CategoryTheory.CategoryStruct.comp (Work.Pi6.MSSK.firstV 1) (Work.Pi6.MSSK.lastEdge t)
        = CategoryTheory.CategoryStruct.comp (Work.Pi6.MSSK.lastV t)
            (SSet.stdSimplex.δ (n := t) (Fin.last (t+1)))) := by
  exact ⟨lastEdgeVertexBridges_fst t, lastEdgeVertexBridges_snd t⟩

end

end Work.Pi6.MSSK
