import Mathlib
import Submission.Work.Pi6.MSSK.LastEdge
import Submission.Work.Pi6.MSSK.lastEdgeVertexBridges
set_option backward.isDefEq.respectTransparency false  -- v435port
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 800000

open CategoryTheory CategoryTheory.Limits Simplicial Opposite

namespace Work.Pi6.MSSK

noncomputable section

variable {E B : Type} [TopologicalSpace E] [TopologicalSpace B]

/-- The two spellings of the source vertex of the last edge give the same pullback. -/
theorem pullAlongBridge0 (p : C(E, B)) {t : ℕ}
    (σ : (SSet.stdSimplex.obj (SimplexCategory.mk (t+1)) : SSet.{0}) ⟶ Work.SSSR.sSing B) :
    Work.SSSR.pullAlong (Work.SSSR.sSingP p)
        (CategoryTheory.CategoryStruct.comp (firstV 1) (CategoryTheory.CategoryStruct.comp
          (lastEdge t) σ))
      = Work.SSSR.pullAlong (Work.SSSR.sSingP p)
        (CategoryTheory.CategoryStruct.comp (lastV t) (CategoryTheory.CategoryStruct.comp
          (SSet.stdSimplex.δ (n := t) (Fin.last (t+1))) σ)) := by
  have h := congrArg (fun g => CategoryTheory.CategoryStruct.comp g σ)
    (lastEdgeVertexBridges t).2
  simp only [← Category.assoc, h]

/-- The two spellings of the target vertex of the last edge give the same pullback. -/
theorem pullAlongBridge1 (p : C(E, B)) {t : ℕ}
    (σ : (SSet.stdSimplex.obj (SimplexCategory.mk (t+1)) : SSet.{0}) ⟶ Work.SSSR.sSing B) :
    Work.SSSR.pullAlong (Work.SSSR.sSingP p)
        (CategoryTheory.CategoryStruct.comp (lastV 1) (CategoryTheory.CategoryStruct.comp
          (lastEdge t) σ))
      = Work.SSSR.pullAlong (Work.SSSR.sSingP p)
        (CategoryTheory.CategoryStruct.comp (lastV (t+1)) σ) := by
  have h := congrArg (fun g => CategoryTheory.CategoryStruct.comp g σ)
    (lastEdgeVertexBridges t).1
  simp only [← Category.assoc, h]

/-- The base points of the two spellings of the source vertex agree. -/
theorem sigmaVertBridge0 {B : Type} [TopologicalSpace B] {t : ℕ}
    (σ : (SSet.stdSimplex.obj (SimplexCategory.mk (t+1)) : SSet.{0}) ⟶ Work.SSSR.sSing B) :
    Work.SSSR.sigmaVert (CategoryTheory.CategoryStruct.comp (firstV 1)
        (CategoryTheory.CategoryStruct.comp (lastEdge t) σ))
      = Work.SSSR.sigmaVert (CategoryTheory.CategoryStruct.comp (lastV t)
          (CategoryTheory.CategoryStruct.comp (SSet.stdSimplex.δ (n := t) (Fin.last (t+1))) σ)) := by
  have h := congrArg (fun g => CategoryTheory.CategoryStruct.comp g σ)
    (lastEdgeVertexBridges t).2
  simp only [← Category.assoc, h]

/-- The base points of the two spellings of the target vertex agree. -/
theorem sigmaVertBridge1 {B : Type} [TopologicalSpace B] {t : ℕ}
    (σ : (SSet.stdSimplex.obj (SimplexCategory.mk (t+1)) : SSet.{0}) ⟶ Work.SSSR.sSing B) :
    Work.SSSR.sigmaVert (CategoryTheory.CategoryStruct.comp (lastV 1)
        (CategoryTheory.CategoryStruct.comp (lastEdge t) σ))
      = Work.SSSR.sigmaVert (CategoryTheory.CategoryStruct.comp (lastV (t+1)) σ) := by
  have h := congrArg (fun g => CategoryTheory.CategoryStruct.comp g σ)
    (lastEdgeVertexBridges t).1
  simp only [← Category.assoc, h]

end

end Work.Pi6.MSSK
