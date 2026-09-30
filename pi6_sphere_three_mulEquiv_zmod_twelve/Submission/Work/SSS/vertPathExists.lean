import Mathlib
import Submission.Work.Cohomology.SingBridge
import Submission.Work.SSS.vertRestrPath

namespace Work.SSS

open CategoryTheory CategoryTheory.Limits Simplicial Opposite MonoidalCategory
open scoped MonoidalCategory Simplicial Topology

noncomputable section

/-- The monotone map `⦋1⦌ ⟶ ⦋s+1⦌` sending `0 ↦ 0`, `1 ↦ 1`; its image under the standard
simplex cosimplicial object `SSet.stdSimplex` is `Work.SSS.vertEdge s`, the `(0,1)`-edge of
`Δ[s+1]`. -/
def vertEdgeHom (s : ℕ) : SimplexCategory.mk 1 ⟶ SimplexCategory.mk (s+1) :=
  SimplexCategory.mkHom
    { toFun := fun i => ⟨i.val, by have := i.isLt; omega⟩
      monotone' := fun a b hab => by simp only [Fin.le_def] at *; omega }

theorem vertEdge_eq_map_vertEdgeHom (s : ℕ) :
    Work.SSS.vertEdge s = SSet.stdSimplex.map (vertEdgeHom s) := rfl

/-- **The continuous map underlying the edge simplex.**  Evaluating `vertEdgeMap s σ` at a point
`z` of `Δ¹` is evaluating the continuous map underlying `σ` at the image of `z` under the
monotone map induced by `vertEdgeHom s`.  This is the naturality of the identification
`(Sing B)_n ≃ C(Δⁿ, B)`. -/
lemma vertEdgeMap_apply {B : Type} [TopologicalSpace B] (s : ℕ)
    (σ : (SSet.stdSimplex.obj (SimplexCategory.mk (s+1)) : SSet.{0}) ⟶ Work.SSS.sSing B)
    (z : stdSimplex ℝ (Fin 2)) :
    Work.SSS.vertEdgeMap s σ z =
      (TopCat.toSSetObjEquivT (TopCat.of B) (Opposite.op (SimplexCategory.mk (s+1)))
        (SSet.yonedaEquiv σ)) (stdSimplex.map (⇑(ConcreteCategory.hom (vertEdgeHom s))) z) := by
  rw [Work.SSS.vertEdgeMap, Work.SSS.vertEdgeSimplex, vertEdge_eq_map_vertEdgeHom]
  rw [← SSet.yonedaEquiv_naturality (vertEdgeHom s) σ]
  exact TopCat.toSSetObjEquivT_naturality_apply (vertEdgeHom s) (SSet.yonedaEquiv σ) z

/-- The `(0,1)`-edge of `σ`, evaluated at the vertex `0`, is the `0`-th vertex of `σ`. -/
lemma vertEdgeMap_vertex_zero {B : Type} [TopologicalSpace B] (s : ℕ)
    (σ : (SSet.stdSimplex.obj (SimplexCategory.mk (s+1)) : SSet.{0}) ⟶ Work.SSS.sSing B) :
    Work.SSS.vertEdgeMap s σ (stdSimplex.vertex (0 : Fin 2)) = Work.SSS.sigmaVert σ := by
  rw [vertEdgeMap_apply]
  have hv : (stdSimplex.map (⇑(ConcreteCategory.hom (vertEdgeHom s)))
      (stdSimplex.vertex (0 : Fin 2)) : stdSimplex ℝ (Fin (s+2))) = stdSimplex.vertex (0 : Fin (s+2)) := by
    rw [stdSimplex.map_vertex]
    congr 1
  rw [hv]
  rw [Work.SSS.sigmaVert]

/-- The `(0,1)`-edge of `σ`, evaluated at the vertex `1`, is the `0`-th vertex of the `0`-th face
`δ 0 ≫ σ` (which omits the vertex `0` of `Δ[s+1]`, so its `0`-th vertex is `v₁`). -/
lemma vertEdgeMap_vertex_one {B : Type} [TopologicalSpace B] (s : ℕ)
    (σ : (SSet.stdSimplex.obj (SimplexCategory.mk (s+1)) : SSet.{0}) ⟶ Work.SSS.sSing B) :
    Work.SSS.vertEdgeMap s σ (stdSimplex.vertex (1 : Fin 2))
      = Work.SSS.sigmaVert (SSet.stdSimplex.δ (n := s) 0 ≫ σ) := by
  rw [vertEdgeMap_apply]
  have hv : (stdSimplex.map (⇑(ConcreteCategory.hom (vertEdgeHom s)))
      (stdSimplex.vertex (1 : Fin 2)) : stdSimplex ℝ (Fin (s+2))) = stdSimplex.vertex (1 : Fin (s+2)) := by
    rw [stdSimplex.map_vertex]
    congr 1
  rw [hv]
  rw [Work.SSS.sigmaVert]
  have hδ : SSet.yonedaEquiv (SSet.stdSimplex.δ (n := s) 0 ≫ σ) =
      (Work.SSS.sSing B).map (SimplexCategory.δ (n := s) (0 : Fin (s+2))).op (SSet.yonedaEquiv σ) := by
    show SSet.yonedaEquiv
      (SSet.stdSimplex.map (SimplexCategory.δ (n := s) (0 : Fin (s+2))) ≫ σ) = _
    exact (SSet.yonedaEquiv_naturality (SimplexCategory.δ (n := s) (0 : Fin (s+2))) σ).symm
  rw [hδ]
  rw [TopCat.toSSetObjEquivT_naturality_apply (SimplexCategory.δ (n := s) (0 : Fin (s+2)))
      (SSet.yonedaEquiv σ) (stdSimplex.vertex (0 : Fin (s+1)))]
  have hv2 : (stdSimplex.map (⇑(ConcreteCategory.hom (SimplexCategory.δ (n := s) (0 : Fin (s+2)))))
      (stdSimplex.vertex (0 : Fin (s+1))) : stdSimplex ℝ (Fin (s+2))) = stdSimplex.vertex (1 : Fin (s+2)) := by
    rw [stdSimplex.map_vertex]
    congr 1
  rw [hv2]

/-- The inverse of the homeomorphism `Δ¹ ≅ I` at `0` is the vertex `0`. -/
lemma stdSimplexHomeomorphUnitInterval_symm_zero :
    stdSimplexHomeomorphUnitInterval.symm (0 : unitInterval) = stdSimplex.vertex (0 : Fin 2) := by
  rw [← stdSimplexHomeomorphUnitInterval_zero]
  exact stdSimplexHomeomorphUnitInterval.symm_apply_apply _

/-- The inverse of the homeomorphism `Δ¹ ≅ I` at `1` is the vertex `1`. -/
lemma stdSimplexHomeomorphUnitInterval_symm_one :
    stdSimplexHomeomorphUnitInterval.symm (1 : unitInterval) = stdSimplex.vertex (1 : Fin 2) := by
  rw [← stdSimplexHomeomorphUnitInterval_one]
  exact stdSimplexHomeomorphUnitInterval.symm_apply_apply _

/-- The path in `B` underlying the `(0,1)`-edge of a simplex `σ`, with endpoints and the
compatibility that the canonical `1`-simplex of the interval induces the singular `1`-simplex of the
edge. -/
theorem vertPathExists {B : Type} [TopologicalSpace B] (s : ℕ) (b : B)
    (σ : (SSet.stdSimplex.obj (SimplexCategory.mk (s+1)) : SSet.{0}) ⟶ Work.SSS.sSing B)
    (h : Work.SSS.sigmaVert σ = b) :
    ∃ γ : Path b (Work.SSS.sigmaVert (SSet.stdSimplex.δ (n := s) 0 ≫ σ)),
      (Work.SSS.sSingP γ.toContinuousMap).app (Opposite.op (SimplexCategory.mk 1))
        Work.SSS.lambda1 = Work.SSS.vertEdgeSimplex s σ := by
  have hcont : Continuous fun t : unitInterval =>
      Work.SSS.vertEdgeMap s σ (stdSimplexHomeomorphUnitInterval.symm t) :=
    (Work.SSS.vertEdgeMap s σ).continuous.comp stdSimplexHomeomorphUnitInterval.symm.continuous
  refine ⟨⟨⟨fun t => Work.SSS.vertEdgeMap s σ (stdSimplexHomeomorphUnitInterval.symm t), hcont⟩, ?_, ?_⟩, ?_⟩
  · show Work.SSS.vertEdgeMap s σ (stdSimplexHomeomorphUnitInterval.symm 0) = b
    rw [stdSimplexHomeomorphUnitInterval_symm_zero, vertEdgeMap_vertex_zero, h]
  · show Work.SSS.vertEdgeMap s σ (stdSimplexHomeomorphUnitInterval.symm 1)
      = Work.SSS.sigmaVert (SSet.stdSimplex.δ (n := s) 0 ≫ σ)
    rw [stdSimplexHomeomorphUnitInterval_symm_one, vertEdgeMap_vertex_one]
  · exact Work.SSS.sSing_comp_lambda1_eq s σ
      ⟨fun t => Work.SSS.vertEdgeMap s σ (stdSimplexHomeomorphUnitInterval.symm t), hcont⟩ rfl

end

end Work.SSS
