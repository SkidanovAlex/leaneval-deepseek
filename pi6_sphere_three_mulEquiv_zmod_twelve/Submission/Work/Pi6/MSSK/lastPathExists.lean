import Mathlib
import Submission.Work.Pi6.MSSK.LastEdge
import Submission.Work.SSSR.vertRestrPath
set_option backward.isDefEq.respectTransparency false  -- v435port
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 800000

open CategoryTheory CategoryTheory.Limits Simplicial Opposite

namespace Work.Pi6.MSSK

noncomputable section

/-- **`sigmaVert` of a simplicial map out of the standard simplex.**  For a map
`a : Δ[m] ⟶ Δ[n]` and a simplex `θ : Δ[n] ⟶ Sing B`, the point underlying the composite
`Δ[m] → Δ[n] → Sing B` is the value of the continuous map underlying `θ` at the image under `a`
of the `0`-th vertex of `Δ[m]`. -/
lemma sigmaVert_stdSimplex_map {B : Type} [TopologicalSpace B] {n m : ℕ}
    (a : SimplexCategory.mk m ⟶ SimplexCategory.mk n)
    (θ : (SSet.stdSimplex.obj (SimplexCategory.mk n) : SSet.{0}) ⟶ Work.SSSR.sSing B) :
    Work.SSSR.sigmaVert (SSet.stdSimplex.map a ≫ θ) =
      (TopCat.toSSetObjEquivT (TopCat.of B) (Opposite.op (SimplexCategory.mk n))
        (SSet.yonedaEquiv θ))
        (stdSimplex.map (⇑(ConcreteCategory.hom a)) (stdSimplex.vertex (0 : Fin (m+1)))) := by
  have h1 : SSet.yonedaEquiv (SSet.stdSimplex.map a ≫ θ)
      = (TopCat.toSSet.obj (TopCat.of B)).map a.op (SSet.yonedaEquiv θ) :=
    (SSet.yonedaEquiv_naturality a θ).symm
  rw [Work.SSSR.sigmaVert, h1]
  rw [TopCat.toSSetObjEquivT_naturality_apply a (SSet.yonedaEquiv θ)
    (stdSimplex.vertex (0 : Fin (m+1)))]

/-- **The continuous map underlying the last-edge simplex.**  Evaluating `lastEdgeMap t σ` at a
point `z` of `Δ¹` is evaluating the continuous map underlying `σ` at the image of `z` under the
monotone map `lastEdgeHom t` (the last edge `{t, t+1}` of `Δ[t+1]`).  This is the naturality of the
identification `(Sing B)_n ≃ C(Δⁿ, B)`. -/
lemma lastEdgeMap_apply {B : Type} [TopologicalSpace B] (t : ℕ)
    (σ : (SSet.stdSimplex.obj (SimplexCategory.mk (t+1)) : SSet.{0}) ⟶ Work.SSSR.sSing B)
    (z : stdSimplex ℝ (Fin 2)) :
    Work.Pi6.MSSK.lastEdgeMap t σ z =
      (TopCat.toSSetObjEquivT (TopCat.of B) (Opposite.op (SimplexCategory.mk (t+1)))
        (SSet.yonedaEquiv σ))
        (stdSimplex.map (⇑(ConcreteCategory.hom (Work.Pi6.MSSK.lastEdgeHom t))) z) := by
  rw [Work.Pi6.MSSK.lastEdgeMap, Work.Pi6.MSSK.lastEdgeSimplex, Work.Pi6.MSSK.lastEdge]
  rw [← SSet.yonedaEquiv_naturality (Work.Pi6.MSSK.lastEdgeHom t) σ]
  exact TopCat.toSSetObjEquivT_naturality_apply (Work.Pi6.MSSK.lastEdgeHom t)
    (SSet.yonedaEquiv σ) z

/-- The `0`-th vertex of the last edge `{t, t+1}` of `σ` is the vertex `t` of `σ`. -/
lemma lastEdgeMap_vertex_zero {B : Type} [TopologicalSpace B] (t : ℕ)
    (σ : (SSet.stdSimplex.obj (SimplexCategory.mk (t+1)) : SSet.{0}) ⟶ Work.SSSR.sSing B) :
    Work.Pi6.MSSK.lastEdgeMap t σ (stdSimplex.vertex (0 : Fin 2))
      = Work.SSSR.sigmaVert (Work.Pi6.MSSK.lastV t ≫
          SSet.stdSimplex.δ (n := t) (Fin.last (t+1)) ≫ σ) := by
  rw [lastEdgeMap_apply]
  simp only [Work.Pi6.MSSK.lastV]
  rw [sigmaVert_stdSimplex_map]
  rw [show stdSimplex.map (⇑(ConcreteCategory.hom
        (SimplexCategory.const (SimplexCategory.mk 0) (SimplexCategory.mk t) (Fin.last t))))
        (stdSimplex.vertex (0 : Fin 1)) = stdSimplex.vertex (Fin.last t) from by
      rw [stdSimplex.map_vertex]; rfl]
  have hδ : SSet.yonedaEquiv (SSet.stdSimplex.δ (n := t) (Fin.last (t+1)) ≫ σ)
      = (Work.SSSR.sSing B).map (SimplexCategory.δ (n := t) (Fin.last (t+1))).op
          (SSet.yonedaEquiv σ) := by
    show SSet.yonedaEquiv
      (SSet.stdSimplex.map (SimplexCategory.δ (n := t) (Fin.last (t+1))) ≫ σ) = _
    exact (SSet.yonedaEquiv_naturality (SimplexCategory.δ (n := t) (Fin.last (t+1))) σ).symm
  rw [hδ]
  rw [TopCat.toSSetObjEquivT_naturality_apply (SimplexCategory.δ (n := t) (Fin.last (t+1)))
        (SSet.yonedaEquiv σ) (stdSimplex.vertex (Fin.last t))]
  rw [stdSimplex.map_vertex, stdSimplex.map_vertex]
  have hfin : (ConcreteCategory.hom (Work.Pi6.MSSK.lastEdgeHom t)) (0 : Fin 2)
      = (ConcreteCategory.hom (SimplexCategory.δ (n := t) (Fin.last (t+1)))) (Fin.last t) := by
    rw [show (ConcreteCategory.hom (SimplexCategory.δ (n := t) (Fin.last (t+1)))) (Fin.last t)
          = (Fin.last t).castSucc from by
        rw [show (ConcreteCategory.hom (SimplexCategory.δ (n := t) (Fin.last (t+1)))) (Fin.last t)
              = Fin.succAbove (Fin.last (t+1)) (Fin.last t) from rfl, Fin.succAbove_last]]
    rfl
  rw [hfin]

/-- The `1`-st vertex of the last edge `{t, t+1}` of `σ` is the vertex `t+1` of `σ`. -/
lemma lastEdgeMap_vertex_one {B : Type} [TopologicalSpace B] (t : ℕ)
    (σ : (SSet.stdSimplex.obj (SimplexCategory.mk (t+1)) : SSet.{0}) ⟶ Work.SSSR.sSing B) :
    Work.Pi6.MSSK.lastEdgeMap t σ (stdSimplex.vertex (1 : Fin 2))
      = Work.SSSR.sigmaVert (Work.Pi6.MSSK.lastV (t+1) ≫ σ) := by
  rw [lastEdgeMap_apply]
  simp only [Work.Pi6.MSSK.lastV]
  rw [sigmaVert_stdSimplex_map]
  rw [show stdSimplex.map (⇑(ConcreteCategory.hom
        (SimplexCategory.const (SimplexCategory.mk 0) (SimplexCategory.mk (t+1))
          (Fin.last (t+1)))))
        (stdSimplex.vertex (0 : Fin 1)) = stdSimplex.vertex (Fin.last (t+1)) from by
      rw [stdSimplex.map_vertex]; rfl]
  rw [stdSimplex.map_vertex]
  have hfin : (ConcreteCategory.hom (Work.Pi6.MSSK.lastEdgeHom t)) (1 : Fin 2)
      = Fin.last (t+1) := rfl
  rw [hfin]

/-- The inverse of the homeomorphism `Δ¹ ≅ I` at `0` is the vertex `0`. -/
lemma lastEdgeSymm_zero :
    stdSimplexHomeomorphUnitInterval.symm (0 : unitInterval) = stdSimplex.vertex (0 : Fin 2) := by
  rw [← stdSimplexHomeomorphUnitInterval_zero]
  exact stdSimplexHomeomorphUnitInterval.symm_apply_apply _

/-- The inverse of the homeomorphism `Δ¹ ≅ I` at `1` is the vertex `1`. -/
lemma lastEdgeSymm_one :
    stdSimplexHomeomorphUnitInterval.symm (1 : unitInterval) = stdSimplex.vertex (1 : Fin 2) := by
  rw [← stdSimplexHomeomorphUnitInterval_one]
  exact stdSimplexHomeomorphUnitInterval.symm_apply_apply _

/-- **The key compatibility for the last edge**: if `γ` is the continuous path in `B` whose
underlying map is `lastEdgeMap t σ` precomposed with the inverse of the homeomorphism `Δ¹ ≅ I`,
then the canonical `1`-simplex of the interval induces the singular `1`-simplex of the last edge. -/
lemma lastEdge_sSing_comp_lambda1 {B : Type} [TopologicalSpace B] (t : ℕ)
    (σ : (SSet.stdSimplex.obj (SimplexCategory.mk (t+1)) : SSet.{0}) ⟶ Work.SSSR.sSing B)
    (γ : C(unitInterval, B))
    (hγ : ⇑γ = fun x => Work.Pi6.MSSK.lastEdgeMap t σ
        (stdSimplexHomeomorphUnitInterval.symm x)) :
    (Work.SSSR.sSingP γ).app (Opposite.op (SimplexCategory.mk 1)) Work.SSSR.lambda1
      = Work.Pi6.MSSK.lastEdgeSimplex t σ := by
  apply (TopCat.toSSetObjEquivT (TopCat.of B) (Opposite.op (SimplexCategory.mk 1))).injective
  have h1 : (TopCat.toSSetObjEquivT (TopCat.of B) (Opposite.op (SimplexCategory.mk 1)))
      ((Work.SSSR.sSingP γ).app (Opposite.op (SimplexCategory.mk 1)) Work.SSSR.lambda1)
      = γ.comp ((TopCat.toSSetObjEquivT (TopCat.of unitInterval)
          (Opposite.op (SimplexCategory.mk 1))) Work.SSSR.lambda1) := rfl
  rw [h1, Work.SSSR.lambda1_apply]
  refine ContinuousMap.ext fun z => ?_
  simp only [ContinuousMap.comp_apply, ContinuousMap.coe_mk]
  rw [hγ]
  exact congrArg (fun x => (TopCat.toSSetObjEquivT (TopCat.of B)
    (Opposite.op (SimplexCategory.mk 1))) (Work.Pi6.MSSK.lastEdgeSimplex t σ) x)
    (stdSimplexHomeomorphUnitInterval.symm_apply_apply z)

theorem lastPathExists {B : Type} [TopologicalSpace B] (t : ℕ)
    (σ : (SSet.stdSimplex.obj (SimplexCategory.mk (t+1)) : SSet.{0}) ⟶ Work.SSSR.sSing B) :
    ∃ γ : Path (Work.SSSR.sigmaVert (CategoryTheory.CategoryStruct.comp
            (Work.Pi6.MSSK.lastV t) (CategoryTheory.CategoryStruct.comp
              (SSet.stdSimplex.δ (n := t) (Fin.last (t+1))) σ)))
        (Work.SSSR.sigmaVert (CategoryTheory.CategoryStruct.comp
            (Work.Pi6.MSSK.lastV (t+1)) σ)),
      (Work.SSSR.sSingP γ.toContinuousMap).app (Opposite.op (SimplexCategory.mk 1))
        Work.SSSR.lambda1 = Work.Pi6.MSSK.lastEdgeSimplex t σ := by
  have hcont : Continuous fun x : unitInterval =>
      Work.Pi6.MSSK.lastEdgeMap t σ (stdSimplexHomeomorphUnitInterval.symm x) :=
    (Work.Pi6.MSSK.lastEdgeMap t σ).continuous.comp
      stdSimplexHomeomorphUnitInterval.symm.continuous
  refine ⟨⟨⟨fun x => Work.Pi6.MSSK.lastEdgeMap t σ (stdSimplexHomeomorphUnitInterval.symm x),
    hcont⟩, ?_, ?_⟩, ?_⟩
  · show Work.Pi6.MSSK.lastEdgeMap t σ (stdSimplexHomeomorphUnitInterval.symm 0)
      = Work.SSSR.sigmaVert (Work.Pi6.MSSK.lastV t ≫
          SSet.stdSimplex.δ (n := t) (Fin.last (t+1)) ≫ σ)
    rw [lastEdgeSymm_zero, lastEdgeMap_vertex_zero]
  · show Work.Pi6.MSSK.lastEdgeMap t σ (stdSimplexHomeomorphUnitInterval.symm 1)
      = Work.SSSR.sigmaVert (Work.Pi6.MSSK.lastV (t+1) ≫ σ)
    rw [lastEdgeSymm_one, lastEdgeMap_vertex_one]
  · exact lastEdge_sSing_comp_lambda1 t σ
      ⟨fun x => Work.Pi6.MSSK.lastEdgeMap t σ (stdSimplexHomeomorphUnitInterval.symm x), hcont⟩ rfl

end

end Work.Pi6.MSSK
