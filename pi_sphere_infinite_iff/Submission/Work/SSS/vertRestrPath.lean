import Mathlib
import Submission.Work.Cohomology.SingBridge
import Submission.Work.SSS.piszDefs
import Submission.Work.SSS.transport_eq_topEnd

set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace Work.SSS

open CategoryTheory CategoryTheory.Limits Simplicial Opposite MonoidalCategory
open scoped MonoidalCategory Simplicial Topology

noncomputable section

variable {E B : Type} [TopologicalSpace E] [TopologicalSpace B]

/-- The `(0,1)`-edge of `Δ[s+1]`. -/
def vertEdge (s : ℕ) :
    (SSet.stdSimplex.obj (SimplexCategory.mk 1) : SSet.{0}) ⟶
      (SSet.stdSimplex.obj (SimplexCategory.mk (s+1)) : SSet.{0}) :=
  SSet.stdSimplex.map (SimplexCategory.mkHom
    { toFun := fun i => ⟨i.val, by have := i.isLt; omega⟩
      monotone' := fun a b hab => by simp only [Fin.le_def] at *; omega })

/-- The singular `1`-simplex of the `(0,1)`-edge of `σ`. -/
def vertEdgeSimplex (s : ℕ)
    (σ : (SSet.stdSimplex.obj (SimplexCategory.mk (s+1)) : SSet.{0}) ⟶ sSing B) :
    (Work.SSS.sSing B) _⦋1⦌ :=
  SSet.yonedaEquiv (vertEdge s ≫ σ)

/-- The canonical `1`-simplex of the unit interval. -/
def lambda1 : (Work.SSS.sSing unitInterval) _⦋1⦌ :=
  (TopCat.toSSetObjEquivT (TopCat.of unitInterval) (Opposite.op (SimplexCategory.mk 1))).symm
    ⟨⇑stdSimplexHomeomorphUnitInterval, stdSimplexHomeomorphUnitInterval.continuous⟩

/-- The continuous map underlying the edge simplex, as a map `stdSimplex ℝ (Fin 2) → B`. -/
def vertEdgeMap (s : ℕ)
    (σ : (SSet.stdSimplex.obj (SimplexCategory.mk (s+1)) : SSet.{0}) ⟶ sSing B) :
    C(↥(stdSimplex ℝ (Fin 2)), B) :=
  TopCat.toSSetObjEquivT (TopCat.of B) (Opposite.op (SimplexCategory.mk 1))
    (vertEdgeSimplex s σ)

theorem lambda1_apply :
    (TopCat.toSSetObjEquivT (TopCat.of unitInterval) (Opposite.op (SimplexCategory.mk 1))) lambda1
      = ⟨⇑stdSimplexHomeomorphUnitInterval, stdSimplexHomeomorphUnitInterval.continuous⟩ := by
  simp [lambda1]

/-- **The key compatibility**: the canonical `1`-simplex of the interval induces the singular
`1`-simplex of the edge.  More precisely, for any continuous map `γ` whose `toSSetObjEquivT`
transpose is `vertEdgeMap` composed with the inverse of the interval homeomorphism, the composite
`λ₁ ≫ Sing γ` is the edge simplex. -/
theorem sSing_comp_lambda1_eq (s : ℕ)
    (σ : (SSet.stdSimplex.obj (SimplexCategory.mk (s+1)) : SSet.{0}) ⟶ sSing B)
    (γ : C(unitInterval, B))
    (hγ : ⇑γ = fun t => (vertEdgeMap s σ) (stdSimplexHomeomorphUnitInterval.symm t)) :
    (Work.SSS.sSingP γ).app (Opposite.op (SimplexCategory.mk 1)) lambda1
      = vertEdgeSimplex s σ := by
  apply (TopCat.toSSetObjEquivT (TopCat.of B) (Opposite.op (SimplexCategory.mk 1))).injective
  have h1 : (TopCat.toSSetObjEquivT (TopCat.of B) (Opposite.op (SimplexCategory.mk 1)))
      ((Work.SSS.sSingP γ).app (Opposite.op (SimplexCategory.mk 1)) lambda1)
      = γ.comp ((TopCat.toSSetObjEquivT (TopCat.of unitInterval)
          (Opposite.op (SimplexCategory.mk 1))) lambda1) := rfl
  rw [h1, lambda1_apply]
  refine ContinuousMap.ext fun z => ?_
  simp only [ContinuousMap.comp_apply, ContinuousMap.coe_mk]
  rw [hγ]
  exact congrArg (fun x => (TopCat.toSSetObjEquivT (TopCat.of B)
    (Opposite.op (SimplexCategory.mk 1)) (vertEdgeSimplex s σ)) x)
    (stdSimplexHomeomorphUnitInterval.symm_apply_apply z)

end

end Work.SSS
