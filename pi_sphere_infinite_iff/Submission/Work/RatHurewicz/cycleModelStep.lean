import Mathlib
import Submission.Work.RatHurewicz.cycleModelDefs
import Submission.Work.RatHurewicz.cycleModelPathConnected
import Submission.Work.RatHurewicz.cycleChain_d
import Submission.Work.RatHurewicz.finiteRangeOfFg
import Submission.Work.StemsB.PiMap

/-!
# The model of a cycle of positive degree, with a finitely generated `π₁`

Given a cycle `z` in degree `n+1 ≥ 1`, the model of `z` (its top cells are the `(n+1)`-simplices in
the support of `z`) is path connected (`Work.RatHurewicz.subsingleton_pi0_model`), the model chain
`cycleChain` is a cycle (`Work.RatHurewicz.cycleChain_d`) which maps to `z`
(`Work.RatHurewicz.cycleChain_map`), and if `π₁` of the model at its base point is finitely
generated, then the image of `π₁` of the model in `π₁(X)` is finite: this is the combination of
`Work.RatHurewicz.finiteRangeOfFg` with the fact that `π₁(X)` is an abelian torsion group.
-/

open CategoryTheory CategoryTheory.Limits AlgebraicTopology
open scoped Topology Simplicial unitInterval

attribute [local implicit_reducible] AlgebraicTopology.singularChainComplexFunctor

namespace Work.RatHurewicz

noncomputable section

variable {X : Type} [TopologicalSpace X] {x₀ : X}

/-- The base point of the model of a cycle maps to the base point of `X`. -/
theorem cycleModelToX_modelBase (hconnX : Subsingleton (HomotopyGroup (Fin 0) X x₀)) (n : ℕ)
    (z : (Work.Cohomology.singularChains ℚ (TopCat.of X)).X (n + 1))
    [Nonempty (cycleMData hconnX n z).Idx] :
    cycleModelToX hconnX n z (modelBase (cycleMData hconnX n z)) = x₀ := by
  show toXFun (cycleMData hconnX n z)
    (Sum.inr ⟨(Classical.choice (inferInstance : Nonempty (cycleMData hconnX n z).Idx)),
      (1 : unitInterval)⟩) = x₀
  exact (cycleMData hconnX n z).arc_one _

/-- **The model of a cycle of degree `n+1 ≥ 1`**: a path connected space with a cycle lifting `z`,
whose `π₁`-image in `π₁(X)` is finite as soon as `π₁` of the model is finitely generated. -/
theorem exists_model_cycle (hconnX : Subsingleton (HomotopyGroup (Fin 0) X x₀)) (n : ℕ)
    (z : (Work.Cohomology.singularChains ℚ (TopCat.of X)).X (n + 1))
    (hz : (Work.Cohomology.singularChains ℚ (TopCat.of X)).d (n + 1) n z = 0)
    [Nonempty (cycleMData hconnX n z).Idx]
    (hfg : Group.FG (HomotopyGroup (Fin 1) (cycleModelSpace hconnX n z)
      (modelBase (cycleMData hconnX n z))))
    (hcomm : ∀ a b : HomotopyGroup (Fin 1) X x₀, a * b = b * a)
    (htors : ∀ α : HomotopyGroup (Fin 1) X x₀, ∃ K : ℕ, 0 < K ∧ α ^ K = 1) :
    ∃ (Y : Type) (_ : TopologicalSpace Y) (y₀ : Y) (φ : C(Y, X))
      (w : (Work.Cohomology.singularChains ℚ (TopCat.of Y)).X (n + 1)),
      Subsingleton (HomotopyGroup (Fin 0) Y y₀) ∧
      (Work.Cohomology.singularChains ℚ (TopCat.of Y)).d (n + 1) n w = 0 ∧
      (Work.Cohomology.chainMap ℚ (TopCat.of Y) (TopCat.of X) (TopCat.ofHom φ)).f (n + 1) w = z ∧
      (Set.range (Work.StemsB.πmap φ 0 y₀)).Finite := by
  refine ⟨Model (cycleMData hconnX n z), inferInstance, modelBase (cycleMData hconnX n z),
    cycleModelToX hconnX n z, cycleChain hconnX n z, ?_, ?_, ?_, ?_⟩
  · exact subsingleton_pi0_model (cycleMData hconnX n z)
  · exact cycleChain_d hconnX n z hz
  · exact cycleChain_map hconnX n z
  · have hbase := cycleModelToX_modelBase hconnX n z
    refine finiteRangeOfFg hfg ?_ ?_
      (Work.StemsB.πmap (cycleModelToX hconnX n z) 0 (modelBase (cycleMData hconnX n z)))
    · exact hbase.symm ▸ hcomm
    · exact hbase.symm ▸ htors

end

end Work.RatHurewicz
