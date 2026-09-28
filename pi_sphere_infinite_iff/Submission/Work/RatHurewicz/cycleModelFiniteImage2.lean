import Mathlib
import Submission.Work.RatHurewicz.cycleModelDefs
import Submission.Work.RatHurewicz.cycleModelStep
import Submission.Work.RatHurewicz.cycleModelZero
import Submission.Work.RatHurewicz.compress_to_skeleton
import Submission.Work.RatHurewicz.skeletonPiOne_surjective
import Submission.Work.RatHurewicz.skeletonPiOneFg
import Submission.Work.StemsB.PiMap
import Submission.Work.Stems.subsingleton_of_contractible

set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false

namespace Work.RatHurewicz

open CategoryTheory CategoryTheory.Limits AlgebraicTopology
open scoped Topology Simplicial unitInterval

attribute [local implicit_reducible] AlgebraicTopology.singularChainComplexFunctor

noncomputable section

variable {X : Type} [TopologicalSpace X] {x₀ : X}

/-!
## The compactness reduction of a rational cycle to a model with finite `π₁`-image

Given a rational cycle `z` in degree `t` on a space `X` with trivial `π₀` and abelian torsion `π₁`,
we build a space `Y`, a map `φ : Y → X` and a cycle `w` on `Y` with `φ_# w = z`, such that `Y` is
path connected and the image of `π₁(Y, y₀) → π₁(X, φ y₀)` is finite.

The space `Y` is the *model* of the cycle (`Work.RatHurewicz.cycleMData`): one copy of `Δ^{t+1}` for
each simplex of the support of `z`, glued along faces that agree in `X`, plus one arc from a vertex
of each copy to `x₀` (which makes the model path connected).  The cycle `w` is the sum of the
identity simplices of the copies, with the coefficients of `z`, and it is a cycle because `z` is one
(`Work.RatHurewicz.cycleChain_d`); it maps to `z` because the copies are the simplices of `z`
(`Work.RatHurewicz.cycleChain_map`).  Finally `π₁` of the model is a quotient of `π₁` of its
`1`-skeleton, which is a finite graph and hence finitely generated
(`Work.RatHurewicz.piOneModel_fg`), so the image in the abelian torsion group `π₁(X)` is finite
(`Work.RatHurewicz.finiteRangeOfFg`).
-/

/-- **Paths in the model between skeleton points can be pushed into the skeleton**, in the
`CompressRel` form used by `Work.Serre.CWModel.πmap_setIncl_surjective_of_compressRel`. -/
theorem compressRel_one_cycleModel {n : ℕ} (D : MData X n x₀) :
    CompressRel (Model D) (skeleton D) 1 :=
  compressRel_one_of_paths fun y z hy hz p => compress_to_skeleton D y z hy hz p

/-- **The `1`-skeleton generates `π₁` of the model**: the map induced by the inclusion of the
`1`-skeleton is surjective. -/
theorem skeletonPiOneSurjective' {n : ℕ} (D : MData X n x₀) [Nonempty D.Idx] :
    Function.Surjective (Work.StemsB.πmap (setIncl (skeleton D)) 0
      ⟨modelBase D, mem_skeleton_modelBase D⟩) :=
  Work.Serre.CWModel.πmap_setIncl_surjective_of_compressRel 0
    (compressRel_one_cycleModel D) _

/-- **`π₁` of the model of a cycle is finitely generated.**

`π₁` of the model is a quotient of `π₁` of its `1`-skeleton (the compression of loops into the
`1`-skeleton, `Work.RatHurewicz.compress_to_skeleton`), and the `1`-skeleton is a finite graph,
whose fundamental group is finitely generated (`Work.RatHurewicz.skeletonPiOneFg`). -/
theorem piOneModel_fg {n : ℕ} (D : MData X n x₀) [Nonempty D.Idx] :
    Group.FG (HomotopyGroup (Fin 1) (Model D) (modelBase D)) := by
  haveI := skeletonPiOneFg D
  exact Group.fg_of_surjective (skeletonPiOneSurjective' D)

/-- **The trivial model of the zero cycle**: the one-point space, with the zero cycle. -/
theorem exists_model_of_eq_zero (t : ℕ) (hconnX : Subsingleton (HomotopyGroup (Fin 0) X x₀))
    (z : (Work.Cohomology.singularChains ℚ (TopCat.of X)).X t) (hz0 : z = 0) :
    ∃ (Y : Type) (_ : TopologicalSpace Y) (y₀ : Y) (φ : C(Y, X))
      (w : (Work.Cohomology.singularChains ℚ (TopCat.of Y)).X t),
      Subsingleton (HomotopyGroup (Fin 0) Y y₀) ∧
      (Work.Cohomology.singularChains ℚ (TopCat.of Y)).d t (t - 1) w = 0 ∧
      (Work.Cohomology.chainMap ℚ (TopCat.of Y) (TopCat.of X) (TopCat.ofHom φ)).f t w = z ∧
      (Set.range (Work.StemsB.πmap φ 0 y₀)).Finite := by
  refine ⟨PUnit, inferInstance, PUnit.unit, ⟨fun _ => x₀, continuous_const⟩, 0,
    Work.Stems.subsingleton_of_contractible (N := Fin 0) PUnit.unit, ?_, ?_, ?_⟩
  · rw [map_zero]
  · rw [map_zero, hz0]
  · haveI : Subsingleton (HomotopyGroup (Fin 1) PUnit PUnit.unit) :=
      Work.Stems.subsingleton_of_contractible (N := Fin 1) PUnit.unit
    refine Set.Subsingleton.finite fun a ha b hb => ?_
    obtain ⟨x, rfl⟩ := ha
    obtain ⟨y, rfl⟩ := hb
    rw [Subsingleton.elim x y]

/-- The support of a nonzero chain is nonempty. -/
theorem cycleSupport_nonempty_of_ne_zero (m : ℕ)
    (z : (Work.Cohomology.singularChains ℚ (TopCat.of X)).X m) (hz0 : z ≠ 0) :
    (cycleSupport m z).Nonempty := by
  by_contra h
  refine hz0 ?_
  rw [Work.StemsB.chain_eq_sum_genQ (TopCat.toSSet.obj (TopCat.of X)) m z]
  rw [show (Work.StemsB.coordsQ (TopCat.toSSet.obj (TopCat.of X)) m z).support = ∅ from
    Finset.not_nonempty_iff_eq_empty.mp h]
  exact Finset.sum_empty

/-- **The compactness reduction of a rational cycle**: a rational cycle in degree `t` on a space with
trivial `π₀` and abelian torsion `π₁` is carried by a cycle on a model whose `π₁`-image in `π₁(X)`
is finite. -/
theorem cycleModelFiniteImage2 (X : Type) [TopologicalSpace X] (x₀ : X) (t : ℕ)
    (hconnX : Subsingleton (HomotopyGroup (Fin 0) X x₀))
    (z : (Work.Cohomology.singularChains ℚ (TopCat.of X)).X t)
    (hz : (Work.Cohomology.singularChains ℚ (TopCat.of X)).d t (t - 1) z = 0)
    (htors : ∀ α : HomotopyGroup (Fin 1) X x₀, ∃ K : ℕ, 0 < K ∧ α ^ K = 1)
    (hcomm : ∀ a b : HomotopyGroup (Fin 1) X x₀, a * b = b * a) :
    ∃ (Y : Type) (_ : TopologicalSpace Y) (y₀ : Y) (φ : C(Y, X))
      (w : (Work.Cohomology.singularChains ℚ (TopCat.of Y)).X t),
      Subsingleton (HomotopyGroup (Fin 0) Y y₀) ∧
      (Work.Cohomology.singularChains ℚ (TopCat.of Y)).d t (t - 1) w = 0 ∧
      (Work.Cohomology.chainMap ℚ (TopCat.of Y) (TopCat.of X) (TopCat.ofHom φ)).f t w = z ∧
      (Set.range (Work.StemsB.πmap φ 0 y₀)).Finite := by
  rcases t with _ | k
  · by_cases hz0 : z = 0
    · exact exists_model_of_eq_zero 0 hconnX z hz0
    · haveI : Nonempty (constMData hconnX z).Idx :=
        let ⟨s, hs⟩ := cycleSupport_nonempty_of_ne_zero 0 z hz0
        ⟨⟨s, hs⟩⟩
      exact exists_model_zero hconnX z (piOneModel_fg (constMData hconnX z)) hcomm htors
  · by_cases hz0 : z = 0
    · exact exists_model_of_eq_zero (k + 1) hconnX z hz0
    · haveI : Nonempty (cycleMData hconnX k z).Idx :=
        let ⟨s, hs⟩ := cycleSupport_nonempty_of_ne_zero (k + 1) z hz0
        ⟨⟨s, hs⟩⟩
      exact exists_model_cycle hconnX k z hz (piOneModel_fg (cycleMData hconnX k z)) hcomm htors

end

end Work.RatHurewicz
