import Mathlib
import Submission.Work.ThomBordism.Interface
import Submission.Work.ThomBordism.homologyFinite_of_isRetract

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


set_option synthInstance.maxHeartbeats 400000

open scoped Manifold ContDiff
open CategoryTheory AlgebraicTopology

namespace Work.ThomBordism.NullBord

noncomputable section

variable {X : Type} [TopologicalSpace X] [ChartedSpace (EuclideanHalfSpace 9) X]
  [IsManifold (modelWithCornersEuclideanHalfSpace 9) ∞ X]

/-- **Mathlib's Whitney embedding theorem for a compact manifold with corners**: a compact `T²`
`C^∞` manifold with boundary (model `ℝ^9₊`) admits a smooth immersion into some Euclidean space
which is a closed embedding. -/
theorem exists_immersion_closedEmbedding [T2Space X] [CompactSpace X] :
    ∃ (N : ℕ) (e : X → EuclideanSpace ℝ (Fin N)),
      ContMDiff (modelWithCornersEuclideanHalfSpace 9)
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin N))) ∞ e ∧
      Topology.IsClosedEmbedding e ∧
      ∀ x : X, Function.Injective (mfderiv (modelWithCornersEuclideanHalfSpace 9)
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin N))) e x) :=
  exists_embedding_euclidean_of_compact

/-- **The image of a closed embedding of a compact space is homeomorphic to the space.** -/
theorem homeo_range_of_isClosedEmbedding [T2Space X] [CompactSpace X] {N : ℕ}
    {e : X → EuclideanSpace ℝ (Fin N)} (he : Topology.IsClosedEmbedding e) :
    Nonempty (X ≃ₜ ↥(Set.range e)) := by
  have hbij : Function.Bijective (fun x : X => (⟨e x, Set.mem_range_self x⟩ : ↥(Set.range e))) :=
    ⟨fun x x' h => he.injective (Subtype.ext_iff.mp h), fun y => by
      obtain ⟨x, hx⟩ := y.2
      exact ⟨x, Subtype.ext hx⟩⟩
  exact ⟨Continuous.homeoOfEquivCompactToT2 (f := Equiv.ofBijective _ hbij)
    (he.continuous.subtype_mk _)⟩

/-- **Finiteness of singular homology transports along a homeomorphism.** -/
theorem fg_homology_of_homeo {U V : TopCat} (φ : U ≃ₜ V) (k : ℕ)
    (h : Module.Finite ℤ ((Work.Cohomology.chainC ℤ (TopCat.toSSet.obj U)).homology k)) :
    Module.Finite ℤ ((Work.Cohomology.chainC ℤ (TopCat.toSSet.obj V)).homology k) := by
  haveI : Module.Finite ℤ
      ↥((HomologicalComplex.homologyFunctor (ModuleCat ℤ) (ComplexShape.down ℕ) k).obj
        (Work.ThomBordism.singC.obj U)) := h
  have hφ := (HomologicalComplex.homologyFunctor (ModuleCat ℤ) (ComplexShape.down ℕ) k).mapIso
    (Work.ThomBordism.singC.mapIso (TopCat.isoOfHomeo φ))
  exact Module.Finite.of_surjective (Iso.toLinearEquiv hφ).toLinearMap
    (Iso.toLinearEquiv hφ).surjective

/-- **The retraction of a neighbourhood of the image gives finitely generated homology.** -/
theorem homologyFinite_of_enr [T2Space X] [CompactSpace X] {N : ℕ}
    {e : X → EuclideanSpace ℝ (Fin N)} (he : Topology.IsClosedEmbedding e)
    (h : ∃ (U : Set (EuclideanSpace ℝ (Fin N))) (hU : IsOpen U) (hrange : Set.range e ⊆ U),
      ∃ r : ↥U → ↥(Set.range e), Continuous r ∧
        ∀ x : ↥(Set.range e), r ⟨x.1, hrange x.2⟩ = x) (k : ℕ) :
    Module.Finite ℤ ((Work.Cohomology.chainC ℤ (TopCat.toSSet.obj (TopCat.of X))).homology k) := by
  obtain ⟨U, hU, hrange, r, hr, hrf⟩ := h
  haveI : CompactSpace ↥(Set.range e) :=
    isCompact_iff_compactSpace.mp (isCompact_range he.continuous)
  have hK : Module.Finite ℤ
      ((Work.Cohomology.chainC ℤ (TopCat.toSSet.obj (TopCat.of ↥(Set.range e)))).homology k) :=
    Work.ThomBordism.homologyFinite_of_isRetract (Set.range e) U hU hrange r hr hrf
  obtain ⟨φ⟩ := homeo_range_of_isClosedEmbedding (X := X) he
  exact fg_homology_of_homeo φ.symm k hK

end

end Work.ThomBordism.NullBord
