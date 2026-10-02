import Mathlib
import Submission.Work.Thom.Cohomology
import Submission.Work.Thom.discThom_iso_openThom
import Submission.Work.Cohomology.Crux.relComplexMap_homologyMap_isIso

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

open CategoryTheory

namespace Work.Thom

/-- **A homotopy equivalence of pairs induces a bijection on relative cohomology.**

If `f : X → Y` is a homotopy equivalence (`e1`) which restricts — up to the identification
`he2` — to a homotopy equivalence `A → B` of the subspaces (`e2`), then the pullback of relative
cohomology `H^n(Y,B;ℤ) → H^n(X,A;ℤ)` is a bijection in every degree.

The proof shows that the map is an isomorphism.  The forward map `f` is the forward map of a
homotopy equivalence, hence induces a quasi-isomorphism on singular chains in every degree
(`Work.Thom.homologyMap_chainMap_isIso_of_homotopyEquiv`), and the same holds for its restriction
to the subspaces: by `he2` the induced map of pairs `relMapSub A B f hf` is the continuous map
`e2.toFun` on the subtypes.  The map of relative cochain complexes induced by a map of pairs whose
two components are quasi-isomorphisms on chains is itself a quasi-isomorphism
(`Work.Thom.relComplexMap_homologyMap_isIso`, by duality and the five lemma), so
`relCohMap f A B hf ℤ n` is an isomorphism of `ℤ`-modules, and an isomorphism of modules is a
bijection. -/
theorem bijective_relCohMap_of_homotopyEquiv {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (A : Set X) (B : Set Y) (f : C(X, Y)) (hf : ∀ x ∈ A, f x ∈ B)
    (e1 : ContinuousMap.HomotopyEquiv X Y) (he1 : ⇑e1.toFun = ⇑f)
    (e2 : ContinuousMap.HomotopyEquiv ↥A ↥B)
    (he2 : ∀ q : ↥A, ((e2.toFun q : ↥B) : Y) = f (q : X)) :
    ∀ n, Function.Bijective (relCohMap f A B hf ℤ n).hom := by
  intro n
  -- `f` is the forward map of the homotopy equivalence `e1`, as a morphism of `TopCat`.
  have hfe : (TopCat.ofHom f : TopCat.of X ⟶ TopCat.of Y) = TopCat.ofHom e1.toFun := by
    ext x
    exact (congrFun he1 x).symm
  -- hence it is a quasi-isomorphism on singular chains.
  have hf' : ∀ k, IsIso (HomologicalComplex.homologyMap
      (Work.Cohomology.chainMap ℤ (TopCat.of X) (TopCat.of Y) (TopCat.ofHom f)) k) := by
    intro k
    rw [hfe]
    exact homologyMap_chainMap_isIso_of_homotopyEquiv e1 k
  -- the induced map of pairs on the subspaces is the continuous map underlying `e2`.
  have hsub : Work.Cohomology.relMapSub A B (TopCat.ofHom f) hf = TopCat.ofHom e2.toFun := by
    ext q
    simp only [Work.Cohomology.relMapSub]
    exact (he2 q).symm
  -- so the restriction to the subspaces is a quasi-isomorphism on singular chains as well.
  have hg' : ∀ k, IsIso (HomologicalComplex.homologyMap
      (Work.Cohomology.chainMap ℤ (TopCat.of ↥A) (TopCat.of ↥B)
        (Work.Cohomology.relMapSub A B (TopCat.ofHom f) hf)) k) := by
    intro k
    rw [hsub]
    exact homologyMap_chainMap_isIso_of_homotopyEquiv e2 k
  -- the map of relative cochain complexes of a pair of quasi-isomorphisms is a quasi-isomorphism,
  -- i.e. the pullback on relative cohomology is an isomorphism.
  have hIso : IsIso (relCohMap f A B hf ℤ n) :=
    relComplexMap_homologyMap_isIso (X₁ := TopCat.of X) (X₂ := TopCat.of Y)
      A B (TopCat.ofHom f) hf hf' hg' n
  exact (ConcreteCategory.isIso_iff_bijective (relCohMap f A B hf ℤ n)).mp hIso

end Work.Thom
