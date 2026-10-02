import Mathlib
import Submission.Work.Cohomology.cappedPairDefs
import Submission.Work.Cohomology.isIso_homologyMap_tau1
import Submission.Work.Cohomology.collarInclCohomologyIsIso

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The pair map `(Vk(-2), collar) → (Vk(-2), range mkToVkFun(-2))` is a cohomology isomorphism

The relative cochain complex `C^*(X, A)` (`Work.Cohomology.relComplex`) sits in the short exact
sequence of a pair `0 ⟶ C^*(X,A) ⟶ C^*(X) ⟶ C^*(A) ⟶ 0` (`Work.Cohomology.pairShort`,
`pairShort_shortExact`).  A map of pairs therefore induces a morphism of short exact sequences, and
if two of its three components are isomorphisms on homology so is the third
(`Work.Cohomology.isIso_homologyMap_tau1`, the five lemma in the `τ₁` direction).

Here we apply this to the inclusion of pairs `(Vk(-2), range mkToVkFun(-2)) → (Vk(-2), collar)`,
where the map of spaces is the identity:

* on `C^*(X)` the induced map is the identity, hence a homology isomorphism;
* on `C^*(collar)` the induced map is the pullback along the inclusion
  `range mkToVkFun → collar`, which is a homotopy equivalence, hence a homology isomorphism
  (`Work.Cohomology.collarInclCohomologyIsIso`).

Consequently the induced map `H^*(Vk(-2), collar) ⟶ H^*(Vk(-2), range mkToVkFun(-2))` is an
isomorphism in every degree, which is the statement `relComplexMapCollarIsIso`.
-/

set_option backward.isDefEq.respectTransparency false

namespace Work.Cohomology

open CategoryTheory AlgebraicTopology Limits

noncomputable section

/-- The map on relative cochains of a map of pairs is compatible with the inclusion of the relative
cochains into the absolute ones.  (Re-proved here to avoid pulling in the large module
`Submission.Work.Cohomology.capped_rel_cupSquare_ne_zero`.) -/
theorem relComplexMap_comp_relIncl_local {R : Type} [CommRing R] {X₁ X₂ : TopCat} (A₁ : Set X₁)
    (A₂ : Set X₂) (f : X₁ ⟶ X₂) (h : ∀ x ∈ A₁, f x ∈ A₂) :
    Work.Cohomology.relComplexMap R A₁ A₂ f h ≫ Work.Cohomology.relIncl R X₁ A₁ =
      Work.Cohomology.relIncl R X₂ A₂ ≫ Work.Cohomology.dualChainMap R X₁ X₂ f := by
  apply HomologicalComplex.hom_ext
  intro n
  rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f, Work.Cohomology.relComplexMap_f,
    Work.Cohomology.relIncl_f, Work.Cohomology.relIncl_f]
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  exact Work.Cohomology.relMapLM_coe R A₁ A₂ f h n x

/-- The pair map `(Vk(-2), range mkToVkFun(-2)) → (Vk(-2), collar)` induced by the identity is a
homology isomorphism of the relative cochain complexes, for an arbitrary proof that the range of
`mkToVkFun(-2)` lies in the collar. -/
theorem relComplexMapCollarIsIso_aux
    (h : ∀ x ∈ (Set.range (Work.Milnor.mkToVkFun (-2)) : Set (Submission.Milnor.Vk (-2))),
      (CategoryTheory.CategoryStruct.id (TopCat.of (Submission.Milnor.Vk (-2)))) x ∈
        Work.Milnor.collar (-2))
    (n : ℕ) :
    CategoryTheory.IsIso (HomologicalComplex.homologyMap
      (Work.Cohomology.relComplexMap (R := ℤ) (Set.range (Work.Milnor.mkToVkFun (-2)))
        (Work.Milnor.collar (-2))
        (CategoryTheory.CategoryStruct.id (TopCat.of (Submission.Milnor.Vk (-2)))) h) n) := by
  classical
  let X : TopCat := TopCat.of (Submission.Milnor.Vk (-2))
  let A₁ : Set X := Set.range (Work.Milnor.mkToVkFun (-2))
  let A₂ : Set X := Work.Milnor.collar (-2)
  have h' : ∀ x ∈ A₁, (CategoryTheory.CategoryStruct.id X) x ∈ A₂ := h
  -- The morphism of short exact sequences of the pair `(X, A₂) → (X, A₁)`.
  let φ : pairShort ℤ X A₂ ⟶ pairShort ℤ X A₁ :=
    ShortComplex.homMk (relComplexMap ℤ A₁ A₂ (CategoryTheory.CategoryStruct.id X) h')
       (𝟙 (singularCochainComplex ℤ X))
       (dualChainMap ℤ (TopCat.of ↥A₁) (TopCat.of ↥A₂)
          (relMapSub A₁ A₂ (CategoryTheory.CategoryStruct.id X) h'))
       (by
         have hh := relComplexMap_comp_relIncl_local (R := ℤ) A₁ A₂
           (CategoryTheory.CategoryStruct.id X) h'
         rwa [dualChainMap_id] at hh)
       (by
         show (𝟙 (singularCochainComplex ℤ X)) ≫ restr ℤ X A₁
           = restr ℤ X A₂ ≫ dualChainMap ℤ (TopCat.of ↥A₁) (TopCat.of ↥A₂)
               (relMapSub A₁ A₂ (CategoryTheory.CategoryStruct.id X) h')
         rw [Category.id_comp]
         have hh := dualChainMap_restr_comp ℤ A₁ A₂ (CategoryTheory.CategoryStruct.id X) h'
         rwa [dualChainMap_id] at hh)
  -- The component on the absolute cochains of `X` is the identity.
  have h₂ : ∀ k, CategoryTheory.IsIso (HomologicalComplex.homologyMap φ.τ₂ k) := by
    intro k
    have hh : CategoryTheory.IsIso
        (HomologicalComplex.homologyMap (𝟙 (singularCochainComplex ℤ X)) k) := by
      rw [HomologicalComplex.homologyMap_id]
      infer_instance
    exact hh
  -- The component on the cochains of the subspaces is the pullback along a homotopy equivalence.
  have h₃ : ∀ k, CategoryTheory.IsIso (HomologicalComplex.homologyMap φ.τ₃ k) := by
    intro k
    exact collarInclCohomologyIsIso h' k
  -- The five lemma in the `τ₁` direction.
  have hmain := isIso_homologyMap_tau1 ℤ φ (pairShort_shortExact ℤ X A₂)
    (pairShort_shortExact ℤ X A₁) h₂ h₃ n
  exact hmain

/-- **The relative cohomology of `(Vk(-2), collar(-2))` and of `(Vk(-2), range mkToVkFun(-2))`
agree via the pair map induced by the identity.** -/
theorem relComplexMapCollarIsIso (n : ℕ) :
    CategoryTheory.IsIso (HomologicalComplex.homologyMap
      (Work.Cohomology.relComplexMap (R := ℤ) (Set.range (Work.Milnor.mkToVkFun (-2)))
        (Work.Milnor.collar (-2))
        (CategoryTheory.CategoryStruct.id (TopCat.of (Submission.Milnor.Vk (-2))))
        (by
          intro x hx
          obtain ⟨q, rfl⟩ := hx
          exact Work.Milnor.mem_collar.mpr
            (Work.Milnor.one_lt_fibreNorm_mkToVkFun (-2) q))) n) :=
  relComplexMapCollarIsIso_aux (by
      intro x hx
      obtain ⟨q, rfl⟩ := hx
      exact Work.Milnor.mem_collar.mpr (Work.Milnor.one_lt_fibreNorm_mkToVkFun (-2) q)) n

end

end Work.Cohomology
