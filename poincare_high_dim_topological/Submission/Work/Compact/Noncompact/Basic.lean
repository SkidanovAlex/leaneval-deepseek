import Mathlib
import Submission.Work.Cohomology.localHomology
import Submission.Work.Cohomology.HomologyPairSequence

/-!
# Relative singular chains: functoriality in the subspace

For a topological space `X` and subsets `A ⊆ B ⊆ X` there is a canonical map of relative chain
complexes `C_*(X,A) ⟶ C_*(X,B)`, induced by the identity on `C_*(X)`.  This file provides it
(`relMap`), its functoriality (`relMap_rfl`, `relMap_comp`) and the induced maps in homology.

`RC X A` is the relative chain complex `C_*(X,A) = C_*(X)/C_*(A)`, written as the explicit cokernel
of `inclChains X A` (it is definitionally equal to `Work.Cohomology.relChains X A`).

The main use is the *localization map*
`H_n(X) = H_n(C_*(X,∅)) ⟶ H_n(X, X∖{x})`
whose vanishing expresses that a homology class is locally trivial at `x`.
-/

set_option maxHeartbeats 800000

open CategoryTheory AlgebraicTopology CategoryTheory.Limits

namespace Work.Compact.Noncompact

noncomputable section

variable {X : TopCat}

/-- The relative chain complex `C_*(X,A)`, as an explicit cokernel. -/
abbrev RC (X : TopCat) (A : Set X) : ChainComplex (ModuleCat ℤ) ℕ :=
  cokernel (Work.Cohomology.inclChains X A)

/-- `RC` agrees definitionally with the relative chains of the cohomology chapter. -/
lemma RC_eq_relChains (X : TopCat) (A : Set X) :
    RC X A = Work.Cohomology.relChains X A := rfl

/-- The inclusion `↥A ⟶ ↥B` of subspaces induced by `A ⊆ B`. -/
def inclSet {A B : Set X} (h : A ⊆ B) : TopCat.of A ⟶ TopCat.of B :=
  TopCat.ofHom ⟨fun a => ⟨a.1, h a.2⟩, Continuous.subtype_mk continuous_subtype_val (fun a => h a.2)⟩

lemma inclSet_comp {A B : Set X} (h : A ⊆ B) :
    inclSet h ≫ Work.Cohomology.subtypeIncl X B = Work.Cohomology.subtypeIncl X A := by
  ext x; rfl

/-- **Functoriality of relative chains in the subspace**: for `A ⊆ B` the identity of `X` induces a
map of relative chain complexes `C_*(X,A) ⟶ C_*(X,B)`. -/
def relMap {A B : Set X} (h : A ⊆ B) : RC X A ⟶ RC X B :=
  cokernel.map (Work.Cohomology.inclChains X A) (Work.Cohomology.inclChains X B)
    (Work.Cohomology.chainMap ℤ (TopCat.of A) (TopCat.of B) (inclSet h))
    (𝟙 (Work.Cohomology.singularChains ℤ X)) (by
      rw [Category.comp_id]
      show Work.Cohomology.chainMap ℤ (TopCat.of A) X (Work.Cohomology.subtypeIncl X A) = _
      rw [show (Work.Cohomology.chainMap ℤ (TopCat.of A) (TopCat.of B) (inclSet h) ≫
          Work.Cohomology.chainMap ℤ (TopCat.of B) X (Work.Cohomology.subtypeIncl X B))
          = Work.Cohomology.chainMap ℤ (TopCat.of A) X
              (inclSet h ≫ Work.Cohomology.subtypeIncl X B) from
        (Functor.map_comp _ _ _).symm]
      rw [inclSet_comp])

/-- Compatibility of `relMap` with the canonical projections. -/
theorem cokernel_π_relMap {A B : Set X} (h : A ⊆ B) :
    cokernel.π (Work.Cohomology.inclChains X A) ≫ relMap h =
      𝟙 (Work.Cohomology.singularChains ℤ X) ≫ cokernel.π (Work.Cohomology.inclChains X B) := by
  rw [relMap]; rw [cokernel.map]; exact cokernel.π_desc _ _ _

@[simp]
lemma relMap_rfl {A : Set X} : relMap (subset_refl A : A ⊆ A) = 𝟙 (RC X A) := by
  refine (cancel_epi (cokernel.π (Work.Cohomology.inclChains X A))).1 ?_
  rw [cokernel_π_relMap, Category.comp_id, Category.id_comp]

lemma relMap_comp {A B C : Set X} (h₁ : A ⊆ B) (h₂ : B ⊆ C) :
    relMap h₁ ≫ relMap h₂ = relMap (h₁.trans h₂) := by
  refine (cancel_epi (cokernel.π (Work.Cohomology.inclChains X A))).1 ?_
  rw [← Category.assoc (cokernel.π _) (relMap h₁) (relMap h₂)]
  rw [cokernel_π_relMap h₁, Category.id_comp, cokernel_π_relMap h₂, Category.id_comp,
    cokernel_π_relMap (h₁.trans h₂), Category.id_comp]

/-- The map on homology `H_n(X, A) ⟶ H_n(X, B)` for `A ⊆ B`. -/
abbrev relMapHom {A B : Set X} (h : A ⊆ B) (n : ℕ) :
    (RC X A).homology n ⟶ (RC X B).homology n :=
  HomologicalComplex.homologyMap (relMap h) n

@[simp]
lemma relMapHom_rfl {A : Set X} (n : ℕ) :
    relMapHom (subset_refl A : A ⊆ A) n = 𝟙 _ := by
  simp [relMapHom]

lemma relMapHom_comp {A B C : Set X} (h₁ : A ⊆ B) (h₂ : B ⊆ C) (n : ℕ) :
    relMapHom h₁ n ≫ relMapHom h₂ n = relMapHom (h₁.trans h₂) n := by
  rw [relMapHom, relMapHom, relMapHom, ← HomologicalComplex.homologyMap_comp, relMap_comp]

/-- The **localization map** at a point `x`: the map `H_n(X) ⟶ H_n(X, X∖{x})`. -/
abbrev localMap (n : ℕ) (x : X) :
    (Work.Cohomology.singularChains ℤ X).homology n ⟶ (RC X ({x}ᶜ : Set X)).homology n :=
  HomologicalComplex.homologyMap (cokernel.π (Work.Cohomology.inclChains X ∅)) n ≫
    relMapHom (Set.empty_subset _) n

end

end Work.Compact.Noncompact
