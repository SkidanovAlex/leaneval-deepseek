import Mathlib
import Submission.Work.Cohomology.HomologyPairSequence
import Submission.Work.Cohomology.MVSequence
import Submission.Work.Cohomology.smallChains_homology_iso
import Submission.Work.Cohomology.cokerSmallOfU_iso_relChainsCov

/-!
# The two-cover lemma for relative homology

Let `X` be a topological space and `U, V ⊆ X` open subsets with `U ∪ V = X`.  Then the inclusion
of pairs `(U, U ∩ V) → (X, V)` induces an isomorphism on relative singular homology in every
degree:

`H_k(X, V) ≅ H_k(U, U ∩ V)`.

This is the topological heart of the Mayer–Vietoris sequence (equivalently, excision for the
closed set `X ∖ U` excised from `V`).

## Proof

The relative chains `C_*(X, V) = C_*(X)/C_*(V)` are compared with a quotient of the *small*
chains.  Write `Q = coker(smallOfU V U)`, the quotient of the small chains `C^{V,U}_*(X)` by the
image of `C_*(V)`.  The inclusion `smallToSing V U` of the small chains into the singular chains is
a quasi-isomorphism (`smallChains_homology_iso`), and filling in the identity on `C_*(V)` gives a
morphism of short exact sequences

`0 → C_*(V) → C^{V,U}_*(X) → Q → 0`
`0 → C_*(V) → C_*(X) → C_*(X,V) → 0`

from which the five lemma (`HomologicalComplex.HomologySequence.isIso_homologyMap_τ₃`) gives
`H_k(Q) ≅ H_k(X,V)`.  Identifying `Q` with `C_*(U)/C_*(U ∩ V)` — the second isomorphism theorem
applied to the pushout square underlying the Mayer–Vietoris sequence — completes the proof.

## Main results

* `mono_smallOfU`, `smallOfU_comp_smallToSing`, `cokerMap_comp` — basic properties of the
  inclusion `C_*(U) ⟶ C^{U,V}_*(X)` of the chains of `U` into the small chains;
* `isIso_homologyMap_cokerSmallOfU` — the five-lemma comparison `H_k(Q) ≅ H_k(X,V)`;
* `homologyTwoCover` — the two-cover lemma.
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option linter.style.haveILetI false

open CategoryTheory AlgebraicTopology CategoryTheory.Limits

namespace Work.Cohomology

noncomputable section

section Helpers

open scoped Simplicial

variable {X : TopCat}

/-- The naturality of the projection to a cokernel: `cokernel.π f ≫ cokernel.map f f' p q w`
equals `q ≫ cokernel.π f'`. -/
theorem cokernel_π_map' {C : Type*} [Category C] [HasZeroMorphisms C] {X Y X' Y' : C}
    (f : X ⟶ Y) [HasCokernel f] (f' : X' ⟶ Y') [HasCokernel f'] (p : X ⟶ X') (q : Y ⟶ Y')
    (w : f ≫ q = p ≫ f') :
    cokernel.π f ≫ cokernel.map f f' p q w = q ≫ cokernel.π f' := by
  rw [cokernel.map]
  exact cokernel.π_desc _ _ _

/-- The inclusion `C_*(U) ⟶ C^{U,V}_*(X)` of the chains of `U` into the small chains is a
monomorphism. -/
theorem mono_smallOfU (U V : Set X) : Mono (smallOfU U V) := by
  apply HomologicalComplex.mono_of_mono_f
  intro n
  have h : (smallOfU U V).f n
      = coprodMap (R := ℤ) ((smallLiftU U V).app (Opposite.op ⦋n⦌)) := rfl
  rw [h]
  exact mono_coprodMap _ (smallLift_injective U V (Opposite.op ⦋n⦌)).1

/-- The composite of `smallOfU` with the inclusion of the small chains into the singular chains of
`X` is the inclusion of the chains of `U`. -/
theorem smallOfU_comp_smallToSing (U V : Set X) :
    smallOfU U V ≫ smallToSing U V = inclChains X U := by
  have h : SSet.chainComplexMap (smallLiftU U V) (ModuleCat.of ℤ ℤ) ≫
      SSet.chainComplexMap (smallSubcomplex U V).ι (ModuleCat.of ℤ ℤ)
      = SSet.chainComplexMap (TopCat.toSSet.map (inclUX U)) (ModuleCat.of ℤ ℤ) := by
    rw [← Functor.map_comp]
    rw [show smallLiftU U V ≫ (smallSubcomplex U V).ι = TopCat.toSSet.map (inclUX U) from
      SSet.Subcomplex.lift_ι _ _]
  exact h

/-- The composite of `smallOfU` with the inclusion of the small chains into the singular chains of
`X`, in the form required by `cokernel.map`. -/
theorem cokerMap_comp (V U : Set X) :
    smallOfU V U ≫ smallToSing V U = 𝟙 _ ≫ inclChains X V := by
  rw [smallOfU_comp_smallToSing]; simp

/-- **The five-lemma comparison for the two-cover.**  For an open cover `X = U ∪ V`, the map
`coker(smallOfU V U) ⟶ C_*(X,V)` induced by the inclusion of the small chains into the singular
chains of `X` is an isomorphism in homology in every degree. -/
theorem isIso_homologyMap_cokerSmallOfU (U V : Set X) (hU : IsOpen U) (hV : IsOpen V)
    (hcov : U ∪ V = Set.univ) (k : ℕ) :
    IsIso (HomologicalComplex.homologyMap
      (cokernel.map (smallOfU V U) (inclChains X V) (𝟙 _) (smallToSing V U)
        (cokerMap_comp V U)) k) := by
  have hcov' : V ∪ U = Set.univ := by rw [Set.union_comm]; exact hcov
  let S₁ : ShortComplex (ChainComplex (ModuleCat ℤ) ℕ) :=
    ShortComplex.mk (smallOfU V U) (cokernel.π (smallOfU V U)) (cokernel.condition _)
  let S₂ : ShortComplex (ChainComplex (ModuleCat ℤ) ℕ) := hPairShort X V
  have hS₁ : S₁.ShortExact :=
    ShortComplex.ShortExact.mk' (ShortComplex.exact_cokernel (smallOfU V U))
      (mono_smallOfU V U) (inferInstance : Epi (cokernel.π (smallOfU V U)))
  have hS₂ : S₂.ShortExact := hPairShort_shortExact X V
  have hw' : 𝟙 (singularChains ℤ (TopCat.of V)) ≫ S₂.f = S₁.f ≫ smallToSing V U :=
    (cokerMap_comp V U).symm
  let φ : S₁ ⟶ S₂ := ShortComplex.homMk (𝟙 _) (smallToSing V U)
    (cokernel.map (smallOfU V U) (inclChains X V) (𝟙 _) (smallToSing V U)
      (cokerMap_comp V U))
    hw' (cokernel_π_map' (smallOfU V U) (inclChains X V) (𝟙 _) (smallToSing V U)
      (cokerMap_comp V U)).symm
  have hφ1 : φ.τ₁ = 𝟙 (singularChains ℤ (TopCat.of V)) := rfl
  have hφ2 : φ.τ₂ = smallToSing V U := rfl
  have h1 : Epi (HomologicalComplex.homologyMap φ.τ₁ k) := by
    rw [hφ1, HomologicalComplex.homologyMap_id]; infer_instance
  have h2 : IsIso (HomologicalComplex.homologyMap φ.τ₂ k) := by
    rw [hφ2]; exact smallChains_homology_iso V U hV hU hcov' k
  have h3 : ∀ j, (ComplexShape.down ℕ).Rel k j → IsIso (HomologicalComplex.homologyMap φ.τ₁ j) := by
    intro j _; rw [hφ1, HomologicalComplex.homologyMap_id]; infer_instance
  have h4 : ∀ j, (ComplexShape.down ℕ).Rel k j → Mono (HomologicalComplex.homologyMap φ.τ₂ j) := by
    intro j _; rw [hφ2]
    haveI := smallChains_homology_iso V U hV hU hcov' j
    infer_instance
  exact HomologicalComplex.HomologySequence.isIso_homologyMap_τ₃ φ hS₁ hS₂ k h1 h2 h3 h4

end Helpers

theorem homologyTwoCover (X : TopCat) (U V : Set X) (hU : IsOpen U) (hV : IsOpen V)
    (hcov : U ∪ V = Set.univ) (k : ℕ) :
    Nonempty ((relChains X V).homology k ≅
      (relChains (TopCat.of ↥U) {y : ↥U | (y : X) ∈ V}).homology k) := by
  obtain ⟨e⟩ := cokerSmallOfU_iso_relChainsCov X V U
  haveI : IsIso (HomologicalComplex.homologyMap
      (cokernel.map (smallOfU V U) (inclChains X V) (𝟙 _) (smallToSing V U)
        (cokerMap_comp V U)) k) :=
    isIso_homologyMap_cokerSmallOfU U V hU hV hcov k
  exact ⟨(asIso (HomologicalComplex.homologyMap
      (cokernel.map (smallOfU V U) (inclChains X V) (𝟙 _) (smallToSing V U)
        (cokerMap_comp V U)) k)).symm.trans
    ((HomologicalComplex.homologyFunctor (ModuleCat ℤ) (ComplexShape.down ℕ) k).mapIso e)⟩

end

end Work.Cohomology
