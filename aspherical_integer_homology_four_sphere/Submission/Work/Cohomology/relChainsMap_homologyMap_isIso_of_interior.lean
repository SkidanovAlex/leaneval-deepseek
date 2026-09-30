import Mathlib
import Submission.Work.Cohomology.localHomology
import Submission.Work.Cohomology.cokerSmallOfU_iso_relChains_compat
import Submission.Work.Cohomology.excisionAux
import Submission.Work.Cohomology.smallChains_homology_iso_int

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# Excision for a cover by interiors

For arbitrary subsets `V, A ⊆ X` whose *interiors* cover `X`,
`interior A ∪ interior V = univ`, the inclusion of pairs `(V, V ∩ A) ⟶ (X, A)` induces an
isomorphism on relative singular homology.  This is the classical excision hypothesis
(`X = int A ∪ int V`); no openness of `V` or `A` themselves is required.

The proof is the same five-lemma comparison as for the open case
(`Work.Cohomology.excision_relChainsMap_isIso`), except that the middle vertical map is the
inclusion `smallToSing A V` of the small chains into the singular chains, which is a
quasi-isomorphism precisely under the interior-cover hypothesis
(`Work.Cohomology.smallChains_homology_iso_int`).
-/

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option linter.style.haveILetI false

open CategoryTheory AlgebraicTopology CategoryTheory.Limits

namespace Work.Cohomology

noncomputable section

theorem relChainsMap_homologyMap_isIso_of_interior (X : TopCat) (V A : Set X)
    (hcov : interior A ∪ interior V = Set.univ) (n : ℕ) :
    CategoryTheory.IsIso
      (HomologicalComplex.homologyMap (Work.Cohomology.relChainsMap X V A) n) := by
  let A' : Set V := {x : V | (x : X) ∈ A}
  let u : singularChains ℤ (TopCat.of A) ⟶ smallChains A V := smallOfU A V
  let w : smallChains A V ⟶ singularChains ℤ X := smallToSing A V
  have huw : u ≫ w = inclChains X A := smallOfU_comp_smallToSing A V
  have huw' : u ≫ w = (𝟙 (singularChains ℤ (TopCat.of A))) ≫ inclChains X A := by
    rw [Category.id_comp]; exact huw
  let S₁ : ShortComplex (ChainComplex (ModuleCat ℤ) ℕ) :=
    ShortComplex.mk u (cokernel.π u) (cokernel.condition u)
  let S₂ : ShortComplex (ChainComplex (ModuleCat ℤ) ℕ) := hPairShort X A
  have hS₁ : S₁.ShortExact :=
    { exact := ShortComplex.exact_cokernel u
      mono_f := mono_smallOfU A V
      epi_g := inferInstance }
  have hS₂ : S₂.ShortExact := hPairShort_shortExact X A
  let τ₃ : S₁.X₃ ⟶ S₂.X₃ := cokernel.map u (inclChains X A) (𝟙 _) w huw'
  have hcomp1 : (𝟙 S₁.X₁) ≫ S₂.f = S₁.f ≫ w := by
    show (𝟙 (singularChains ℤ (TopCat.of A))) ≫ inclChains X A = u ≫ w
    rw [Category.id_comp]; exact huw.symm
  have hcomp2 : w ≫ S₂.g = S₁.g ≫ τ₃ := by
    show w ≫ cokernel.π (inclChains X A)
      = cokernel.π u ≫ cokernel.map u (inclChains X A) (𝟙 _) w huw'
    exact (cokernel_π_map u (inclChains X A) (𝟙 _) w huw').symm
  let φ : S₁ ⟶ S₂ := ShortComplex.homMk (𝟙 S₁.X₁) w τ₃ hcomp1 hcomp2
  have hφ₂ : φ.τ₂ = w := rfl
  have hφ₁ : φ.τ₁ = 𝟙 S₁.X₁ := rfl
  have hτ₃ : IsIso (HomologicalComplex.homologyMap τ₃ n) := by
    refine HomologicalComplex.HomologySequence.isIso_homologyMap_τ₃ φ hS₁ hS₂ n ?_ ?_ ?_ ?_
    · rw [hφ₁, HomologicalComplex.homologyMap_id]; infer_instance
    · rw [hφ₂]; exact smallChains_homology_iso_int A V hcov n
    · intro j _
      rw [hφ₁, HomologicalComplex.homologyMap_id]; infer_instance
    · intro j _
      rw [hφ₂]
      haveI := smallChains_homology_iso_int A V hcov j
      infer_instance
  obtain ⟨e, he⟩ := cokerSmallOfU_iso_relChains_compat X A V
  have key : cokernel.π (smallOfU A V) ≫ τ₃ = w ≫ cokernel.π (inclChains X A) :=
    cokernel_π_map u (inclChains X A) (𝟙 _) w huw'
  have hfac : relChainsMap X V A = e.hom ≫ τ₃ := by
    apply (cancel_epi (cokernel.π (inclChains (TopCat.of V) A'))).1
    calc cokernel.π (inclChains (TopCat.of V) A') ≫ relChainsMap X V A
        = chainMap ℤ (TopCat.of V) X (subtypeIncl X V) ≫ cokernel.π (inclChains X A) :=
          cokernel_π_relChainsMap X V A
      _ = inclChains X V ≫ cokernel.π (inclChains X A) := rfl
      _ = (smallOfV A V ≫ w) ≫ cokernel.π (inclChains X A) := by
            rw [smallOfV_comp_smallToSing]
      _ = smallOfV A V ≫ (w ≫ cokernel.π (inclChains X A)) := Category.assoc _ _ _
      _ = smallOfV A V ≫ (cokernel.π (smallOfU A V) ≫ τ₃) := by rw [key]
      _ = (smallOfV A V ≫ cokernel.π (smallOfU A V)) ≫ τ₃ := (Category.assoc _ _ _).symm
      _ = (cokernel.π (inclChains (TopCat.of V) A') ≫ e.hom) ≫ τ₃ := by rw [he]
      _ = cokernel.π (inclChains (TopCat.of V) A') ≫ (e.hom ≫ τ₃) :=
          Category.assoc _ _ _
  rw [hfac, HomologicalComplex.homologyMap_comp]
  haveI : IsIso (HomologicalComplex.homologyMap e.hom n) :=
    Functor.map_isIso
      (HomologicalComplex.homologyFunctor (ModuleCat ℤ) (ComplexShape.down ℕ) n) e.hom
  exact inferInstance

end

end Work.Cohomology
