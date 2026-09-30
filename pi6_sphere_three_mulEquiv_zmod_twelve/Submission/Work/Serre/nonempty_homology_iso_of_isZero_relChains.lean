import Mathlib
import Submission.Work.Serre.E2dEngine

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# Comparing the homology of two subspaces through the long exact sequence of a pair

If the relative homology `H_m(Y, F)` vanishes in every degree `m`, then the inclusion
`F ↪ Y` induces an isomorphism on homology in every degree: the long exact sequence of the pair
(`Work.Cohomology.hPair_exact₁`, `Work.Cohomology.hPair_exact₂`) exhibits the map
`H_k(F) → H_k(Y)` as injective (the source of the connecting map is `H_{k+1}(Y,F) = 0`) and
surjective (`H_k(Y,F) = 0`).

Consequently, two subspaces `F`, `F'` whose pairs with `Y` have vanishing relative homology have
isomorphic homology.
-/

open CategoryTheory CategoryTheory.Limits

namespace Work.Serre

noncomputable section

/-- **The inclusion of a subspace whose relative homology vanishes is a homology isomorphism.** -/
theorem isIso_inclChains_homologyMap_of_isZero_relChains {Y : TopCat} (F : Set Y)
    (hF : ∀ m, IsZero ((Work.Cohomology.relChains Y F).homology m)) (k : ℕ) :
    IsIso (HomologicalComplex.homologyMap (Work.Cohomology.inclChains Y F) k) := by
  have hmono : Mono (HomologicalComplex.homologyMap (Work.Cohomology.inclChains Y F) k) := by
    have hf0 : ModuleCat.Hom.hom (Work.Cohomology.hPairδ Y F k) = 0 := by
      rw [IsZero.eq_zero_of_src (hF (k + 1)) (Work.Cohomology.hPairδ Y F k)]
      exact ModuleCat.hom_zero
    have hex1 := Work.Cohomology.hPair_exact₁ Y F k
    have hker : LinearMap.ker (ModuleCat.Hom.hom
        (HomologicalComplex.homologyMap (Work.Cohomology.inclChains Y F) k)) = ⊥ := by
      rw [← ShortComplex.Exact.moduleCat_range_eq_ker hex1, hf0, LinearMap.range_zero]
    rw [ModuleCat.mono_iff_injective]
    exact LinearMap.ker_eq_bot.mp hker
  have hepi : Epi (HomologicalComplex.homologyMap (Work.Cohomology.inclChains Y F) k) := by
    have hg0 : ModuleCat.Hom.hom (HomologicalComplex.homologyMap
        (cokernel.π (Work.Cohomology.inclChains Y F)) k) = 0 := by
      rw [IsZero.eq_zero_of_tgt (hF k)
        (HomologicalComplex.homologyMap (cokernel.π (Work.Cohomology.inclChains Y F)) k)]
      exact ModuleCat.hom_zero
    have hex2 := Work.Cohomology.hPair_exact₂ Y F k
    have hrange : LinearMap.range (ModuleCat.Hom.hom
        (HomologicalComplex.homologyMap (Work.Cohomology.inclChains Y F) k)) = ⊤ := by
      rw [ShortComplex.Exact.moduleCat_range_eq_ker hex2, hg0, LinearMap.ker_zero]
    rw [ModuleCat.epi_iff_surjective]
    intro y
    exact LinearMap.mem_range.mp (by rw [hrange]; exact Submodule.mem_top)
  exact isIso_of_mono_of_epi _

/-- **Two subspaces whose pairs with `Y` have vanishing relative homology have isomorphic
homology.** -/
theorem nonempty_homology_iso_of_isZero_relChains {Y : TopCat} (F F' : Set Y)
    (hF : ∀ m, IsZero ((Work.Cohomology.relChains Y F).homology m))
    (hF' : ∀ m, IsZero ((Work.Cohomology.relChains Y F').homology m)) (k : ℕ) :
    Nonempty (((Work.Cohomology.singularChains ℤ (TopCat.of ↥F)).homology k) ≅
      ((Work.Cohomology.singularChains ℤ (TopCat.of ↥F')).homology k)) := by
  haveI h1 := isIso_inclChains_homologyMap_of_isZero_relChains F hF k
  haveI h2 := isIso_inclChains_homologyMap_of_isZero_relChains F' hF' k
  exact ⟨(asIso (HomologicalComplex.homologyMap (Work.Cohomology.inclChains Y F) k)) ≪≫
    (asIso (HomologicalComplex.homologyMap (Work.Cohomology.inclChains Y F') k)).symm⟩

end

end Work.Serre
