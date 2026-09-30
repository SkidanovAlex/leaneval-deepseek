import Mathlib
import Submission.Work.SSSR.Serre.E2dEngine
set_option backward.isDefEq.respectTransparency false  -- v435port
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

open Work.Serre
variable {R : Type} [CommRing R] [Nontrivial R]

open CategoryTheory CategoryTheory.Limits
namespace Work.SSSR.Serre

noncomputable section

/-- **The inclusion of a subspace whose relative homology vanishes is a homology isomorphism.** -/
theorem isIso_inclChains_homologyMap_of_isZero_relChains {Y : TopCat} (F : Set Y)
    (hF : ∀ m, IsZero ((Work.SSSR.Cohomology.relChains R Y F).homology m)) (k : ℕ) :
    IsIso (HomologicalComplex.homologyMap (Work.SSSR.Cohomology.inclChains R Y F) k) := by
  have hmono : Mono (HomologicalComplex.homologyMap (Work.SSSR.Cohomology.inclChains R Y F) k) := by
    have hf0 : ModuleCat.Hom.hom (Work.SSSR.Cohomology.hPairδ (R := R) Y F k) = 0 := by
      rw [IsZero.eq_zero_of_src (hF (k + 1)) (Work.SSSR.Cohomology.hPairδ (R := R) Y F k)]
      exact ModuleCat.hom_zero
    have hex1 := Work.SSSR.Cohomology.hPair_exact₁ (R := R) Y F k
    have hker : LinearMap.ker (ModuleCat.Hom.hom
        (HomologicalComplex.homologyMap (Work.SSSR.Cohomology.inclChains R Y F) k)) = ⊥ := by
      rw [← ShortComplex.Exact.moduleCat_range_eq_ker hex1, hf0, LinearMap.range_zero]
    rw [ModuleCat.mono_iff_injective]
    exact LinearMap.ker_eq_bot.mp hker
  have hepi : Epi (HomologicalComplex.homologyMap (Work.SSSR.Cohomology.inclChains R Y F) k) := by
    have hg0 : ModuleCat.Hom.hom (HomologicalComplex.homologyMap
        (cokernel.π (Work.SSSR.Cohomology.inclChains R Y F)) k) = 0 := by
      rw [IsZero.eq_zero_of_tgt (hF k)
        (HomologicalComplex.homologyMap (cokernel.π (Work.SSSR.Cohomology.inclChains R Y F)) k)]
      exact ModuleCat.hom_zero
    have hex2 := Work.SSSR.Cohomology.hPair_exact₂ (R := R) Y F k
    have hrange : LinearMap.range (ModuleCat.Hom.hom
        (HomologicalComplex.homologyMap (Work.SSSR.Cohomology.inclChains R Y F) k)) = ⊤ := by
      rw [ShortComplex.Exact.moduleCat_range_eq_ker hex2, hg0, LinearMap.ker_zero]
    rw [ModuleCat.epi_iff_surjective]
    intro y
    exact LinearMap.mem_range.mp (by rw [hrange]; exact Submodule.mem_top)
  exact isIso_of_mono_of_epi _

end

end Work.SSSR.Serre
