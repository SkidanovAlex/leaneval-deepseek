import Mathlib
import Submission.Work.Cohomology.DiskPairBasic
import Submission.Work.Cohomology.HomologyPairSequence
import Submission.Work.Cohomology.homologyContractible
import Submission.Work.Cohomology.epsilonNaturality
import Submission.Work.Cohomology.reducedH0SphereInUnitOne

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# The top relative homology of the pair `(D¹, S⁰)`

The relative homology of the pair `(D¹, S⁰)` in degree `1` is `ℤ`: the `1`-dimensional instance of
the classical computation `Hₙ(Dⁿ, Sⁿ⁻¹) ≅ ℤ`.

The proof runs the long exact sequence of the pair (`Work.Cohomology.hPair_exact₁`,
`Work.Cohomology.hPair_exact₃`)

`H₁(D¹) ⟶ H₁(D¹, S⁰) --δ--> H₀(S⁰) --i--> H₀(D¹)`,

in which the first term vanishes (`Work.Cohomology.homologyContractible`, as `D¹` is contractible),
so that `δ` exhibits `H₁(D¹, S⁰)` as the kernel of the map `i` on `H₀`.  The naturality of the
augmentation (`Work.Cohomology.epsilonNaturality`) identifies `i` with `ε(S⁰) ≫ ε(D¹)⁻¹`, so its
kernel is the kernel of the augmentation of `S⁰`, i.e. the reduced zeroth homology of `S⁰`, which
is `ℤ` (`Work.Cohomology.reducedH0SphereInUnitOne`).
-/

set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

open CategoryTheory AlgebraicTopology CategoryTheory.Limits

namespace Work.Cohomology

noncomputable section

/-- The `ModuleCat` object attached to a submodule `K`, with the module structure inherited from
`K` (the spelling used by Mathlib's `ModuleCat.kernelIsoKer`). -/
abbrev ofSubmodule {R : Type*} [Ring R] {M : Type*} [AddCommGroup M] [Module R M]
    (K : Submodule R M) : ModuleCat R :=
  ModuleCat.of R ↥K

/-- The two spellings `ofSubmodule K` and `ModuleCat.of ℤ ↥K` of the `ModuleCat` object attached to
a submodule of a `ℤ`-module coincide, because all `ℤ`-module structures on a fixed abelian group
are equal (`AddCommMonoid.subsingletonIntModule`). -/
lemma ofSubmodule_eq {M : Type*} [AddCommGroup M] [Module ℤ M] (K : Submodule ℤ M) :
    ofSubmodule K = ModuleCat.of ℤ ↥K := by
  rw [ofSubmodule]
  exact congrArg (fun m => @ModuleCat.of ℤ _ ↥K _ m) (Subsingleton.elim _ _)

/-- The isomorphism between the two spellings of the object attached to a submodule. -/
def ofSubmodule_iso {M : Type*} [AddCommGroup M] [Module ℤ M] (K : Submodule ℤ M) :
    ofSubmodule K ≅ ModuleCat.of ℤ ↥K :=
  eqToIso (ofSubmodule_eq K)

/-- **The connecting map of the pair `(X, A)` exhibits `H₁(X,A)` as the kernel of the map induced
by the inclusion on `H₀`**, provided the degree-`1` homology of `X` vanishes. -/
theorem relHomologyOne_iso_kernel (X : TopCat) (A : Set X)
    (h1 : IsZero ((singularChains ℤ X).homology 1)) :
    Nonempty ((relChains X A).homology 1 ≅ kernel (HomologicalComplex.homologyMap
      (inclChains X A) 0)) := by
  -- the pair sequence is exact at `H₁(X,A)` and at `H₀(A)`
  have hrange : (ModuleCat.Hom.hom (hPairδ X A 0)).range =
      (ModuleCat.Hom.hom (HomologicalComplex.homologyMap (inclChains X A) 0)).ker :=
    ShortComplex.Exact.moduleCat_range_eq_ker (hPair_exact₁ X A 0)
  have hex : Function.Exact (ModuleCat.Hom.hom (hPairδ X A 0))
      (ModuleCat.Hom.hom (HomologicalComplex.homologyMap (inclChains X A) 0)) :=
    LinearMap.exact_iff.mpr hrange.symm
  -- the connecting map is injective because `H₁(X) = 0`
  have hf : (ShortComplex.mk
      (HomologicalComplex.homologyMap (cokernel.π (inclChains X A)) 1)
      (hPairδ X A 0) (hPair_comp_δ X A 0)).f = 0 := h1.eq_of_src _ 0
  have hmono : Mono (hPairδ X A 0) :=
    (ShortComplex.exact_iff_mono _ hf).1 (hPair_exact₃ X A 0)
  have hinj : Function.Injective (ModuleCat.Hom.hom (hPairδ X A 0)) :=
    (ModuleCat.mono_iff_injective _).mp hmono
  -- so `δ` itself is a kernel of the map `H₀(A) ⟶ H₀(X)`, and `kernel` is unique up to iso
  exact ⟨IsLimit.conePointUniqueUpToIso
    (ModuleCat.isLimitKernelFork (hPairδ X A 0)
      (HomologicalComplex.homologyMap (inclChains X A) 0) hex hinj) (limit.isLimit _)⟩

/-- The augmentation `H₀(S⁰) ⟶ ℤ` of `S⁰ = sphereInUnit 1`. -/
abbrev epsSphereInUnitOne : ((singularChains ℤ (TopCat.of (sphereInUnit 1))).homology 0) ⟶
    ModuleCat.of ℤ ℤ :=
  TopCat.singularHomology₀ε (TopCat.of (sphereInUnit 1)) (ModuleCat.of ℤ ℤ)

/-- The augmentation `H₀(D¹) ⟶ ℤ` of `D¹ = diskUnit 1`. -/
abbrev epsDiskUnitOne : ((singularChains ℤ (diskUnit 1)).homology 0) ⟶
    ModuleCat.of ℤ ℤ :=
  TopCat.singularHomology₀ε (diskUnit 1) (ModuleCat.of ℤ ℤ)

/-- The degree-`0` map induced by the inclusion `S⁰ ⊆ D¹` is the augmentation of `S⁰` followed by
the inverse of the augmentation of `D¹`.  This is the naturality of the augmentation. -/
lemma inclChains_zero_eq (h : IsIso epsDiskUnitOne) :
    HomologicalComplex.homologyMap (inclChains (diskUnit 1) (sphereInUnit 1)) 0 =
      epsSphereInUnitOne ≫ inv epsDiskUnitOne := by
  have hnat : HomologicalComplex.homologyMap
      (inclChains (diskUnit 1) (sphereInUnit 1)) 0 ≫ epsDiskUnitOne = epsSphereInUnitOne :=
    epsilonNaturality _ _ (subtypeIncl _ _)
  rw [← hnat, Category.assoc, IsIso.hom_inv_id, Category.comp_id]

/-- `D¹` is contractible (it is a nonempty convex subset of `ℝ¹`). -/
theorem diskUnitOne_contractible : ContractibleSpace (diskUnit 1) :=
  Convex.contractibleSpace (convex_closedBall 0 1) ⟨0, by simp [Metric.mem_closedBall]⟩

theorem diskPairHomologyTopOne :
    Nonempty
      ((Work.Cohomology.relChains (Work.Cohomology.diskUnit 1)
        (Work.Cohomology.sphereInUnit 1)).homology 1 ≅ ModuleCat.of ℤ ℤ) := by
  -- the reduced zeroth homology of `S⁰` is `ℤ`
  obtain ⟨e4⟩ := reducedH0SphereInUnitOne
  haveI hc : ContractibleSpace (diskUnit 1) := diskUnitOne_contractible
  have hz : IsZero ((singularChains ℤ (diskUnit 1)).homology 1) :=
    homologyContractible 1 (by norm_num)
  -- `H₁(D¹,S⁰)` is the kernel of the map `H₀(S⁰) ⟶ H₀(D¹)` induced by the inclusion
  obtain ⟨e1⟩ := relHomologyOne_iso_kernel (diskUnit 1) (sphereInUnit 1) hz
  -- that map is `ε(S⁰) ≫ ε(D¹)⁻¹`, so its kernel is the kernel of the augmentation of `S⁰`
  haveI : IsIso epsDiskUnitOne := inferInstance
  have hcomp : HomologicalComplex.homologyMap (inclChains (diskUnit 1) (sphereInUnit 1)) 0 ≫
      epsDiskUnitOne = epsSphereInUnitOne :=
    epsilonNaturality _ _ (subtypeIncl _ _)
  have e2 : kernel (HomologicalComplex.homologyMap (inclChains (diskUnit 1) (sphereInUnit 1)) 0) ≅
      kernel epsSphereInUnitOne :=
    (IsLimit.conePointUniqueUpToIso
      (kernel.ofCompIso (f := epsSphereInUnitOne)
        (HomologicalComplex.homologyMap (inclChains (diskUnit 1) (sphereInUnit 1)) 0)
        (asIso epsDiskUnitOne) hcomp) (limit.isLimit _)).symm
  exact ⟨e1 ≪≫ e2 ≪≫ ModuleCat.kernelIsoKer epsSphereInUnitOne ≪≫
    ofSubmodule_iso (ModuleCat.Hom.hom epsSphereInUnitOne).ker ≪≫ e4⟩

end

end Work.Cohomology
