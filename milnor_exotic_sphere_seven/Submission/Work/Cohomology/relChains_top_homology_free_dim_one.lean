import Mathlib
import Submission.Work.Cohomology.HomologyPairSequence
import Submission.Work.Cohomology.diskPairHomologyTopOne
import Submission.Work.Cohomology.homology_zero_free
import Submission.Work.Cohomology.free_submodule_of_free_int

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

open CategoryTheory AlgebraicTopology CategoryTheory.Limits

namespace Work.Cohomology

noncomputable section

/-- The two `ModuleCat ℤ` objects attached to the kernel of a `ℤ`-linear map: the one whose module
structure is the canonical `AddCommGroup.toIntModule` (what typeclass search produces over `ℤ`) and
the one whose module structure is `Submodule.module` (what Mathlib's `ModuleCat.kernelIsoKer` uses,
where the ring is a variable so that only `Submodule.module` applies).  The two `ℤ`-module
structures on an abelian group are equal (`Subsingleton (Module ℤ _)`), whence the isomorphism. -/
lemma moduleCat_of_ker_iso_self {M N : Type*} [AddCommGroup M] [Module ℤ M] [AddCommGroup N]
    [Module ℤ N] (f : M →ₗ[ℤ] N) :
    Nonempty (ModuleCat.of ℤ ↥(LinearMap.ker f) ≅
      @ModuleCat.of ℤ _ ↥(LinearMap.ker f) _ (Submodule.module (LinearMap.ker f))) := by
  have h : (AddCommGroup.toIntModule ↥(LinearMap.ker f))
      = Submodule.module (LinearMap.ker f) := Subsingleton.elim _ _
  rw [h]
  exact ⟨Iso.refl _⟩

/-- **The top relative homology of `(ℝ¹, ℝ¹∖C)` is free, `C` compact** (the `N = 1` case of the
statement that `H_N(ℝ^N, ℝ^N∖C)` is free; `N = 1` is the only case of that statement not yet
proved, the `N ≥ 2` case being reduced to `H_{N-1}(ℝ^N∖C)` and
`Work.Cohomology.euclidean_open_homology_top_free`).

Route (all ingredients are in the workspace and sorry-free):
* `Work.Cohomology.relHomologyOne_iso_kernel` (module
  `Submission/Work/Cohomology/diskPairHomologyTopOne.lean`) gives
  `H_1(ℝ, ℝ∖C) ≅ kernel (H_0(ℝ∖C) → H_0(ℝ))` in `ModuleCat ℤ`, using
  `homologyContractible 1` for `ℝ = EuclideanSpace ℝ (Fin 1)`;
* `Work.Cohomology.homology_zero_free` (module `.../homology_zero_free.lean`) gives that
  `H_0(ℝ∖C; ℤ)` is a free `ℤ`-module;
* `Work.Cohomology.free_submodule_of_free` (module `.../free_homology_iUnion_of_split.lean`) gives
  that the kernel `LinearMap.ker (H_0(ℝ∖C) → H_0(ℝ))` is free, being a subgroup of a free abelian
  group;
* conclude with `ModuleCat.kernelIsoKer` and `Module.Free.of_equiv'`.
Watch out for the `ℤ`-module instance diamond between `Submodule.module` and
`AddCommGroup.toIntModule` (`set_option backward.isDefEq.respectTransparency false`, possibly
`attribute [local instance 5000] Submodule.module`, or an explicit `LinearEquiv` between the two
structures on `⟨LinearMap.ker _⟩`).

The step "a subgroup of a free abelian group is free" is supplied by
`Work.Cohomology.free_submodule_of_free_int` (module `.../free_submodule_of_free_int.lean`, a
self-contained well-ordering argument); the module `.../free_homology_iUnion_of_split.lean`
mentioned above contains a development of the same statement together with an (unrelated) later
section that does not currently compile, so it is not imported here.  The `ℤ`-module instance
diamond is handled by `moduleCat_of_ker_iso_self` below: the two `ModuleCat ℤ` objects attached to
a kernel are isomorphic because the `ℤ`-module structure on an abelian group is unique, so the
kernel of the connecting map can be transported to the `ModuleCat` object produced by
`ModuleCat.kernelIsoKer`. -/
theorem relChains_top_homology_free_dim_one
    (C : Set (EuclideanSpace ℝ (Fin 1))) (hC : IsCompact C) :
    Module.Free ℤ ↥((Work.Cohomology.relChains (TopCat.of (EuclideanSpace ℝ (Fin 1)))
      {y : EuclideanSpace ℝ (Fin 1) | y ∉ C}).homology 1) := by
  -- `ℝ = EuclideanSpace ℝ (Fin 1)` is contractible, so `H₁(ℝ) = 0`; hence the connecting map of
  -- the pair `(ℝ, ℝ∖C)` exhibits `H₁(ℝ, ℝ∖C)` as the kernel of `H₀(ℝ∖C) ⟶ H₀(ℝ)`
  haveI : ContractibleSpace (TopCat.of (EuclideanSpace ℝ (Fin 1))) := inferInstance
  obtain ⟨e⟩ := relHomologyOne_iso_kernel (TopCat.of (EuclideanSpace ℝ (Fin 1)))
    {y : EuclideanSpace ℝ (Fin 1) | y ∉ C} (homologyContractible 1 (by norm_num))
  -- `H₀(ℝ∖C)` is free, being the free abelian group on the path components of `ℝ∖C`
  haveI h0 : Module.Free ℤ ↥((singularChains ℤ
      (TopCat.of ↥{y : EuclideanSpace ℝ (Fin 1) | y ∉ C})).homology 0) := homology_zero_free _
  -- a subgroup of a free abelian group is free, so the kernel of `H₀(ℝ∖C) ⟶ H₀(ℝ)` is free
  have hK : Module.Free ℤ ↥(LinearMap.ker (ModuleCat.Hom.hom
      (HomologicalComplex.homologyMap (inclChains (TopCat.of (EuclideanSpace ℝ (Fin 1)))
        {y : EuclideanSpace ℝ (Fin 1) | y ∉ C}) 0))) :=
    free_submodule_of_free_int _
  -- transport the freeness to the categorical kernel, and then along the isomorphism given by the
  -- long exact sequence of the pair
  obtain ⟨br⟩ := moduleCat_of_ker_iso_self (ModuleCat.Hom.hom
    (HomologicalComplex.homologyMap (inclChains (TopCat.of (EuclideanSpace ℝ (Fin 1)))
      {y : EuclideanSpace ℝ (Fin 1) | y ∉ C}) 0))
  have hker : Module.Free ℤ ↥(kernel (HomologicalComplex.homologyMap
      (inclChains (TopCat.of (EuclideanSpace ℝ (Fin 1)))
        {y : EuclideanSpace ℝ (Fin 1) | y ∉ C}) 0)) :=
    Module.Free.of_equiv' hK (br ≪≫ (ModuleCat.kernelIsoKer (R := ℤ)
      (HomologicalComplex.homologyMap (inclChains (TopCat.of (EuclideanSpace ℝ (Fin 1)))
        {y : EuclideanSpace ℝ (Fin 1) | y ∉ C}) 0)).symm).toLinearEquiv
  exact Module.Free.of_equiv' hker e.toLinearEquiv.symm

end

end Work.Cohomology
