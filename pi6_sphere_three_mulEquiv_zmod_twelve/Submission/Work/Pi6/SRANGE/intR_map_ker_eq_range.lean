import Mathlib
import Submission.Work.Pi6.SRANGE.Defs
set_option backward.isDefEq.respectTransparency false  -- v435port
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

/-!
# Extension of scalars along `ℤ → R` is right exact

Let `q : M →ₗ[ℤ] N` be a surjective `ℤ`-linear map and `k : K →ₗ[ℤ] M` a map whose range is the
kernel of `q`, so that `K --k--> M --q--> N` is exact at `M` with `q` surjective (equivalently, `q`
is the cokernel of `k`).  Then for every commutative ring `R` the sequence obtained by tensoring
with `R` stays exact at the middle term:

`ker (k ⊗ R) = range (f ⊗ R)`, i.e. `LinearMap.ker (q ⊗ R) = LinearMap.range (k ⊗ R)`.

This is right exactness of `- ⊗[ℤ] R`, which holds for *every* coefficient ring `R` (flatness is
not needed: `M ⧸ range k ≅ N`, so tensoring the cokernel description of `q` is enough).

The maps appearing in the statement are the underlying `R`-linear maps of the base change
`(IntR R).map ...`, which is `LinearMap.baseChange ℤ R`; the proof works with the equivalent
description `LinearMap.lTensor (Rmod R)`, for which Mathlib provides right exactness
(`TensorProduct.lTensor_exact`).
-/

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option linter.unusedVariables false

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

namespace Work.Pi6.SRANGE

noncomputable section

-- Make the module structures on submodules and quotients the ones induced from the ambient
-- module, so that the various `Submodule` constructions are `defeq`-compatible.
attribute [local instance 5000] Submodule.module
attribute [local instance 5000] Submodule.Quotient.module

/-- `R` as a `ℤ`-module, in the form used by `ModuleCat.extendScalars` (via `restrictScalars`). -/
abbrev intRKerRmod (R : Type) [CommRing R] : Type :=
  ↥((ModuleCat.restrictScalars (Int.castRingHom R)).obj (ModuleCat.of R R))

/-- The underlying `R`-linear map of the extension of scalars `ℤ → R` applied to a `ℤ`-linear
map: this is `LinearMap.baseChange ℤ R`, written with the module structures used by
`ModuleCat.extendScalars`. -/
def intRKerBcMap (R : Type) [CommRing R] {M N : Type} [AddCommGroup M] [Module ℤ M]
    [AddCommGroup N] [Module ℤ N] (f : M →ₗ[ℤ] N) :
    ↥((IntR R).obj (ModuleCat.of ℤ M)) →ₗ[R] ↥((IntR R).obj (ModuleCat.of ℤ N)) :=
  @LinearMap.baseChange ℤ R M N _ _ ((algebraMap R R).comp (Int.castRingHom R)).toAlgebra
    _ _ _ _ f

/-- On the underlying functions the base change of `f` is `LinearMap.lTensor`. -/
lemma intRKerBcMap_fun_eq_lTensor {R : Type} [CommRing R] {M N : Type} [AddCommGroup M]
    [Module ℤ M] [AddCommGroup N] [Module ℤ N] (f : M →ₗ[ℤ] N) :
    ⇑(intRKerBcMap R f) = ⇑(LinearMap.lTensor (intRKerRmod R) f) := by
  rw [intRKerBcMap]
  exact @LinearMap.baseChange_eq_ltensor ℤ R M N _ _
    ((algebraMap R R).comp (Int.castRingHom R)).toAlgebra _ _ _ _ f

/-- Base change is functorial. -/
lemma intRKerBcMap_comp {R : Type} [CommRing R] {L M N : Type} [AddCommGroup L] [Module ℤ L]
    [AddCommGroup M] [Module ℤ M] [AddCommGroup N] [Module ℤ N]
    (f : L →ₗ[ℤ] M) (g : M →ₗ[ℤ] N) :
    intRKerBcMap R (g.comp f) = (intRKerBcMap R g).comp (intRKerBcMap R f) :=
  @LinearMap.baseChange_comp ℤ R L M N _ _
    ((algebraMap R R).comp (Int.castRingHom R)).toAlgebra _ _ _ _ _ _ f g

/-- Base change preserves surjectivity. -/
lemma intRKerBcMap_surjective {R : Type} [CommRing R] {M N : Type} [AddCommGroup M] [Module ℤ M]
    [AddCommGroup N] [Module ℤ N] (f : M →ₗ[ℤ] N) (hf : Function.Surjective f) :
    Function.Surjective ⇑(intRKerBcMap R f) := by
  have h1 : Function.Surjective ⇑(LinearMap.lTensor (intRKerRmod R) f) :=
    LinearMap.lTensor_surjective (intRKerRmod R) hf
  rwa [← intRKerBcMap_fun_eq_lTensor] at h1

/-- **Extension of scalars along `ℤ → R` is right exact at the middle term.**

If `range k = ker q` and `q` is surjective, then `ker (q ⊗ R) = range (k ⊗ R)`. -/
theorem intR_map_ker_eq_range (R : Type) [CommRing R]
    {M N K : Type} [AddCommGroup M] [Module ℤ M] [AddCommGroup N] [Module ℤ N]
    [AddCommGroup K] [Module ℤ K]
    (q : M →ₗ[ℤ] N) (hq : Function.Surjective q) (k : K →ₗ[ℤ] M)
    (hk : LinearMap.range k = LinearMap.ker q) :
    LinearMap.ker (ModuleCat.Hom.hom ((Work.Pi6.SRANGE.IntR R).map (ModuleCat.ofHom q)))
      = LinearMap.range (ModuleCat.Hom.hom ((Work.Pi6.SRANGE.IntR R).map (ModuleCat.ofHom k))) := by
  change LinearMap.ker (intRKerBcMap R q) = LinearMap.range (intRKerBcMap R k)
  -- Right exactness: the base change of `ker q ↪ M ↠ N` is exact at `R ⊗ M`.
  have hker : LinearMap.ker (intRKerBcMap R q)
      = LinearMap.range (intRKerBcMap R (LinearMap.ker q).subtype) := by
    have h1 : Function.Exact ⇑(intRKerBcMap R (LinearMap.ker q).subtype)
        ⇑(intRKerBcMap R q) := by
      have h := lTensor_exact (intRKerRmod R) (LinearMap.exact_subtype_ker_map q) hq
      rw [intRKerBcMap_fun_eq_lTensor, intRKerBcMap_fun_eq_lTensor]
      exact h
    exact LinearMap.exact_iff.mp h1
  rw [hker]
  -- `k` factors through `ker q`, and the factorisation is surjective because `range k = ker q`.
  have hmem : ∀ a : K, k a ∈ LinearMap.ker q := fun a => by rw [← hk]; exact ⟨a, rfl⟩
  let k' : K →ₗ[ℤ] ↥(LinearMap.ker q) := k.codRestrict (LinearMap.ker q) hmem
  have hsurj' : Function.Surjective ⇑k' := by
    intro y
    obtain ⟨a, ha⟩ := LinearMap.mem_range.mp (by rw [hk]; exact y.2)
    refine ⟨a, Subtype.ext ?_⟩
    show k a = ↑y
    exact ha
  have hfac : k = (LinearMap.ker q).subtype.comp k' :=
    (LinearMap.subtype_comp_codRestrict k (LinearMap.ker q) hmem).symm
  have hrange : LinearMap.range (intRKerBcMap R k)
      = LinearMap.range (intRKerBcMap R (LinearMap.ker q).subtype) := by
    rw [hfac, intRKerBcMap_comp, LinearMap.range_comp,
      LinearMap.range_eq_top.mpr (intRKerBcMap_surjective k' hsurj'), Submodule.map_top]
  rw [hrange]

end

end Work.Pi6.SRANGE
