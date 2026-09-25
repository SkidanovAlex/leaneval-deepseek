import Mathlib
import Submission.NK.GlobalCFT.Cohomology
import Submission.NK.GlobalCFT.NormFunctorial
import Submission.NK.GlobalCFT.Inclusion.globalCFT_fixed_idele_mem_range
import Submission.CFTLib.Interfaces

/-!
# The vocabulary of Roquette's idèle computation

This file collects the objects in terms of which the Roquette bound

`rank_p Ĥ⁻¹(Gal(K/F), C_K) ≤ r₁ + r₂ - 1 + δ_p(F) + |T|`

(for `K/F` a finite Galois extension of number fields with `p`-group Galois group, unramified
everywhere) is stated.

* `NK.CFTLib.unitsNormSubgroup` — the norm group `N_{K/F} Kˣ ≤ Fˣ`;
* `NK.CFTLib.normPrincipalPreimage` — the elements of `Fˣ` whose principal idèle is a norm of an
  idèle of `K`, i.e. `Fˣ ∩ N_{K/F} 𝕀_K`;
* `NK.CFTLib.normQuotient` — the quotient `(Fˣ ∩ N_{K/F} 𝕀_K) / N_{K/F} Kˣ`, the concrete
  `ℤ`-module isomorphic to `Ĥ⁻¹(Gal(K/F), C_K)` when `K/F` is unramified;
* `NK.CFTLib.finrank_tensor_zmod_eq_of_linearEquiv` — transporting `𝔽_p`-dimensions of
  `- ⊗[ℤ] ZMod p` along a `ℤ`-linear equivalence.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

open scoped NumberField RestrictedProduct IsMulCommutative
open NumberField IsDedekindDomain
open CategoryTheory

noncomputable section

namespace NK.CFTLib

open NK.GlobalCFT

variable (F K : Type*) [Field F] [NumberField F] [Field K] [NumberField K] [Algebra F K]

/-- The norm group `N_{K/F} Kˣ` of the units, as a subgroup of `Fˣ`. -/
def unitsNormSubgroup : Subgroup Fˣ :=
  MonoidHom.range (Units.map (Algebra.norm F : K →* F))

/-- The elements of `Fˣ` whose principal idèle is a norm of an idèle of `K`; this is
`Fˣ ∩ N_{K/F} 𝕀_K` under the identification of `Fˣ` with the principal idèles of `F`. -/
def normPrincipalPreimage [FiniteDimensional F K] : Subgroup Fˣ :=
  (Idele.normImage F K).comap (Idele.principalIdele F)

/-- The norm group of the units is contained in `Fˣ ∩ N_{K/F} 𝕀_K`. -/
theorem unitsNormSubgroup_le_normPrincipalPreimage [FiniteDimensional F K] :
    unitsNormSubgroup F K ≤ normPrincipalPreimage F K := by
  rintro x ⟨b, rfl⟩
  rw [normPrincipalPreimage, Subgroup.mem_comap, Idele.normImage_eq_map, MonoidHom.mem_range]
  exact ⟨Idele.principalIdele K b, Idele.normIdeleHom_principalIdele b⟩

/-- The concrete `ℤ`-module `(Fˣ ∩ N_{K/F} 𝕀_K) / N_{K/F} Kˣ`.  In the unramified case it is the
model for `Ĥ⁻¹(Gal(K/F), C_K)` (`NK.CFTLib.tateCohomology_neg_one_iso_normQuotient`). -/
abbrev normQuotient [FiniteDimensional F K] : Type _ :=
  Additive (normPrincipalPreimage F K) ⧸
    ((unitsNormSubgroup F K).subgroupOf (normPrincipalPreimage F K)).toAddSubgroup

/-- **Transport of `𝔽_p`-dimensions along a `ℤ`-linear equivalence**: a `ℤ`-linear isomorphism
`M ≃ₗ[ℤ] N` induces a `(ZMod p)`-linear isomorphism `ZMod p ⊗[ℤ] M ≃ₗ[ZMod p] ZMod p ⊗[ℤ] N` and
hence an equality of `Module.finrank`s. -/
theorem finrank_tensor_zmod_eq_of_linearEquiv {M N : Type*} [AddCommGroup M] [Module ℤ M]
    [AddCommGroup N] [Module ℤ N] (e : M ≃ₗ[ℤ] N) (p : ℕ) :
    Module.finrank (ZMod p) (TensorProduct ℤ (ZMod p) M) =
      Module.finrank (ZMod p) (TensorProduct ℤ (ZMod p) N) :=
  LinearEquiv.finrank_eq
    (TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl (ZMod p) (ZMod p)) e)

/-- The idèle group `𝕀_K` as a `ℤ[Gal(K/F)]`-module (the action permutes the components along the
places). -/
def ideleRep : Rep ℤ (K ≃ₐ[F] K) := Rep.ofMulDistribMulAction (K ≃ₐ[F] K) (Idele K)

end NK.CFTLib
