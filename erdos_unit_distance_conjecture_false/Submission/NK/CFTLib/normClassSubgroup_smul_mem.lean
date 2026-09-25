/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import Submission.NK.CFTLib.inclusion_smul_of_tower
import Submission.NK.HassePrinciple.ideleInclusion_smul_of_restrict
import Submission.NK.GlobalCFT.NormGroup.globalCFT_normClassHom_trans
import Submission.NK.GlobalCFT.H0Computation

/-!
# The norm subgroup `N_{L/M} C_L` is stable under `Gal(M/K)`

For a tower `K ⊆ M ⊆ L` of number fields with `M/K`, `L/M` and `L/K` all Galois, the norm
subgroup `N_{L/M} C_L ≤ C_M` is stable under the action of `Gal(M/K)` on the idèle class group
`C_M`:

  `q ∈ N_{L/M} C_L  ⟹  σ • q ∈ N_{L/M} C_L     (σ : Gal(M/K))`.

This is the statement a colleague needs for the paper's proof (Neukirch–Uchida); the classical
content is the **equivariance of the norm** in a Galois tower.

## Route

`Gal(M/K)` is the quotient of `Gal(L/K)` by the (normal, since `M/K` is Galois) subgroup
`Gal(L/M)`, so every `σ : Gal(M/K)` admits a lift `γ : Gal(L/K)`
(`AlgEquiv.restrictNormalHom_surjective`, using `Normal K M` and `Normal K L`).  The main
ingredients are

* the action of `Gal(L/M)` on `C_L` agrees with the action of the underlying `K`-automorphisms
  (`AlgEquiv.restrictScalars K`): `smul_restrictScalars_ideleClassGroup`;
* **the equivariance of the idèle inclusion** `ψ : C_M →* C_L`
  (`HassePrinciple.ideleInclusion_smul_of_restrict`, giving `ψ (σ • q) = γ • ψ q` when
  `σ = γ|_M`);
* **the `H⁰`-computation** `ψ (N_{L/M} z) = ∏_{τ : Gal(L/M)} τ • z`
  (`GlobalCFT.globalCFT_normClassHom_eq_prod_smul`), and injectivity of `ψ`.

Writing both sides of `N_{L/M} (γ • z) = σ • N_{L/M} z` as products over `Gal(L/M)`, the two
products are

  `∏_{τ} (γ τ) • z`   and   `∏_{τ} τ • (γ • z)`,

i.e. products over the same *coset* `γ · Gal(L/M) = Gal(L/M) · γ`, their equality being exactly
the normality of `Gal(L/M) ◁ Gal(L/K)`.  Formally this reindexing is implemented by the
conjugation permutation `galConjEquiv γ : Gal(L/M) ≃ Gal(L/M)`,
`τ ↦ γ τ γ⁻¹` (well defined by normality) with `Fintype.prod_equiv`.

## Main results

* `NK.CFTLib.galConj` / `galConjEquiv`: the conjugation action of `Gal(L/K)` on `Gal(L/M)`;
* `NK.CFTLib.normClassHom_smul_of_restrict`: **`N_{L/M} (γ • q) = (γ|_M) • N_{L/M} q`**;
* `NK.CFTLib.normClassSubgroup_smul_mem`: the requested stability of the norm subgroup.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

open scoped NumberField RestrictedProduct
open NumberField IsDedekindDomain

noncomputable section

namespace NK.CFTLib

open NK.GlobalCFT

section Aux

variable {K M L : Type} [Field K] [NumberField K] [Field M] [NumberField M] [Field L]
  [NumberField L] [Algebra K M] [Algebra M L] [Algebra K L] [IsScalarTower K M L]
  [FiniteDimensional K M] [FiniteDimensional M L] [FiniteDimensional K L]
  [IsGalois K M] [IsGalois M L] [IsGalois K L]

/-! ### The conjugation action of `Gal(L/K)` on `Gal(L/M)` -/

/-- **Conjugation by `γ : Gal(L/K)` on `Gal(L/M)`.**  For `x ∈ Gal(L/M)` the `K`-automorphism
`γ x γ⁻¹` of `L` fixes `M` pointwise — because `M/K` is normal, `Gal(L/M) = ker (·|_M)` is normal
in `Gal(L/K)` — hence it is an element of `Gal(L/M)`. -/
noncomputable def galConj (γ : L ≃ₐ[K] L) (x : L ≃ₐ[M] L) : L ≃ₐ[M] L :=
  AlgEquiv.ofBijective
    ({ (γ * x.restrictScalars K * γ⁻¹).toRingEquiv.toRingHom with
        commutes' := fun m => by
          have h : (γ * x.restrictScalars K * γ⁻¹).restrictNormal M = 1 := by
            rw [← show AlgEquiv.restrictNormalHom M (γ * x.restrictScalars K * γ⁻¹) =
              (γ * x.restrictScalars K * γ⁻¹).restrictNormal M from rfl]
            rw [map_mul, map_mul, map_inv]
            have hx1 : AlgEquiv.restrictNormalHom M (x.restrictScalars K) = 1 := by
              rw [show AlgEquiv.restrictNormalHom M (x.restrictScalars K) =
                (x.restrictScalars K).restrictNormal M from rfl]
              ext m
              rw [AlgEquiv.one_apply]
              apply (algebraMap M L).injective
              rw [AlgEquiv.restrictNormal_commutes]
              exact x.commutes m
            rw [hx1, mul_one]
            exact mul_inv_cancel _
          have h2 := AlgEquiv.restrictNormal_commutes (χ := γ * x.restrictScalars K * γ⁻¹)
            (E := M) m
          rw [h, AlgEquiv.one_apply] at h2
          exact h2.symm } : L →ₐ[M] L)
    (AlgHom.normal_bijective M L L _)

/-- The underlying `K`-automorphism of a conjugate is the conjugate. -/
theorem galConj_restrictScalars (γ : L ≃ₐ[K] L) (x : L ≃ₐ[M] L) :
    (galConj γ x).restrictScalars K = γ * x.restrictScalars K * γ⁻¹ := by
  ext y
  rfl

/-- Conjugating by `γ` and then by `γ⁻¹` is the identity. -/
theorem galConj_comp (γ : L ≃ₐ[K] L) (x : L ≃ₐ[M] L) :
    galConj γ⁻¹ (galConj γ x) = x := by
  have hinj : Function.Injective (AlgEquiv.restrictScalars (R := K) (S := M) :
      (L ≃ₐ[M] L) → (L ≃ₐ[K] L)) := by
    intro a b hab
    ext y
    exact congrArg (fun (e : L ≃ₐ[K] L) => e y) hab
  apply hinj
  rw [galConj_restrictScalars γ⁻¹ (galConj γ x), galConj_restrictScalars γ x]
  group

/-- **Conjugation as a permutation of `Gal(L/M)`**: the composite of `galConj` with its inverse
is the identity. -/
noncomputable def galConjEquiv (γ : L ≃ₐ[K] L) : (L ≃ₐ[M] L) ≃ (L ≃ₐ[M] L) where
  toFun := galConj γ
  invFun := galConj γ⁻¹
  left_inv x := galConj_comp γ x
  right_inv x := galConj_comp γ⁻¹ x

/-! ### The two actions of `Gal(L/M)` and of `Gal(L/K)` on `C_L` -/

/-- The action of `Gal(L/M)` on the idèle class group of `L` agrees with the action of the
underlying `K`-algebra automorphisms (`AlgEquiv.restrictScalars K`). -/
theorem smul_restrictScalars_ideleClassGroup (h : L ≃ₐ[M] L) (q : IdeleClassGroup L) :
    h • q = (h.restrictScalars K) • q := by
  obtain ⟨x, rfl⟩ := IdeleClassGroup.mk_surjective L q
  rw [IdeleClassGroup.smul_mk, IdeleClassGroup.smul_mk]
  congr 1

/-- **The conjugation identity on the level of the action**: for `γ : Gal(L/K)`, `x : Gal(L/M)`
and `q ∈ C_L` one has `γ • (x • q) = (γ x γ⁻¹) • (γ • q)`. -/
theorem galConj_smul_smul (γ : L ≃ₐ[K] L) (x : L ≃ₐ[M] L) (q : IdeleClassGroup L) :
    γ • (x • q) = galConj γ x • (γ • q) := by
  rw [smul_restrictScalars_ideleClassGroup (K := K) x q]
  conv_rhs => rw [smul_restrictScalars_ideleClassGroup (K := K) (galConj γ x) (γ • q)]
  rw [← mul_smul, ← mul_smul, galConj_restrictScalars]
  group

/-! ### Equivariance of the norm in a Galois tower -/

/-- **Equivariance of the idèle-class-group norm in a Galois tower.**  For a tower `K ⊆ M ⊆ L`
of number fields with `M/K` normal and `L/M`, `L/K` Galois, and for `γ : Gal(L/K)` one has

  `N_{L/M} (γ • q) = (γ|_M) • N_{L/M} q    (q ∈ C_L)`

where `γ|_M : Gal(M/K)` is the restriction of `γ` to `M`.

The proof compares the two sides after applying the idèle inclusion `ψ : C_M →* C_L` (which is
injective, and satisfies `ψ (N_{L/M} z) = ∏_{τ : Gal(L/M)} τ • z` and `ψ (σ • q) = γ • ψ q` when
`σ = γ|_M`): the two products over `Gal(L/M)` are reindexed by conjugation `τ ↦ γ τ γ⁻¹`, which
is the normality of `Gal(L/M) ◁ Gal(L/K)`. -/
theorem normClassHom_smul_of_restrict (γ : L ≃ₐ[K] L) (q : IdeleClassGroup L) :
    IdeleClassGroup.normClassHom M L (γ • q) =
      (AlgEquiv.restrictNormalHom M γ) • IdeleClassGroup.normClassHom M L q := by
  haveI hN : Normal K M := IsGalois.to_normal
  haveI hNML : Normal M L := IsGalois.to_normal
  classical
  obtain ⟨u, hu⟩ : ∃ u : Place L → Place M, ∀ w, Place.LiesOver w (u w) :=
    ⟨fun w => Classical.choose (Inclusion.globalCFT_exists_placeUnder (K := M) (L := L) w),
     fun w => Classical.choose_spec
       (Inclusion.globalCFT_exists_placeUnder (K := M) (L := L) w)⟩
  obtain ⟨φ, hφ⟩ := Inclusion.globalCFT_ideleInclusion_exists (K := M) (L := L) u hu
  obtain ⟨ψ, hψ⟩ :=
    Inclusion.globalCFT_ideleClassGroup_inclusion_exists (K := M) (L := L) u hu φ hφ
  have hψinj : Function.Injective ψ :=
    Inclusion.globalCFT_ideleClassGroup_inclusion_injective u hu φ hφ ψ hψ
  have hψnorm : ∀ z : IdeleClassGroup L,
      ψ (IdeleClassGroup.normClassHom M L z) = ∏ σ : L ≃ₐ[M] L, σ • z :=
    fun z => globalCFT_normClassHom_eq_prod_smul u hu φ hφ ψ hψ z
  have hψsmul : ∀ (σ : L ≃ₐ[K] L) (z : IdeleClassGroup M),
      ψ (AlgEquiv.restrictNormalHom M σ • z) = σ • ψ z := by
    intro σ z
    obtain ⟨x, rfl⟩ := IdeleClassGroup.mk_surjective M z
    rw [IdeleClassGroup.smul_mk, hψ ((AlgEquiv.restrictNormalHom M σ) • x), hψ x,
      IdeleClassGroup.smul_mk,
      NK.HassePrinciple.ideleInclusion_smul_of_restrict u hu φ hφ σ x]
  apply hψinj
  rw [hψnorm (γ • q), hψsmul γ (IdeleClassGroup.normClassHom M L q), hψnorm q,
    Finset.smul_prod']
  exact (Fintype.prod_equiv (galConjEquiv (K := K) γ) (fun σ => γ • (σ • q))
    (fun τ => τ • (γ • q)) (fun σ => galConj_smul_smul (K := K) γ σ q)).symm

end Aux

theorem normClassSubgroup_smul_mem {K M L : Type} [Field K] [NumberField K] [Field M] [NumberField M] [Field L] [NumberField L] [Algebra K M] [Algebra M L] [Algebra K L] [IsScalarTower K M L] [FiniteDimensional K M] [FiniteDimensional M L] [FiniteDimensional K L] [IsGalois K M] [IsGalois M L] [IsGalois K L] : ∀ (σ : Gal(M/K)) (q : NK.GlobalCFT.IdeleClassGroup M), q ∈ NK.GlobalCFT.Idele.normClassSubgroup M L → σ • q ∈ NK.GlobalCFT.Idele.normClassSubgroup M L := by
  haveI hN : Normal K M := IsGalois.to_normal
  intro σ q hq
  obtain ⟨y, rfl⟩ := Idele.mem_normClassSubgroup.mp hq
  -- lift `σ : Gal(M/K)` to `γ : Gal(L/K)`
  obtain ⟨γ, hγ⟩ := AlgEquiv.restrictNormalHom_surjective (F := K) (K₁ := M) L σ
  have hkey : σ • IdeleClassGroup.normClassHom M L y =
      IdeleClassGroup.normClassHom M L (γ • y) := by
    rw [← hγ]
    exact (normClassHom_smul_of_restrict (K := K) γ y).symm
  rw [hkey]
  exact Idele.mem_normClassSubgroup.mpr ⟨γ • y, rfl⟩

section Corollary

variable {K M L : Type} [Field K] [NumberField K] [Field M] [NumberField M] [Field L]
  [NumberField L] [Algebra K M] [Algebra M L] [Algebra K L] [IsScalarTower K M L]
  [FiniteDimensional K M] [FiniteDimensional M L] [FiniteDimensional K L]
  [IsGalois K M] [IsGalois M L] [IsGalois K L]

/-- **The norm subgroup is stable under `Gal(M/K)`**, at the level of subgroups. -/
theorem normClassSubgroup_map_smul_le (σ : Gal(M/K)) :
    (Idele.normClassSubgroup M L).map
        (MulDistribMulAction.toMulAut (Gal(M/K)) (IdeleClassGroup M) σ).toMonoidHom ≤
      Idele.normClassSubgroup M L := by
  rintro q ⟨x, hx, rfl⟩
  change σ • x ∈ Idele.normClassSubgroup M L
  exact normClassSubgroup_smul_mem σ x hx

/-- **`Gal(M/K)` maps the norm subgroup onto itself.** -/
theorem normClassSubgroup_map_smul_eq (σ : Gal(M/K)) :
    (Idele.normClassSubgroup M L).map
        (MulDistribMulAction.toMulAut (Gal(M/K)) (IdeleClassGroup M) σ).toMonoidHom =
      Idele.normClassSubgroup M L := by
  refine le_antisymm (normClassSubgroup_map_smul_le σ) ?_
  intro q hq
  refine ⟨σ⁻¹ • q, normClassSubgroup_smul_mem σ⁻¹ q hq, ?_⟩
  change σ • (σ⁻¹ • q) = q
  rw [smul_inv_smul]

end Corollary

end NK.CFTLib
