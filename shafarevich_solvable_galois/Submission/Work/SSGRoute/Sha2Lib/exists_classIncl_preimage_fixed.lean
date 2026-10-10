import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RepresentationTheory.Rep.Res
import Submission.Work.SSGRoute.classIncl_isCanonical
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute.Sha2Lib

open SSGRoute.PTExt CategoryTheory
open NK.GlobalCFT NK.HassePrinciple

/-- **A `Gal(L/k)`-fixed class in `C_L` is the image of a `Gal(F/k)`-fixed class in `C_F`**
(the `H⁰`-computation `C_k ≅ (C_K)^{Gal(K/k)}` of class field theory, used here at the two levels
`k ⊆ F ⊆ L` together with the injectivity of the canonical inclusion `C_F → C_L`).

Existence of a preimage `aF` of `a` under `classIncl k F L` is the proof of
`Submission.Work.SSGRoute.classIncl_mem_invariants_range` with `(k, K) := (k, F)` and `L` in place
of `K` (`SSGRoute.classIncl_isCanonical` +
`NK.GlobalCFT.Inclusion.globalCFT_invariants_le_range` from
`Submission.NK.GlobalCFT.Inclusion.globalCFT_invariants_ideleClassGroup`, which uses that `a` is
also fixed by the restriction of the action to `Gal(L/F) ⊆ Gal(L/k)`).

Fixedness of `aF`: `(classIncl k F L).hom` is injective on the underlying carrier
(`NK.GlobalCFT.Inclusion.globalCFT_ideleClassGroup_inclusion_injective` applied to the data
furnished by `classIncl_isCanonical k F L`) and `Gal(L/k) → Gal(F/k)` is onto
(`AlgEquiv.restrictNormalHom_surjective`), so pick a lift `σ` of `τ ∈ Gal(F/k)` and use the
intertwining of `classIncl k F L` (`Representation.IntertwiningMap.hom_comm_apply`) together with
`∀ σ, (classesK k L).ρ σ a = a`. Note: `classIncl k F L` intertwines the action of `Gal(L/k)` on
the source with `galRes`, i.e. `(classIncl k F L).hom (ρ σ x) = ρ σ ((classIncl k F L).hom x)` for
the *res* representation's action `(Rep.res (galRes k F L) (classesK k F)).ρ σ`
(`Rep.coe_res_obj_ρ'`). The file should `open SSGRoute.PTExt CategoryTheory`. -/
theorem exists_classIncl_preimage_fixed (k F L : Type) [Field k] [NumberField k] [Field F]
    [NumberField F] [Field L] [NumberField L] [Algebra k F] [Algebra F L] [Algebra k L]
    [IsScalarTower k F L] [FiniteDimensional k F] [IsGalois k F] [FiniteDimensional k L]
    [IsGalois k L]
    (a : SSGRoute.PTExt.classesK k L)
    (ha : ∀ σ : L ≃ₐ[k] L, (SSGRoute.PTExt.classesK k L).ρ σ a = a) :
    ∃ aF : SSGRoute.PTExt.classesK k F,
      (∀ τ : F ≃ₐ[k] F, (SSGRoute.PTExt.classesK k F).ρ τ aF = aF) ∧
        (SSGRoute.PTExt.classIncl k F L).hom aF = a := by
  classical
  haveI : FiniteDimensional F L := FiniteDimensional.right k F L
  haveI : IsGalois F L := IsGalois.tower_top_of_isGalois k F L
  -- Canonical data for the inclusion `C_F → C_L`.
  obtain ⟨u, hu, φ, hφ, hι⟩ := classIncl_isCanonical k F L
  obtain ⟨ψ, hψ⟩ := NK.GlobalCFT.Inclusion.globalCFT_ideleClassGroup_inclusion_exists u hu φ hφ
  -- `ψ` computes `classIncl` on classes of idèles.
  have hψ_eq : ∀ y : IdeleClassGroup F,
      ψ y = Additive.toMul ((classIncl k F L).hom (Additive.ofMul y)) := by
    intro y
    obtain ⟨x, rfl⟩ := IdeleClassGroup.mk_surjective F y
    rw [hψ x]
    exact (congrArg Additive.toMul (hι x)).symm
  have hψinj : Function.Injective ψ :=
    NK.GlobalCFT.Inclusion.globalCFT_ideleClassGroup_inclusion_injective u hu φ hφ ψ hψ
  -- The class `a` as an element `q` of `C_L`.
  let q : IdeleClassGroup L := Additive.toMul a
  have hqfix : ∀ σ : L ≃ₐ[k] L, σ • q = q := by
    intro σ
    have h' : Additive.ofMul (σ • q) = Additive.ofMul q := by
      have h2 := ha σ
      change (classesK k L).ρ σ (Additive.ofMul q) = Additive.ofMul q at h2
      rwa [NK.HassePrinciple.classGroupRep_ρ_apply k L σ q] at h2
    exact Additive.ofMul.injective h'
  -- `a` is fixed by the smaller group `Gal(L/F)`.
  have hqfixF : ∀ τ : L ≃ₐ[F] L, τ • q = q := fun τ => hqfix (AlgEquiv.restrictScalars k τ)
  -- The `H⁰`-computation of class field theory at the level `F`.
  obtain ⟨y, hy⟩ := NK.GlobalCFT.Inclusion.globalCFT_invariants_le_range u hu φ hφ ψ hψ q hqfixF
  -- `classIncl` sends the class of `y` to `a`.
  have hmain : (classIncl k F L).hom (Additive.ofMul y) = a := by
    have h2 : Additive.toMul ((classIncl k F L).hom (Additive.ofMul y)) = Additive.toMul a := by
      rw [← hψ_eq y]
      exact hy
    exact congrArg Additive.ofMul h2
  refine ⟨Additive.ofMul y, ?_, hmain⟩
  -- `ψ` is equivariant for the Galois action (the intertwining of `classIncl`)
  have hψ_equiv : ∀ (σ : Gal(L/k)) (w : IdeleClassGroup F),
      ψ ((AlgEquiv.restrictNormalHom F) σ • w) = σ • ψ w := by
    intro σ w
    have hinter := Representation.IntertwiningMap.isIntertwining
      (Rep.res (galRes k F L) (classesK k F)).ρ (classesK k L).ρ (classIncl k F L).hom σ
      (Additive.ofMul w)
    rw [show (Rep.res (galRes k F L) (classesK k F)).ρ σ (Additive.ofMul w) =
        Additive.ofMul ((AlgEquiv.restrictNormalHom F) σ • w) from rfl] at hinter
    have h1 : (classIncl k F L).hom (Additive.ofMul w) = Additive.ofMul (ψ w) :=
      congrArg Additive.ofMul (hψ_eq w).symm
    rw [h1] at hinter
    change (Rep.Hom.hom (classIncl k F L))
        (Additive.ofMul ((AlgEquiv.restrictNormalHom F) σ • w)) =
      Additive.ofMul (σ • ψ w) at hinter
    rw [hψ_eq ((AlgEquiv.restrictNormalHom F) σ • w)]
    exact congrArg Additive.toMul hinter
  intro τ
  obtain ⟨σ, hσ⟩ := AlgEquiv.restrictNormalHom_surjective (K₁ := F) L τ
  have hfix : τ • y = y := by
    apply hψinj
    rw [← hσ]
    rw [hψ_equiv σ y]
    rw [hy]
    exact hqfix σ
  rw [NK.HassePrinciple.classGroupRep_ρ_apply k F τ y]
  exact congrArg Additive.ofMul hfix

end Work.SSGRoute.Sha2Lib
