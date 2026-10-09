import Mathlib
import Submission.Work.SSGRoute.Interfaces
import Submission.Work.SSGRoute.DualMod.Main
import Submission.Work.SSGRoute.PTDefs
import Submission.Work.SSGRoute.PT.e1a_coeff_iso_natural
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The canonical coefficient isomorphism `E ≅ Hom_ℤ(E',Ωˣ)`, *generic base field and group*

`Work.SSGRoute.PT.e1a_coeff_iso_natural` proves, for a *number field* base `k` and the group
`K ≃ₐ[k] K`, that the coefficient identification `E ≅ Hom_ℤ(DualMod p (E ⊗ T), Ωˣ)` is a *natural*
family in `E`.  Its construction, however, never uses the base field: `e1aCoeffEquiv` is
`e1aIsoE ▷ Module.evalEquiv ▷ dualEquiv_zpow` and all three factors depend only on `p`, on the
`𝔽_p`-module `E`, on `T` (through `finrank T = 1`) and on the *units of a commutative domain*
with a chosen primitive `p`-th root `ζu`.

The local data of the E1a comparison square — the completion `k_v`, the local field `K_w`, the
local closure `Ω_v` — are **not** number fields, so `e1a_coeff_iso_natural` cannot be instantiated
there; that is exactly why the on-disk local dictionary
(`Work.SSGRoute.local_ext_h1_bridge`) uses the `Nonempty` brick
`homRep_dualMod_units_localClosure` and carries no naturality.

This file provides the *generic* form: for arbitrary `L` (`CharZero`), `M` (algebraically closed
over `L`), an arbitrary group `G` and a comparison `act : (M ≃ₐ[L] M) →* G` for which `T` is
cyclotomic-dual, there is a *single* construction `Ψ : ∀ E, E ≃+ Hom_ℤ(E', Mˣ)` which is
equivariant and natural in `E`.  Instantiated at the local data it is the missing named brick of
the local dictionary; instantiated at `G := K ≃ₐ[k] K`, `act := res k K` it reproduces
`e1a_coeff_iso_natural`.

The action on `Hom_ℤ(E', Mˣ) = DualMod p (E ⊗ T) →+ Additive Mˣ` is the conjugation action
`(γ · φ)(x) = γ • φ ((act γ)⁻¹ • x)` (the `homCoind` convention); the equivariance is stated in
the *conjugated* elementwise form, which is what the `homCoind`-action unfolding consumes.
-/

open scoped TensorProduct

set_option backward.isDefEq.respectTransparency false

namespace Work.SSGRoute.E1aClean

noncomputable section

open Work.AbsoluteKummer

/-- **The generic coefficient isomorphism** `E ≃+ Hom_ℤ(DualMod p (E ⊗ T), Mˣ)`,
`e ↦ (φ ↦ ζu ^ (φ (e ⊗ t₀)))`, for a commutative domain `M` and a primitive root `ζu`. -/
noncomputable def coeffEquivGeneric (p : ℕ) [Fact p.Prime] {M : Type} [CommRing M] [IsDomain M]
    (E T : Type) [AddCommGroup E] [Module (ZMod p) E] [AddCommGroup T] [Module (ZMod p) T]
    [Finite E] (hT : Module.finrank (ZMod p) T = 1) (ζu : Mˣ)
    (hζu : IsPrimitiveRoot ζu p) :
    E ≃+ (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) E T) →+ Additive Mˣ) := by
  classical
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  haveI : Module.Finite (ZMod p) T :=
    Module.finite_of_finrank_pos (by rw [hT]; norm_num)
  haveI : Module.Finite (ZMod p) (TensorProduct (ZMod p) E T) :=
    Module.Finite.tensorProduct (ZMod p) E T
  haveI : Module.IsReflexive (ZMod p) (TensorProduct (ZMod p) E T) := inferInstance
  exact (Work.SSGRoute.PT.e1aIsoE p E T hT).toAddEquiv.trans
    ((Module.evalEquiv (ZMod p) (TensorProduct (ZMod p) E T)).toAddEquiv.trans
      (Work.SSGRoute.dualEquiv_zpow p ζu hζu
        (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) E T))))

/-- The computation rule of `coeffEquivGeneric`: `e ↦ (φ ↦ ζu ^ (φ (e ⊗ t₀)))`. -/
@[simp] theorem coeffEquivGeneric_apply (p : ℕ) [Fact p.Prime] {M : Type} [CommRing M] [IsDomain M]
    (E T : Type) [AddCommGroup E] [Module (ZMod p) E] [AddCommGroup T] [Module (ZMod p) T]
    [Finite E] (hT : Module.finrank (ZMod p) T = 1) (ζu : Mˣ)
    (hζu : IsPrimitiveRoot ζu p)
    (e : E) (φ : Work.SSGRoute.DualMod p (TensorProduct (ZMod p) E T)) :
    coeffEquivGeneric p E T hT ζu hζu e φ
      = Work.SSGRoute.zetaPowHom ζu hζu
          (φ (e ⊗ₜ[ZMod p] Work.SSGRoute.PT.e1aTGen p T hT)) := by
  classical
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  haveI : Module.Finite (ZMod p) T :=
    Module.finite_of_finrank_pos (by rw [hT]; norm_num)
  haveI : Module.Finite (ZMod p) (TensorProduct (ZMod p) E T) :=
    Module.Finite.tensorProduct (ZMod p) E T
  haveI : Module.IsReflexive (ZMod p) (TensorProduct (ZMod p) E T) := inferInstance
  show Work.SSGRoute.dualEquiv_zpow p ζu hζu
      (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) E T))
      ((Module.evalEquiv (ZMod p) (TensorProduct (ZMod p) E T))
        (Work.SSGRoute.PT.e1aIsoE p E T hT e)) φ = _
  rw [Work.SSGRoute.dualEquiv_zpow_apply, Module.evalEquiv_apply, Module.Dual.eval_apply,
    Work.SSGRoute.PT.e1aIsoE_apply]

/-- **The natural coefficient identification over an arbitrary base.**

For `L` of characteristic `0`, `M` algebraically closed over `L`, an arbitrary group `G` and
`act : (M ≃ₐ[L] M) →* G` making `T` cyclotomic-dual to `ζ`, there is a single family
`Ψ_E : E ≃+ Hom_ℤ(DualMod p (E ⊗ T), Mˣ)` which is equivariant for the conjugation action and
natural in the coefficient: for the transpose `F` of an equivariant `f : E₁ → E₂`,
`Ψ_{E₂} (f e) = (Ψ_{E₁} e).comp F.hom.toAddMonoidHom`. -/
theorem coeffIso_natural_generic (p : ℕ) [Fact p.Prime] {L M : Type} [Field L] [CharZero L]
    [Field M] [Algebra L M] [IsAlgClosure L M] {G : Type} [Group G]
    (T : Type) [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction G T]
    [SMulCommClass G (ZMod p) T]
    (act : (M ≃ₐ[L] M) →* G) (ζ : M) (hζ : IsPrimitiveRoot ζ p)
    (hT : SSGRoute.IsCyclotomicDual p (T := T) act ζ) :
    ∃ Ψ : ∀ (E : Type) [AddCommGroup E] [Module (ZMod p) E] [DistribMulAction G E]
        [SMulCommClass G (ZMod p) E] [Finite E],
        E ≃+ (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) E T) →+ Additive Mˣ),
      (∀ (E : Type) [AddCommGroup E] [Module (ZMod p) E] [DistribMulAction G E]
        [SMulCommClass G (ZMod p) E] [Finite E]
        (γ : M ≃ₐ[L] M) (e : E)
        (φ : Work.SSGRoute.DualMod p (TensorProduct (ZMod p) E T)),
        Ψ E (act γ • e) φ = γ • (Ψ E e) ((act γ)⁻¹ • φ)) ∧
      (∀ (E₁ : Type) [AddCommGroup E₁] [Module (ZMod p) E₁] [DistribMulAction G E₁]
        [SMulCommClass G (ZMod p) E₁] [Finite E₁]
        (E₂ : Type) [AddCommGroup E₂] [Module (ZMod p) E₂] [DistribMulAction G E₂]
        [SMulCommClass G (ZMod p) E₂] [Finite E₂]
        (f : E₁ →ₗ[ZMod p] E₂) (hf : ∀ (g : G) (e : E₁), f (g • e) = g • f e)
        (F : SSGRoute.PTExt.modRep G
            (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) E₂ T)) ⟶
          SSGRoute.PTExt.modRep G
            (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) E₁ T)))
        (hF : ∀ (φ : Work.SSGRoute.DualMod p (TensorProduct (ZMod p) E₂ T)) (e : E₁) (t : T),
          (show Work.SSGRoute.DualMod p (TensorProduct (ZMod p) E₁ T) from F.hom φ)
            (TensorProduct.tmul (ZMod p) e t)
          = φ (TensorProduct.tmul (ZMod p) (f e) t))
        (e : E₁), Ψ E₂ (f e) = (Ψ E₁ e).comp F.hom.toAddMonoidHom) := by
  classical
  haveI hNp : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  haveI hTf : Module.Finite (ZMod p) T :=
    Module.finite_of_finrank_pos (by rw [hT.1]; norm_num)
  refine ⟨fun E _ _ _ _ _ => coeffEquivGeneric p E T hT.1
      (Work.SSGRoute.PT.e1aZetaUnit p M ζ hζ)
      (Work.SSGRoute.PT.e1aZetaUnit_isPrimitiveRoot p M ζ hζ), ?_, ?_⟩
  · -- equivariance (conjugated elementwise form)
    intro E _ _ _ _ _ γ e φ
    rw [coeffEquivGeneric_apply, coeffEquivGeneric_apply]
    obtain ⟨c, hc⟩ : ∃ c : ℕ, γ • ζ = ζ ^ c := by
      have hpow : (γ • ζ) ^ p = 1 := by
        rw [show γ • ζ = γ ζ from rfl, ← map_pow, hζ.pow_eq_one, map_one]
      obtain ⟨c, -, hc⟩ := IsPrimitiveRoot.eq_pow_of_pow_eq_one hζ hpow
      exact ⟨c, hc.symm⟩
    have hσζu : γ • Work.SSGRoute.PT.e1aZetaUnit p M ζ hζ
        = (Work.SSGRoute.PT.e1aZetaUnit p M ζ hζ) ^ c := by
      apply Units.ext
      rw [show (↑(γ • Work.SSGRoute.PT.e1aZetaUnit p M ζ hζ) : M)
            = γ • (↑(Work.SSGRoute.PT.e1aZetaUnit p M ζ hζ) : M) from rfl,
        Work.SSGRoute.PT.e1aZetaUnit_val, hc, Units.val_pow_eq_pow_val,
        Work.SSGRoute.PT.e1aZetaUnit_val]
    have hkey : ∀ x : ZMod p,
        γ • Work.SSGRoute.zetaPowHom (Work.SSGRoute.PT.e1aZetaUnit p M ζ hζ)
            (Work.SSGRoute.PT.e1aZetaUnit_isPrimitiveRoot p M ζ hζ) x
          = Work.SSGRoute.zetaPowHom (Work.SSGRoute.PT.e1aZetaUnit p M ζ hζ)
              (Work.SSGRoute.PT.e1aZetaUnit_isPrimitiveRoot p M ζ hζ) (c • x) :=
      fun x => Work.SSGRoute.zetaPowHom_smul (Work.SSGRoute.PT.e1aZetaUnit p M ζ hζ)
        (Work.SSGRoute.PT.e1aZetaUnit_isPrimitiveRoot p M ζ hζ) γ hσζu x
    have hTt : (c : ZMod p) • (act γ • Work.SSGRoute.PT.e1aTGen p T hT.1)
        = Work.SSGRoute.PT.e1aTGen p T hT.1 := by
      rw [Nat.cast_smul_eq_nsmul (ZMod p) c (act γ • Work.SSGRoute.PT.e1aTGen p T hT.1)]
      exact hT.2 γ c hc (Work.SSGRoute.PT.e1aTGen p T hT.1)
    have hz : (c : ZMod p) • (act γ • (e ⊗ₜ[ZMod p] Work.SSGRoute.PT.e1aTGen p T hT.1))
        = (act γ • e) ⊗ₜ[ZMod p] Work.SSGRoute.PT.e1aTGen p T hT.1 := by
      rw [Work.Shrinking.diagTensor_smul_tmul]
      rw [← TensorProduct.tmul_smul (c : ZMod p) (act γ • e)
        (act γ • Work.SSGRoute.PT.e1aTGen p T hT.1)]
      rw [hTt]
    rw [show (((act γ)⁻¹) • φ) (e ⊗ₜ[ZMod p] Work.SSGRoute.PT.e1aTGen p T hT.1)
        = φ (act γ • (e ⊗ₜ[ZMod p] Work.SSGRoute.PT.e1aTGen p T hT.1)) from by
      rw [Work.SSGRoute.DualMod.dualSMul_apply]; simp]
    rw [← hz, map_smul]
    rw [show (c : ZMod p) • (φ (act γ • (e ⊗ₜ[ZMod p] Work.SSGRoute.PT.e1aTGen p T hT.1)))
        = c • (φ (act γ • (e ⊗ₜ[ZMod p] Work.SSGRoute.PT.e1aTGen p T hT.1))) from
      Nat.cast_smul_eq_nsmul (ZMod p) c _]
    rw [hkey]
  · -- naturality in the coefficient
    intro E₁ _ _ _ _ _ E₂ _ _ _ _ _ f hf F hF e
    apply AddMonoidHom.ext
    intro φ
    rw [coeffEquivGeneric_apply]
    simp only [AddMonoidHom.comp_apply]
    rw [coeffEquivGeneric_apply]
    congr 1
    exact (hF φ e (Work.SSGRoute.PT.e1aTGen p T hT.1)).symm

end

end Work.SSGRoute.E1aClean
