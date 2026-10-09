import Mathlib
import Submission.Work.SSGRoute.E7aAux
import Submission.Work.SSGRoute.PTDefs
import Submission.Work.SSGRoute.Interfaces
import Submission.Work.SSGRoute.homRep
import Submission.Work.SSGRoute.hom_dualMod_local_units
import Submission.Work.SSGRoute.PTembedding.homRep_dualMod_units_of_isCyclotomicDual
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute

open SSGRoute.PTExt CategoryTheory
open scoped TensorProduct

set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 800000
set_option linter.style.haveILetI false

/-- **The Tate twist cancels against `μ_p`, for a completely arbitrary target group.**

This is `Work.SSGRoute.PTembedding.homRep_dualMod_units_of_isCyclotomicDual` with the Galois group
`K ≃ₐ[L] K` replaced by an *arbitrary* group `G` carrying the actions on `T` and `E`:

`Hom_ℤ(E^∨(1), Ωˣ) ≅ E`, `E^∨(1) = DualMod p (E ⊗ T)`, as `Rep Coeff Gal(Ω/L)`-modules, where
`homRep` is the internal `Hom` with the conjugation action, `Ωˣ` carries its natural
`Gal(Ω/L)`-action, and `E` is read through the monoid homomorphism `act : Gal(Ω/L) →* G`.

The proof is that of the original (local) theorem: `char Ω ≠ p` (from `hζ`), so `Ωˣ[p] = μ_p =
⟨ζ⟩`, hence `Hom_ℤ(DualMod p (E⊗T), Ωˣ) = Hom_{𝔽_p}(E^∨(1), μ_p)`; double duality over `𝔽_p`
(`[Finite E]` and `finrank T = 1`) identifies this with `E ⊗ T ⊗ μ_p` with action
`ρ_E(act σ) ⊗ χ^{-1}(act σ) ⊗ χ(σ)`, and `T ⊗ μ_p ≅ 𝔽_p` *equivariantly* by `IsCyclotomicDual`.

No hypothesis on `G` beyond the module structure is used: in the original proof the group
`K ≃ₐ[L] K` enters only through `act` and the action on `E`, `T`. -/
theorem homRep_dualMod_units_arbitraryGroup (p : ℕ) [Fact p.Prime] {L Ω : Type} [Field L]
    [Field Ω] [Algebra L Ω]
    {G : Type} [Group G]
    (T : Type) [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction G T]
    [SMulCommClass G (ZMod p) T]
    (E : Type) [AddCommGroup E] [Module (ZMod p) E] [DistribMulAction G E]
    [SMulCommClass G (ZMod p) E] [Finite E]
    (act : (Ω ≃ₐ[L] Ω) →* G)
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ p)
    (hT : SSGRoute.IsCyclotomicDual p (T := T) act ζ) :
    Nonempty (Work.SSGRoute.homRep
        (Rep.res act (SSGRoute.PTExt.modRep G
          (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) E T))))
        (SSGRoute.PTExt.modRep (Ω ≃ₐ[L] Ω) (Additive (Units Ω))) ≅
      Rep.res act (SSGRoute.PTExt.modRep G E)) := by
  classical
  haveI hNp : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  -- the comparison map, as a monoid homomorphism
  let f : (Ω ≃ₐ[L] Ω) →* G := act
  -- the primitive `p`-th root of unity as a unit
  let ζu : Ωˣ := (hζ.isUnit hNp.out).unit
  have hζu_val : (ζu : Ω) = ζ := IsUnit.unit_spec _
  have hζu : IsPrimitiveRoot ζu p :=
    IsPrimitiveRoot.coe_units_iff.mp (by rw [hζu_val]; exact hζ)
  -- `T` is finite of rank one
  haveI : Module.Finite (ZMod p) T :=
    Module.finite_of_finrank_pos (by rw [hT.1]; norm_num)
  let u : T ≃ₗ[ZMod p] ZMod p :=
    LinearEquiv.ofFinrankEq (R := ZMod p) T (ZMod p) (by rw [hT.1, Module.finrank_self])
  let t₀ : T := u.symm 1
  haveI : Fintype (ZMod p) := inferInstance
  haveI : Finite (ZMod p) := inferInstance
  haveI : Finite T := Finite.of_injective u u.injective
  haveI : Module.Finite (ZMod p) E := Module.Finite.of_finite
  haveI : Module.Finite (ZMod p) (TensorProduct (ZMod p) E T) :=
    Module.Finite.tensorProduct (ZMod p) E T
  -- `E ≃ E ⊗ T` over `𝔽_p`, sending `e` to `e ⊗ t₀`
  let isoE_zm : E ≃ₗ[ZMod p] TensorProduct (ZMod p) E T :=
    (TensorProduct.rid (ZMod p) E).symm.trans
      ((TensorProduct.congr (LinearEquiv.refl (ZMod p) E) u).symm)
  have hisoE_zm : ∀ e : E, isoE_zm e = e ⊗ₜ[ZMod p] t₀ := by
    intro e
    rw [show isoE_zm e = (TensorProduct.congr (LinearEquiv.refl (ZMod p) E) u).symm
        ((TensorProduct.rid (ZMod p) E).symm e) from rfl]
    rw [TensorProduct.rid_symm_apply, TensorProduct.congr_symm, TensorProduct.congr_tmul]
    simp [t₀]
  haveI : Finite (TensorProduct (ZMod p) E T) :=
    Finite.of_injective isoE_zm.symm isoE_zm.symm.injective
  -- double duality over `𝔽_p` with values in `Ωˣ`
  obtain ⟨eA, heA⟩ := dualUnits_linearEquiv p ζu hζu (TensorProduct (ZMod p) E T)
  let isoE : E ≃ₗ[SSGRoute.PTExt.Coeff] TensorProduct (ZMod p) E T :=
    AddEquiv.toLinearEquiv isoE_zm.toAddEquiv (fun c x => by
      change isoE_zm.toAddEquiv (c • x) = c • isoE_zm.toAddEquiv x
      rw [show c • x = c.down • x from rfl,
        show c • isoE_zm.toAddEquiv x = c.down • isoE_zm.toAddEquiv x from rfl]
      exact AddMonoidHom.map_zsmul isoE_zm.toAddEquiv.toAddMonoidHom c.down x)
  have hisoE : ∀ e : E, isoE e = e ⊗ₜ[ZMod p] t₀ := fun e => hisoE_zm e
  let Ψ : E ≃ₗ[SSGRoute.PTExt.Coeff]
      (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) E T) →ₗ[SSGRoute.PTExt.Coeff]
        Additive Ωˣ) :=
    isoE.trans eA
  have hΨ : ∀ (e : E) (φ : Work.SSGRoute.DualMod p (TensorProduct (ZMod p) E T)),
      Ψ e φ = SelfDual.zetaPowHom ζu hζu (φ (e ⊗ₜ[ZMod p] t₀)) := by
    intro e φ
    show eA (isoE e) φ = _
    rw [heA (isoE e) φ, hisoE e]
  -- equivariance of `Ψ`
  have hequiv_pt : ∀ (g : Ω ≃ₐ[L] Ω) (e : E),
      Ψ (f g • e)
        = ((homRep (Rep.res f (SSGRoute.PTExt.modRep G
              (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) E T))))
            (SSGRoute.PTExt.modRep (Ω ≃ₐ[L] Ω) (Additive (Units Ω)))).ρ g) (Ψ e) := by
    intro g e
    apply LinearMap.ext
    intro φ
    change Ψ (f g • e) φ
        = (SSGRoute.PTExt.modRep (Ω ≃ₐ[L] Ω) (Additive (Units Ω))).ρ g
          (Ψ e ((f g⁻¹) • φ))
    obtain ⟨c, hc⟩ : ∃ c : ℕ, g • ζ = ζ ^ c := by
      have hpw : (g • ζ) ^ p = 1 := by
        rw [show g • ζ = g ζ from rfl, ← map_pow, hζ.pow_eq_one, map_one]
      obtain ⟨c, -, hc⟩ := IsPrimitiveRoot.eq_pow_of_pow_eq_one hζ hpw
      exact ⟨c, hc.symm⟩
    have hgζu : g • ζu = ζu ^ c := by
      apply Units.ext
      rw [show (↑(g • ζu) : Ω) = g • (↑ζu : Ω) from rfl, hζu_val, hc,
        Units.val_pow_eq_pow_val, hζu_val]
    have hkey : ∀ x : ZMod p, g • SelfDual.zetaPowHom ζu hζu x
        = SelfDual.zetaPowHom ζu hζu (c • x) :=
      fun x => SelfDual.zetaPowHom_smul ζu hζu g hgζu x
    have hTt : (c : ZMod p) • (f g • t₀) = t₀ := by
      rw [Nat.cast_smul_eq_nsmul (ZMod p) c (f g • t₀)]
      exact hT.2 g c hc t₀
    have hz : (c : ZMod p) • (f g • (e ⊗ₜ[ZMod p] t₀)) = (f g • e) ⊗ₜ[ZMod p] t₀ := by
      rw [Work.Shrinking.diagTensor_smul_tmul]
      rw [← TensorProduct.tmul_smul (c : ZMod p) (f g • e) (f g • t₀)]
      rw [hTt]
    rw [hΨ (f g • e) φ, hΨ e ((f g⁻¹) • φ)]
    rw [show ((f g⁻¹) • φ) (e ⊗ₜ[ZMod p] t₀) = φ (f g • (e ⊗ₜ[ZMod p] t₀)) from by
      rw [Work.SSGRoute.DualMod.dualSMul_apply, map_inv, inv_inv]]
    change SelfDual.zetaPowHom ζu hζu (φ ((f g • e) ⊗ₜ[ZMod p] t₀))
        = g • SelfDual.zetaPowHom ζu hζu (φ (f g • (e ⊗ₜ[ZMod p] t₀)))
    rw [← hz, map_smul]
    rw [show (c : ZMod p) • (φ (f g • (e ⊗ₜ[ZMod p] t₀)))
        = c • (φ (f g • (e ⊗ₜ[ZMod p] t₀))) from
      Nat.cast_smul_eq_nsmul (ZMod p) c _]
    rw [hkey]
  have hequiv : ∀ g : Ω ≃ₐ[L] Ω,
      Ψ.toLinearMap ∘ₗ ((Rep.res f (SSGRoute.PTExt.modRep G E)).ρ g)
        = ((homRep (Rep.res f (SSGRoute.PTExt.modRep G
              (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) E T))))
            (SSGRoute.PTExt.modRep (Ω ≃ₐ[L] Ω) (Additive (Units Ω)))).ρ g)
          ∘ₗ Ψ.toLinearMap := by
    intro g
    apply LinearMap.ext
    intro e
    exact hequiv_pt g e
  exact ⟨(Rep.mkIso (Representation.Equiv.mk Ψ hequiv)).symm⟩

theorem homRep_dualMod_units_localClosure (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k]
    [NumberField k] [Field Ω] [Algebra k Ω] [IsSepClosure k Ω] (K : IntermediateField k Ω)
    [FiniteDimensional k K] [IsGalois k K] [NumberField K] (A : ValuationSubring Ω)
    (hA : SSGRoute.IsFinPlace k A)
    (T : Type) [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction (K ≃ₐ[k] K) T]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T]
    (E : Type) [AddCommGroup E] [Module (ZMod p) E] [DistribMulAction (K ≃ₐ[k] K) E]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E] [Finite E]
    (act : (Work.SSGRoute.localClosureAt k A hA ≃ₐ[Work.SSGRoute.localFieldAt k A hA]
        Work.SSGRoute.localClosureAt k A hA) →* (K ≃ₐ[k] K))
    (ζ' : Work.SSGRoute.localClosureAt k A hA) (hζ' : IsPrimitiveRoot ζ' p)
    (hcyc : SSGRoute.IsCyclotomicDual p (T := T) act ζ') :
    Nonempty (Work.SSGRoute.homRep
        (Rep.res act (SSGRoute.PTExt.modRep (K ≃ₐ[k] K)
          (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) E T))))
        (SSGRoute.PTExt.modRep
          (Work.SSGRoute.localClosureAt k A hA ≃ₐ[Work.SSGRoute.localFieldAt k A hA]
            Work.SSGRoute.localClosureAt k A hA)
          (Additive (Units (Work.SSGRoute.localClosureAt k A hA)))) ≅
        Rep.res act (SSGRoute.PTExt.modRep (K ≃ₐ[k] K) E)) := by
  exact homRep_dualMod_units_arbitraryGroup (p := p)
    (L := Work.SSGRoute.localFieldAt k A hA)
    (Ω := Work.SSGRoute.localClosureAt k A hA) (G := K ≃ₐ[k] K)
    (T := T) (E := E) (act := act) (ζ := ζ') (hζ := hζ') (hT := hcyc)

end Work.SSGRoute
