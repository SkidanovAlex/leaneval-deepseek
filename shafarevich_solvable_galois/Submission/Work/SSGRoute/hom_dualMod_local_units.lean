import Mathlib
import Submission.Work.SSGRoute.Interfaces
import Submission.Work.SSGRoute.PTDefs
import Submission.Work.SSGRoute.homRep
import Submission.Work.SSGRoute.DualMod.Main
import Submission.Work.SSGRoute.dualUnits_linearEquiv
import Submission.Work.Shrinking.Basic
import Submission.Work.SSGRoute.PT.Hilbert90IsAlgClosure
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute

open SSGRoute.PTExt
open scoped TensorProduct

set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 800000

/-- **The Tate twist cancels against `μ_p`: the local twin of node `E1a/2`.**  `L` a field, `Ω` a
field containing a primitive `p`-th root of unity `ζ` (`hζ`, and `ζ ∈ K` for a finite Galois
`K ⊆ Ω`), `T` the cyclotomic dual of `μ_p` (`IsCyclotomicDual p T (res) ζ`), `E` a finite
`𝔽_p[Gal(K/L)]`-module.  Then `Hom_ℤ(E^∨(1), Ωˣ) ≅ E`, `E^∨(1) = DualMod p (E ⊗ T)`, as
`Rep Coeff Gal(Ω/L)` — `homRep` is the internal `Hom` with the conjugation action, `Ωˣ` carries
its natural action, and `E` is inflated along `AlgEquiv.restrictNormalHom ↥K`.

Proof: `char Ω ≠ p` (from `hζ`), so `Ωˣ[p] = μ_p = ⟨ζ⟩`, hence
`Hom_ℤ(DualMod p (E⊗T), Ωˣ) = Hom_{𝔽_p}(E^∨(1), μ_p)`; double duality over `𝔽_p`
(`[Finite E]` and `finrank T = 1`) identifies this with `E ⊗ T ⊗ μ_p` with action
`ρ_E(σ) ⊗ χ^{-1}(σ) ⊗ χ(σ)`, and `T ⊗ μ_p ≅ 𝔽_p` *equivariantly* by `IsCyclotomicDual`
(conjugation on `Hom(μ_p,μ_p)` kills the cyclotomic character).  `IsSepClosure`/`IsAlgClosure`
are not needed: only `Ωˣ[p] = μ_p` and `ζ ∈ Ω` are used. -/
theorem hom_dualMod_local_units (p : ℕ) [Fact p.Prime] {L Ω : Type} [Field L] [Field Ω]
    [Algebra L Ω] (K : IntermediateField L Ω) [FiniteDimensional L K] [IsGalois L K]
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
    (T : Type) [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction (K ≃ₐ[L] K) T]
    [SMulCommClass (K ≃ₐ[L] K) (ZMod p) T]
    (hT : SSGRoute.IsCyclotomicDual p (T := T)
      (AlgEquiv.restrictNormalHom (F := L) (K₁ := Ω) ↥K) ζ)
    (E : Type) [AddCommGroup E] [Module (ZMod p) E] [DistribMulAction (K ≃ₐ[L] K) E]
    [SMulCommClass (K ≃ₐ[L] K) (ZMod p) E] [Finite E] :
    Nonempty (Work.SSGRoute.homRep
        (Rep.res (G := ↥K ≃ₐ[L] ↥K)
          (AlgEquiv.restrictNormalHom (F := L) (K₁ := Ω) ↥K)
          (SSGRoute.PTExt.modRep (K ≃ₐ[L] K)
            (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) E T))))
        (SSGRoute.PTExt.modRep (Ω ≃ₐ[L] Ω) (Additive (Units Ω))) ≅
      Rep.res (G := ↥K ≃ₐ[L] ↥K)
        (AlgEquiv.restrictNormalHom (F := L) (K₁ := Ω) ↥K)
        (SSGRoute.PTExt.modRep (K ≃ₐ[L] K) E)) := by
  classical
  haveI hNp : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  -- the restriction map `Ω ≃ₐ[L] Ω →* K ≃ₐ[L] K`
  let f : (Ω ≃ₐ[L] Ω) →* (K ≃ₐ[L] K) :=
    AlgEquiv.restrictNormalHom (F := L) (K₁ := Ω) ↥K
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
        = ((homRep (Rep.res f (SSGRoute.PTExt.modRep (K ≃ₐ[L] K)
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
      Ψ.toLinearMap ∘ₗ ((Rep.res f (SSGRoute.PTExt.modRep (K ≃ₐ[L] K) E)).ρ g)
        = ((homRep (Rep.res f (SSGRoute.PTExt.modRep (K ≃ₐ[L] K)
              (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) E T))))
            (SSGRoute.PTExt.modRep (Ω ≃ₐ[L] Ω) (Additive (Units Ω)))).ρ g)
          ∘ₗ Ψ.toLinearMap := by
    intro g
    apply LinearMap.ext
    intro e
    exact hequiv_pt g e
  exact ⟨(Rep.mkIso (Representation.Equiv.mk Ψ hequiv)).symm⟩

end Work.SSGRoute
