import Mathlib
import Submission.Work.SSGRoute.PT.e1a_chain
import Submission.Work.SSGRoute.PT.e1a_coeff_iso_natural
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# E1a: auxiliary maps for the *canonical* (choice-free) form of the construction of `β`

`Work.SSGRoute.PT.e1aCoeffMap` is a `Classical.choose`-based realisation of the coefficient
identification `H²(Γ,E) → H²(Γ, Hom_ℤ(E',Ωˣ))`: it picks one equivariant additive isomorphism
`E ≃+ homCoind K (E')` out of `dualPairingEquiv_homCoind`.  Any naturality statement in the
coefficient `E` needs the *canonical* choice `e1aCoeffEquiv` (`PT/e1a_coeff_iso_natural.lean`)
instead.  So that the statements below (and the lemmas requested about them) stay free of the
type-class friction between the pointwise and the conjugation action on `homCoind`, the two maps
they concern are packaged here as opaque `def`s:

* `e1aCoeffMapOf … Ψ hΨ : H²(Γ,E) →+ H²(Γ, Hom_ℤ(E',Ωˣ))`, the `mapH2` of an arbitrary
  equivariant additive isomorphism `Ψ : E ≃+ homCoind K E'` — with `Ψ := e1aCoeffEquiv` and
  `hΨ` its equivariance this is the canonical coefficient map;
* `e1aH2Map … f hf : H²(Γ,M) →+ H²(Γ,M₂)`, the `mapH2` of an equivariant `𝔽_p`-linear map
  `f : M → M₂`, for the pulled-back action `DistribMulAction.compHom · (res k K)` of `G_k` on the
  coefficients.
-/

open CategoryTheory SSGRoute.PTExt
open scoped TensorProduct

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 500000

namespace Work.SSGRoute.PT

noncomputable section

/-- The `mapH2` of an equivariant additive isomorphism `Ψ : E ≃+ Hom_ℤ(E',Ωˣ)`, as a map
`H²(Γ,E) → H²(Γ, Hom_ℤ(E',Ωˣ))` (the two `H²`'s carrying the actions induced by
`G_k →* Gal(K/k)` resp. the conjugation action on `homCoind`). -/
noncomputable def e1aCoeffMapOf (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k]
    [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K]
    [IsGalois k K] [NumberField K] (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
    (T : Type) [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction (K ≃ₐ[k] K) T]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T]
    (hT : SSGRoute.IsCyclotomicDual p (T := T) (SSGRoute.res k K) ζ)
    (E : Type) [AddCommGroup E] [Module (ZMod p) E] [DistribMulAction (K ≃ₐ[k] K) E]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E] [Finite E]
    (Ψ : E ≃+ Work.SSGRoute.homCoind k Ω K (SSGRoute.PTExt.modRep (K ≃ₐ[k] K)
        (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) E T))))
    (hΨ : ∀ (σ : Ω ≃ₐ[k] Ω) (e : E),
      Ψ ((SSGRoute.res k K σ) • e) = σ • Ψ e) :
    @Work.AbsoluteKummer.H2 (Ω ≃ₐ[k] Ω) E _ _ _
        (DistribMulAction.compHom E (SSGRoute.res k K)) →+
      Work.AbsoluteKummer.H2 (Ω ≃ₐ[k] Ω)
        (Work.SSGRoute.homCoind k Ω K
          (SSGRoute.PTExt.modRep (K ≃ₐ[k] K)
            (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) E T)))) := by
  letI : DistribMulAction (Ω ≃ₐ[k] Ω) E := DistribMulAction.compHom E (SSGRoute.res k K)
  exact Work.AbsoluteKummer.mapH2 Ψ.toAddMonoidHom (fun σ e => hΨ σ e)

/-- The `mapH2` of an equivariant `𝔽_p`-linear map of coefficients, for the `G_k`-actions pulled
back along `res k K`.  Packaged so that naturality statements in the coefficient module can be
written without mentioning the `DistribMulAction.compHom` instances. -/
noncomputable abbrev e1aH2Map (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k]
    [Field Ω] [Algebra k Ω]
    (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (M : Type) [AddCommGroup M] [Module (ZMod p) M] [DistribMulAction (K ≃ₐ[k] K) M]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M]
    (M₂ : Type) [AddCommGroup M₂] [Module (ZMod p) M₂] [DistribMulAction (K ≃ₐ[k] K) M₂]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M₂]
    (f : M →ₗ[ZMod p] M₂) (hf : ∀ (g : K ≃ₐ[k] K) (m : M), f (g • m) = g • f m) :
    @Work.AbsoluteKummer.H2 (Ω ≃ₐ[k] Ω) M _ _ _
        (DistribMulAction.compHom M (SSGRoute.res k K)) →+
      @Work.AbsoluteKummer.H2 (Ω ≃ₐ[k] Ω) M₂ _ _ _
        (DistribMulAction.compHom M₂ (SSGRoute.res k K)) :=
  @Work.AbsoluteKummer.mapH2 (Ω ≃ₐ[k] Ω) M _ _ _
    (DistribMulAction.compHom M (SSGRoute.res k K))
    M₂ _ (DistribMulAction.compHom M₂ (SSGRoute.res k K))
    f.toAddMonoidHom (fun σ m => hf (SSGRoute.res k K σ) m)

/-- **The computation rule of `e1aH2Map` on classes**: on the class of a continuous `2`-cocycle
`c`, `e1aH2Map` is the class of the pushed-forward cocycle `q ↦ f (c q)`. -/
theorem e1aH2Map_H2π (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k]
    [Field Ω] [Algebra k Ω]
    (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (M : Type) [AddCommGroup M] [Module (ZMod p) M] [DistribMulAction (K ≃ₐ[k] K) M]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M]
    (M₂ : Type) [AddCommGroup M₂] [Module (ZMod p) M₂] [DistribMulAction (K ≃ₐ[k] K) M₂]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M₂]
    (f : M →ₗ[ZMod p] M₂) (hf : ∀ (g : K ≃ₐ[k] K) (m : M), f (g • m) = g • f m)
    (c : @Work.AbsoluteKummer.Z2 (Ω ≃ₐ[k] Ω) M _ _ _
        (DistribMulAction.compHom M (SSGRoute.res k K)))
    (h : (fun q : (Ω ≃ₐ[k] Ω) × (Ω ≃ₐ[k] Ω) => f (c.1 q)) ∈
      @Work.AbsoluteKummer.Z2 (Ω ≃ₐ[k] Ω) M₂ _ _ _
        (DistribMulAction.compHom M₂ (SSGRoute.res k K))) :
    e1aH2Map p k Ω K M M₂ f hf
        (@Work.AbsoluteKummer.H2π (Ω ≃ₐ[k] Ω) M _ _ _
          (DistribMulAction.compHom M (SSGRoute.res k K)) c)
      = (@Work.AbsoluteKummer.H2π (Ω ≃ₐ[k] Ω) M₂ _ _ _
          (DistribMulAction.compHom M₂ (SSGRoute.res k K))
          ⟨fun q : (Ω ≃ₐ[k] Ω) × (Ω ≃ₐ[k] Ω) => f (c.1 q), h⟩) := by
  letI : DistribMulAction (Ω ≃ₐ[k] Ω) M := DistribMulAction.compHom M (SSGRoute.res k K)
  letI : DistribMulAction (Ω ≃ₐ[k] Ω) M₂ := DistribMulAction.compHom M₂ (SSGRoute.res k K)
  have hφ : Work.GroupCohomology.IsEquivariant (Ω ≃ₐ[k] Ω) f.toAddMonoidHom :=
    fun σ m => hf (SSGRoute.res k K σ) m
  show (@Work.AbsoluteKummer.mapH2 (Ω ≃ₐ[k] Ω) M _ _ _
        (DistribMulAction.compHom M (SSGRoute.res k K))
        M₂ _ (DistribMulAction.compHom M₂ (SSGRoute.res k K))
        f.toAddMonoidHom hφ)
      (@Work.AbsoluteKummer.H2π (Ω ≃ₐ[k] Ω) M _ _ _
        (DistribMulAction.compHom M (SSGRoute.res k K)) c)
    = (@Work.AbsoluteKummer.H2π (Ω ≃ₐ[k] Ω) M₂ _ _ _
        (DistribMulAction.compHom M₂ (SSGRoute.res k K))
        ⟨fun q : (Ω ≃ₐ[k] Ω) × (Ω ≃ₐ[k] Ω) => f (c.1 q), h⟩)
  rw [Work.AbsoluteKummer.mapH2_H2π]
  exact congrArg _ (Subtype.ext rfl)

/-- The precomposition `Hom_ℤ(X₂,Ωˣ) →+ Hom_ℤ(X₁,Ωˣ)` induced by a morphism `h : X₁ ⟶ X₂` of
`Gal(K/k)`-modules. -/
noncomputable def e1aPrecomp (k Ω : Type) [Field k] [CharZero k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (X₁ X₂ : Rep.{0} SSGRoute.PTExt.Coeff (K ≃ₐ[k] K)) (h : X₁ ⟶ X₂) :
    Work.SSGRoute.homCoind k Ω K X₂ →+ Work.SSGRoute.homCoind k Ω K X₁ where
  toFun ψ := ψ.comp (Rep.Hom.hom h).toAddMonoidHom
  map_zero' := by ext v; rfl
  map_add' ψ ψ' := by ext v; rfl

/-- The map `H¹(Γ, Hom_ℤ(X₂,Ωˣ)) →+ H¹(Γ, Hom_ℤ(X₁,Ωˣ))` induced by a morphism `h : X₁ ⟶ X₂`
of `Gal(K/k)`-modules (precomposition with `h`).  Packaged with its instance arguments pinned, so
that the naturality statements about the `E1c` dictionary
(`Ext¹_G(X,Kˣ) ≅ H¹(Γ, Hom_ℤ(X,Ωˣ))`) can be written without `@`-applications. -/
noncomputable def e1aH1Map (k Ω : Type) [Field k] [CharZero k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (X₁ X₂ : Rep.{0} SSGRoute.PTExt.Coeff (K ≃ₐ[k] K)) (h : X₁ ⟶ X₂)
    (hf : Work.GroupCohomology.IsEquivariant (Ω ≃ₐ[k] Ω) (e1aPrecomp k Ω K X₁ X₂ h)) :
    @Work.AbsoluteKummer.H1 (Ω ≃ₐ[k] Ω) (Work.SSGRoute.homCoind k Ω K X₂) _ _
        (Work.SSGRoute.homCoind.instAddCommGroup X₂)
        (Work.SSGRoute.homCoind.instDistribMulActionAlgEquiv X₂) →+
      @Work.AbsoluteKummer.H1 (Ω ≃ₐ[k] Ω) (Work.SSGRoute.homCoind k Ω K X₁) _ _
        (Work.SSGRoute.homCoind.instAddCommGroup X₁)
        (Work.SSGRoute.homCoind.instDistribMulActionAlgEquiv X₁) :=
  Work.AbsoluteKummer.mapH1 (e1aPrecomp k Ω K X₁ X₂ h) hf

end

end Work.SSGRoute.PT
