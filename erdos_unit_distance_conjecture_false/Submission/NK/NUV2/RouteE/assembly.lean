import Mathlib
import Submission.NK.LocalArtin.Basic
import Submission.NK.LocalCFT.Reduction.nonempty_artinReciprocity_of_reciprocityLaw
import Submission.NK.LocalReciprocityLubinTate.Unramified.nonempty_kernelCondition_of_reciprocityLaw

/-!
# The final assembly: a compatible family of level maps gives the reciprocity law

Suppose that at every finite abelian level `L` of `F^{ab}` one has a homomorphism
`θ_L : Fˣ →* Gal(L/F)` whose kernel is the norm group `N_{L/F} Lˣ`, which is surjective, and which
is compatible with restriction between nested levels.  Then the level isomorphisms
`Fˣ ⧸ N_{L/F} Lˣ ≃* Gal(L/F)` induced by `θ_L` are automatically compatible, i.e. they form a
`NK.LocalCFT.ReciprocityLaw F F'`, and hence (by the on-disk bridge
`NK.LocalReciprocityLubinTate.Unramified.nonempty_kernelCondition_of_reciprocityLaw`) the local
reciprocity law in kernel form `NK.LocalArtin.KernelCondition F F'`.

This isolates the *assembly* step L8 of the character-formula route: it needs only the per-level
kernel condition (L7) and the compatibility of the level maps (L5).
-/

open scoped Classical

set_option backward.isDefEq.respectTransparency false

namespace NK.NUV2.RouteE

noncomputable section

variable {F : Type} {F' : Type} [Field F] [Field F'] [Algebra F F'] [IsGalois F F']

/-- **L8: a compatible family of level maps produces the reciprocity law.** -/
theorem nonempty_reciprocityLaw_of_levelMaps
    (θ : ∀ (L : IntermediateField F (NK.LocalReciprocity.maxAbelianSubext F F'))
        [FiniteDimensional F L] [Normal F L]
        (_ : ∀ σ τ : ↥L ≃ₐ[F] ↥L, σ * τ = τ * σ), Fˣ →* (↥L ≃ₐ[F] ↥L))
    (hker : ∀ (L : IntermediateField F (NK.LocalReciprocity.maxAbelianSubext F F'))
        [FiniteDimensional F L] [Normal F L]
        (hcomm : ∀ σ τ : ↥L ≃ₐ[F] ↥L, σ * τ = τ * σ),
        MonoidHom.ker (θ L hcomm) = NK.LocalReciprocity.normGroup F ↥L)
    (hsurj : ∀ (L : IntermediateField F (NK.LocalReciprocity.maxAbelianSubext F F'))
        [FiniteDimensional F L] [Normal F L]
        (hcomm : ∀ σ τ : ↥L ≃ₐ[F] ↥L, σ * τ = τ * σ),
        Function.Surjective (θ L hcomm))
    (hcompat : ∀ (L₁ L₂ : IntermediateField F (NK.LocalReciprocity.maxAbelianSubext F F'))
        [FiniteDimensional F L₁] [Normal F L₁] [FiniteDimensional F L₂] [Normal F L₂]
        (h₁ : ∀ σ τ : ↥L₁ ≃ₐ[F] ↥L₁, σ * τ = τ * σ)
        (h₂ : ∀ σ τ : ↥L₂ ≃ₐ[F] ↥L₂, σ * τ = τ * σ) (h : L₂ ≤ L₁) (a : Fˣ),
        NK.LocalCFT.levelRestrictLe h (θ L₁ h₁ a) = θ L₂ h₂ a) :
    Nonempty (NK.LocalCFT.ReciprocityLaw F F') := by
  classical
  -- the induced level isomorphism `Fˣ ⧸ N(L) ≃* Gal(L/F)`
  have key : ∀ (L : IntermediateField F (NK.LocalReciprocity.maxAbelianSubext F F'))
      [FiniteDimensional F L] [Normal F L]
      (hcomm : ∀ σ τ : ↥L ≃ₐ[F] ↥L, σ * τ = τ * σ),
      ∃ (e : (Fˣ ⧸ NK.LocalReciprocity.normGroup F ↥L) ≃* (↥L ≃ₐ[F] ↥L)),
        ∀ x : Fˣ, e (QuotientGroup.mk x) = θ L hcomm x := by
    intro L _ _ hcomm
    refine ⟨MulEquiv.ofBijective
      (QuotientGroup.lift (NK.LocalReciprocity.normGroup F ↥L) (θ L hcomm)
        (by rw [hker L hcomm])) ⟨?_, ?_⟩, ?_⟩
    · -- injectivity
      intro a b hab
      obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective a
      obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective b
      rw [QuotientGroup.lift_mk', QuotientGroup.lift_mk'] at hab
      rw [QuotientGroup.eq]
      rw [← hker L hcomm]
      refine MonoidHom.mem_ker.mpr ?_
      rw [map_mul, map_inv, hab]
      simp
    · -- surjectivity
      intro g
      obtain ⟨x, hx⟩ := hsurj L hcomm g
      exact ⟨QuotientGroup.mk x, by rw [QuotientGroup.lift_mk']; exact hx⟩
    · -- the value on representatives
      intro x
      rw [MulEquiv.ofBijective_apply, QuotientGroup.lift_mk']
  refine ⟨{ levelEquiv := fun L _ _ hcomm => (key L hcomm).choose
            compat := fun L₁ L₂ _ _ _ _ h₁ h₂ h x => ?_ }⟩
  have h2x : QuotientGroup.map (NK.LocalReciprocity.normGroup F ↥L₁)
        (NK.LocalReciprocity.normGroup F ↥L₂) (MonoidHom.id Fˣ)
        (NK.LocalCFT.normGroup_le_of_le h) (QuotientGroup.mk x) = QuotientGroup.mk x :=
    QuotientGroup.map_mk _ _ _ _ x
  rw [h2x, (key L₁ h₁).choose_spec x, (key L₂ h₂).choose_spec x]
  exact hcompat L₁ L₂ h₁ h₂ h x

/-- **The local reciprocity law in kernel form from a compatible family of level maps**: the
composition of `nonempty_reciprocityLaw_of_levelMaps` with the on-disk bridge
`nonempty_kernelCondition_of_reciprocityLaw`. -/
theorem nonempty_kernelCondition_of_levelMaps
    (θ : ∀ (L : IntermediateField F (NK.LocalReciprocity.maxAbelianSubext F F'))
        [FiniteDimensional F L] [Normal F L]
        (_ : ∀ σ τ : ↥L ≃ₐ[F] ↥L, σ * τ = τ * σ), Fˣ →* (↥L ≃ₐ[F] ↥L))
    (hker : ∀ (L : IntermediateField F (NK.LocalReciprocity.maxAbelianSubext F F'))
        [FiniteDimensional F L] [Normal F L]
        (hcomm : ∀ σ τ : ↥L ≃ₐ[F] ↥L, σ * τ = τ * σ),
        MonoidHom.ker (θ L hcomm) = NK.LocalReciprocity.normGroup F ↥L)
    (hsurj : ∀ (L : IntermediateField F (NK.LocalReciprocity.maxAbelianSubext F F'))
        [FiniteDimensional F L] [Normal F L]
        (hcomm : ∀ σ τ : ↥L ≃ₐ[F] ↥L, σ * τ = τ * σ),
        Function.Surjective (θ L hcomm))
    (hcompat : ∀ (L₁ L₂ : IntermediateField F (NK.LocalReciprocity.maxAbelianSubext F F'))
        [FiniteDimensional F L₁] [Normal F L₁] [FiniteDimensional F L₂] [Normal F L₂]
        (h₁ : ∀ σ τ : ↥L₁ ≃ₐ[F] ↥L₁, σ * τ = τ * σ)
        (h₂ : ∀ σ τ : ↥L₂ ≃ₐ[F] ↥L₂, σ * τ = τ * σ) (h : L₂ ≤ L₁) (a : Fˣ),
        NK.LocalCFT.levelRestrictLe h (θ L₁ h₁ a) = θ L₂ h₂ a) :
    Nonempty (NK.LocalArtin.KernelCondition F F') := by
  obtain ⟨hlaw⟩ := nonempty_reciprocityLaw_of_levelMaps θ hker hsurj hcompat
  exact NK.LocalReciprocityLubinTate.Unramified.nonempty_kernelCondition_of_reciprocityLaw hlaw

end

end NK.NUV2.RouteE
