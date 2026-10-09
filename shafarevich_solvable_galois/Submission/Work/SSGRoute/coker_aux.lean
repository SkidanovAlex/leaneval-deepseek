import Mathlib
import Submission.Work.SSGRoute.Interfaces
import Submission.Work.SSGRoute.naturality_gluing
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Auxiliary lemmas of the `coker_obstruction` node, kept in a separate module

These are the two place-monotonicity facts and the `x = 0` case of `Work.SSGRoute.coker_obstruction`.
They are stated here (rather than in `coker_obstruction.lean`) so that the *parallel* development
`Submission/Work/SSGRoute/coker_obstruction_pt.lean` -- which re-proves the same statement under a
fresh name and needs exactly these three lemmas -- can import them from this module instead of
importing `Submission.Work.SSGRoute.coker_obstruction`.  That import is the only reason the two
modules cannot use each other's proofs: `coker_obstruction_pt` imports `coker_obstruction`, so the
reverse import is impossible.  Breaking it makes it possible to prove the requested statement
`Work.SSGRoute.coker_obstruction` directly by `exact Work.SSGRoute.coker_obstruction_pt ...` once
that lane is `sorry`-free, instead of duplicating its (long) assembly.

Nothing else changes: the names stay in the namespace `Work.SSGRoute`, and
`Submission.Work.SSGRoute.coker_obstruction` re-exports them by importing this module.
-/

open scoped TensorProduct

namespace Work.SSGRoute

section Monotone

variable {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω]

/-- Ramification is monotone: a place ramified in a subextension is ramified in every
larger (normal) extension. -/
theorem isRamifiedIn_of_le {N₁ N₂ : IntermediateField k Ω} [Normal k N₁] [Normal k N₂]
    (h : N₁ ≤ N₂) {B : ValuationSubring Ω} (hb : SSGRoute.IsRamifiedIn k N₁ B) :
    SSGRoute.IsRamifiedIn k N₂ B := by
  obtain ⟨σ, hσ, hσfix⟩ := hb
  exact ⟨σ, hσ, fun hmem => hσfix (IntermediateField.fixingSubgroup_le h hmem)⟩

/-- Complete splitting is monotone: a place splitting completely in a larger extension splits
completely in every subextension, i.e. `cs(N₁) ⊆ cs(N₂)` for `N₁ ≤ N₂`. -/
theorem isSplitIn_of_le {N₁ N₂ : IntermediateField k Ω} [Normal k N₁] [Normal k N₂]
    (h : N₁ ≤ N₂) {B : ValuationSubring Ω} (hb : SSGRoute.IsSplitIn k N₂ B) :
    SSGRoute.IsSplitIn k N₁ B :=
  fun σ hσ => IntermediateField.fixingSubgroup_le h (hb hσ)

end Monotone


/-- **The `x = 0` case of `coker_obstruction`.**  If the level-`N` local data `(α, β)` glues (there
is a global cocycle `ε₀` whose local defects against `α` and `β` are coboundaries and which is
unramified outside `S ∪ cs(N)`), then `coker_obstruction` holds with the explicit witness `x := 0`:
the hypothesis `(groupHomology.map q F 1).hom 0 = 0` is automatic and `ε := f ∘ ε₀` is supplied by
`Work.SSGRoute.naturality_gluing`. -/
theorem coker_obstruction_of_level_gluing (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k]
    [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
    (K N : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    [FiniteDimensional k N] [IsGalois k N] (hKN : K ≤ N)
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
    (E T : Type) [AddCommGroup E] [Module (ZMod p) E] [DistribMulAction (K ≃ₐ[k] K) E]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E] [Finite E]
    [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction (K ≃ₐ[k] K) T]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T]
    (hT : SSGRoute.IsCyclotomicDual p (T := T) (SSGRoute.res k K) ζ)
    (πN : (N ≃ₐ[k] N) →* (K ≃ₐ[k] K))
    (hπN : ∀ σ : Ω ≃ₐ[k] Ω, πN (SSGRoute.res k N σ) = SSGRoute.res k K σ)
    (S : Finset (ValuationSubring Ω)) (hSfin : ∀ A ∈ S, SSGRoute.IsFinPlace k A)
    (hSdisj : ∀ A ∈ S, ∀ B ∈ S, SSGRoute.IsConjPlace k A B → A = B)
    (hSram : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
      (SSGRoute.IsRamifiedIn k N B ∨ B.valuation (p : Ω) < 1) → ∃ A ∈ S, SSGRoute.IsConjPlace k A B)
    (C : Finset (Ω ≃ₐ[k] Ω)) (hCinv : ∀ c ∈ C, c ^ 2 = 1)
    (hC : ∀ c : Ω ≃ₐ[k] Ω, c ^ 2 = 1 → c ≠ 1 → ∃ c₀ ∈ C, ∃ σ : Ω ≃ₐ[k] Ω, c = σ * c₀ * σ⁻¹)
    (hCdisj : ∀ c ∈ C, ∀ c' ∈ C, (∃ σ : Ω ≃ₐ[k] Ω, c' = σ * c * σ⁻¹) → c = c')
    (α : ValuationSubring Ω → (Ω ≃ₐ[k] Ω) → E)
    (hα : ∀ A ∈ S, SSGRoute.IsCocycleOn (SSGRoute.res k K) (SSGRoute.decomp k A) (α A) ∧
      SSGRoute.IsLocConstOn (SSGRoute.decomp k A) (α A))
    (β : (Ω ≃ₐ[k] Ω) → (Ω ≃ₐ[k] Ω) → E)
    (hβ : ∀ c ∈ C, SSGRoute.IsCocycleOn (SSGRoute.res k K) (Subgroup.zpowers c) (β c))
    (hglue : ∃ ε₀ : (Ω ≃ₐ[k] Ω) → E,
      SSGRoute.IsCocycleOn (SSGRoute.res k K) ⊤ ε₀ ∧ SSGRoute.IsLocConstOn ⊤ ε₀ ∧
      (∀ A ∈ S, SSGRoute.IsCoboundaryOn (SSGRoute.res k K) (SSGRoute.decomp k A)
        (fun σ => ε₀ σ - α A σ)) ∧
      (∀ c ∈ C, SSGRoute.IsCoboundaryOn (SSGRoute.res k K) (Subgroup.zpowers c)
        (fun σ => ε₀ σ - β c σ)) ∧
      ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
        (∀ A ∈ S, ¬ SSGRoute.IsConjPlace k A B) → ¬ SSGRoute.IsSplitIn k N B →
        ∀ σ : Ω ≃ₐ[k] Ω, SSGRoute.IsInertia k B σ → ε₀ σ = 0) :
    ∃ x : groupHomology.H1 (Rep.res πN
        (Rep.of (Representation.ofDistribMulAction (ZMod p) (K ≃ₐ[k] K) (E ⊗[ZMod p] T)))),
      ∀ (N₂ : IntermediateField k Ω) [FiniteDimensional k N₂] [IsGalois k N₂],
        K ≤ N₂ → N₂ ≤ N →
        ∀ (q : (N ≃ₐ[k] N) →* (N₂ ≃ₐ[k] N₂)),
        (∀ σ : Ω ≃ₐ[k] Ω, q (SSGRoute.res k N σ) = SSGRoute.res k N₂ σ) →
        ∀ (π₂ : (N₂ ≃ₐ[k] N₂) →* (K ≃ₐ[k] K)),
        (∀ σ : Ω ≃ₐ[k] Ω, π₂ (SSGRoute.res k N₂ σ) = SSGRoute.res k K σ) →
        ∀ (E₂ : Type) [AddCommGroup E₂] [Module (ZMod p) E₂] [DistribMulAction (K ≃ₐ[k] K) E₂]
          [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E₂]
          (f : E →ₗ[ZMod p] E₂), (∀ (g : K ≃ₐ[k] K) (e : E), f (g • e) = g • f e) →
        ∀ (F : Rep.res πN
              (Rep.of (Representation.ofDistribMulAction (ZMod p) (K ≃ₐ[k] K) (E ⊗[ZMod p] T))) ⟶
            Rep.res q (Rep.res π₂
              (Rep.of (Representation.ofDistribMulAction (ZMod p) (K ≃ₐ[k] K) (E₂ ⊗[ZMod p] T))))),
        (∀ z : E ⊗[ZMod p] T, F.hom z = f.rTensor T z) →
        (groupHomology.map q F 1).hom x = 0 →
        ∃ ε : (Ω ≃ₐ[k] Ω) → E₂,
          SSGRoute.IsCocycleOn (SSGRoute.res k K) ⊤ ε ∧ SSGRoute.IsLocConstOn ⊤ ε ∧
          (∀ A ∈ S, SSGRoute.IsCoboundaryOn (SSGRoute.res k K) (SSGRoute.decomp k A)
            (fun σ => ε σ - f (α A σ))) ∧
          (∀ c ∈ C, SSGRoute.IsCoboundaryOn (SSGRoute.res k K) (Subgroup.zpowers c)
            (fun σ => ε σ - f (β c σ))) ∧
          ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
            (∀ A ∈ S, ¬ SSGRoute.IsConjPlace k A B) → ¬ SSGRoute.IsSplitIn k N₂ B →
            ∀ σ : Ω ≃ₐ[k] Ω, SSGRoute.IsInertia k B σ → ε σ = 0 := by
  refine ⟨0, ?_⟩
  intro N₂ _ _ hKN₂ hN₂N q _ π₂ _ E₂ _ _ _ _ f hf _ _ _
  exact Work.SSGRoute.naturality_gluing p k Ω K N N₂ hKN₂ hN₂N E S C α β hglue E₂ f hf


end Work.SSGRoute
