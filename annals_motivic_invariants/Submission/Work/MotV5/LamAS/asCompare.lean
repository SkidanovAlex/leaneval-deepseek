import Mathlib
import Submission.Work.MotV5.LamAS.asPsi

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.MotV5.LamAS

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 400000

variable {𝕜 : Type} [Field 𝕜] [CharP 𝕜 5]

/-!
# The twisted Galois actions on `M = L(E)` agree up to conjugation by an `L`-automorphism

This file proves `asCompare` (chain statement (C3) of the Artin–Schreier LAM node):

> An `L`-automorphism `Θ` of `M = L(E)` carrying the first twist field `asF D f₁ f₂ g₁ τ₁ σS` into
> the second `asF D f₁ f₂ g₂ τ₂ σS` conjugates the first twisted Galois action `ψ₁` into the
> second `ψ₂`.

The proof rests on three elementary facts:

* `ψ_γ = σS^(χ γ) ∘ γ̃` acts on the constants `L ⊆ M` by `γ` (both for the first and the second
  twist), and the `L`-automorphism `Θ` fixes the constants: hence `Θ ψ₁` and `ψ₂ Θ` agree on `L`;
* `ψ₁` fixes the first twist field pointwise and `ψ₂` fixes the second, while `Θ` maps the first
  into the second: hence `Θ ψ₁` and `ψ₂ Θ` agree on `asF₁`;
* the first twist field together with the constants generates `M` (`hsup`), so two `K`-algebra
  automorphisms agreeing on `asF₁` and on the constants agree everywhere.

The formalisation packages the last two points as the statement that
`{z | Θ (ψ₁ z) = ψ₂ (Θ z)}` is an intermediate field containing `asF₁` and `asLImageM`, whence it
is `⊤` by `hsup`.
-/

/-- The twisted Galois action `ψ_γ = σS^(χ γ) ∘ γ̃` of the class of `g` acts on the constants
`L` of `M = L(E)` through `γ`: `ψ_γ (algebraMap l) = algebraMap (γ l)`. -/
theorem asPsi_algebraMap (D : Work.MotV.KleinData 𝕜) (f₁ f₂ : RatFunc 𝕜) (g : RatFunc 𝕜)
    (σS' : asML D f₁ f₂ ≃ₐ[↥(asL2 (𝕜 := 𝕜) f₁ f₂)] asML D f₁ f₂)
    (W : ↥(asL2 (𝕜 := 𝕜) f₁ f₂))
    (hW : W ^ 5 - W = algebraMap (RatFunc 𝕜) ↥(asL2 (𝕜 := 𝕜) f₁ f₂) g)
    (γ : ↥(asL2 (𝕜 := 𝕜) f₁ f₂) ≃ₐ[RatFunc 𝕜] ↥(asL2 (𝕜 := 𝕜) f₁ f₂))
    (l : ↥(asL2 (𝕜 := 𝕜) f₁ f₂)) :
    asPsi D f₁ f₂ g σS' W hW γ (algebraMap ↥(asL2 (𝕜 := 𝕜) f₁ f₂) (asML D f₁ f₂) l) =
      algebraMap ↥(asL2 (𝕜 := 𝕜) f₁ f₂) (asML D f₁ f₂) (γ l) := by
  rw [asPsi, AlgEquiv.mul_apply, AlgEquiv.restrictScalars_apply, asCoeff_algebraMap]
  exact (σS' ^ _).commutes (γ l)

/-- The twisted Galois action fixes the base field `K = RatFunc 𝕜` pointwise. -/
theorem asPsi_algebraMap_K (D : Work.MotV.KleinData 𝕜) (f₁ f₂ : RatFunc 𝕜) (g : RatFunc 𝕜)
    (σS' : asML D f₁ f₂ ≃ₐ[↥(asL2 (𝕜 := 𝕜) f₁ f₂)] asML D f₁ f₂)
    (W : ↥(asL2 (𝕜 := 𝕜) f₁ f₂))
    (hW : W ^ 5 - W = algebraMap (RatFunc 𝕜) ↥(asL2 (𝕜 := 𝕜) f₁ f₂) g)
    (γ : ↥(asL2 (𝕜 := 𝕜) f₁ f₂) ≃ₐ[RatFunc 𝕜] ↥(asL2 (𝕜 := 𝕜) f₁ f₂))
    (c : RatFunc 𝕜) :
    asPsi D f₁ f₂ g σS' W hW γ (algebraMap (RatFunc 𝕜) (asML D f₁ f₂) c) =
      algebraMap (RatFunc 𝕜) (asML D f₁ f₂) c := by
  rw [IsScalarTower.algebraMap_apply (RatFunc 𝕜) ↥(asL2 (𝕜 := 𝕜) f₁ f₂) (asML D f₁ f₂) c]
  rw [asPsi_algebraMap]
  rw [AlgEquiv.commutes γ c]

/-- An `L`-algebra automorphism of `M = L(E)` fixes the base field `K = RatFunc 𝕜` pointwise. -/
theorem asML_algEquiv_algebraMap_K (D : Work.MotV.KleinData 𝕜) (f₁ f₂ : RatFunc 𝕜)
    (Θ : asML D f₁ f₂ ≃ₐ[↥(asL2 (𝕜 := 𝕜) f₁ f₂)] asML D f₁ f₂) (c : RatFunc 𝕜) :
    Θ (algebraMap (RatFunc 𝕜) (asML D f₁ f₂) c) =
      algebraMap (RatFunc 𝕜) (asML D f₁ f₂) c := by
  rw [IsScalarTower.algebraMap_apply (RatFunc 𝕜) ↥(asL2 (𝕜 := 𝕜) f₁ f₂) (asML D f₁ f₂) c]
  rw [AlgEquiv.commutes Θ (algebraMap (RatFunc 𝕜) ↥(asL2 (𝕜 := 𝕜) f₁ f₂) c)]

/-- An `L`-automorphism of `M = L(E)` carrying the first twist field into the second conjugates the first twisted Galois action `ψ_γ = σS^(χ₁ γ) ∘ γ̃` into the second. -/
theorem asCompare (𝕜 : Type) [Field 𝕜] [CharP 𝕜 5] (D : Work.MotV.KleinData 𝕜)
    (hD : Work.MotV5.KleinData.ASGood D) (f₁ f₂ g₁ g₂ : RatFunc 𝕜)
    (τ₁ τ₂ : Work.MotV.Om D ≃ₐ[RatFunc 𝕜] Work.MotV.Om D)
    (σS : Work.MotV.Om D ≃ₐ[Work.MotV.Kb 𝕜] Work.MotV.Om D)
    (σS' : Work.MotV5.LamAS.asML D f₁ f₂ ≃ₐ[↥(Work.MotV5.LamAS.asL2 (𝕜 := 𝕜) f₁ f₂)]
      Work.MotV5.LamAS.asML D f₁ f₂)
    (W₁ W₂ : ↥(Work.MotV5.LamAS.asL2 (𝕜 := 𝕜) f₁ f₂))
    (hW₁ : W₁ ^ 5 - W₁ = algebraMap (RatFunc 𝕜) ↥(Work.MotV5.LamAS.asL2 (𝕜 := 𝕜) f₁ f₂) g₁)
    (hW₂ : W₂ ^ 5 - W₂ = algebraMap (RatFunc 𝕜) ↥(Work.MotV5.LamAS.asL2 (𝕜 := 𝕜) f₁ f₂) g₂)
    (γ : ↥(Work.MotV5.LamAS.asL2 (𝕜 := 𝕜) f₁ f₂) ≃ₐ[RatFunc 𝕜]
      ↥(Work.MotV5.LamAS.asL2 (𝕜 := 𝕜) f₁ f₂))
    (Θ : Work.MotV5.LamAS.asML D f₁ f₂ ≃ₐ[↥(Work.MotV5.LamAS.asL2 (𝕜 := 𝕜) f₁ f₂)]
      Work.MotV5.LamAS.asML D f₁ f₂)
    (hΘ : ∀ x ∈ Work.MotV5.LamAS.asF D f₁ f₂ g₁ τ₁ σS,
      Θ x ∈ Work.MotV5.LamAS.asF D f₁ f₂ g₂ τ₂ σS)
    (hsup : Work.MotV5.LamAS.asF D f₁ f₂ g₁ τ₁ σS ⊔ Work.MotV5.LamAS.asLImageM D f₁ f₂ = ⊤)
    (hfix₁ : ∀ x ∈ Work.MotV5.LamAS.asF D f₁ f₂ g₁ τ₁ σS,
      Work.MotV5.LamAS.asPsi D f₁ f₂ g₁ σS' W₁ hW₁ γ x = x)
    (hfix₂ : ∀ x ∈ Work.MotV5.LamAS.asF D f₁ f₂ g₂ τ₂ σS,
      Work.MotV5.LamAS.asPsi D f₁ f₂ g₂ σS' W₂ hW₂ γ x = x) :
    Θ.restrictScalars (RatFunc 𝕜) * (Work.MotV5.LamAS.asPsi D f₁ f₂ g₁ σS' W₁ hW₁ γ) =
      (Work.MotV5.LamAS.asPsi D f₁ f₂ g₂ σS' W₂ hW₂ γ) * Θ.restrictScalars (RatFunc 𝕜) := by
  -- The two compositions agree pointwise.
  have hpt : ∀ x : asML D f₁ f₂,
      Θ (asPsi D f₁ f₂ g₁ σS' W₁ hW₁ γ x) = asPsi D f₁ f₂ g₂ σS' W₂ hW₂ γ (Θ x) := by
    intro x
    -- The equalizer of the two `K`-algebra homs `Θ ∘ ψ₁` and `ψ₂ ∘ Θ`, as an intermediate field.
    let S : IntermediateField (RatFunc 𝕜) (asML D f₁ f₂) :=
      { carrier := {z | Θ (asPsi D f₁ f₂ g₁ σS' W₁ hW₁ γ z) =
                          asPsi D f₁ f₂ g₂ σS' W₂ hW₂ γ (Θ z)}
        zero_mem' := by simp only [Set.mem_ofPred_eq, map_zero]
        one_mem' := by simp only [Set.mem_ofPred_eq, map_one]
        add_mem' := by
          intro a b ha hb
          simp only [Set.mem_ofPred_eq] at ha hb ⊢
          simp only [map_add, ha, hb]
        mul_mem' := by
          intro a b ha hb
          simp only [Set.mem_ofPred_eq] at ha hb ⊢
          simp only [map_mul, ha, hb]
        inv_mem' := by
          intro a ha
          simp only [Set.mem_ofPred_eq] at ha ⊢
          simp only [map_inv₀, ha]
        algebraMap_mem' := by
          intro c
          simp only [Set.mem_ofPred_eq]
          rw [asPsi_algebraMap_K, asML_algEquiv_algebraMap_K, asPsi_algebraMap_K] }
    -- `ψ₁` and `ψ₂` fix their twist fields, and `Θ` carries the first into the second.
    have h1 : asF D f₁ f₂ g₁ τ₁ σS ≤ S := by
      intro z hz
      change Θ (asPsi D f₁ f₂ g₁ σS' W₁ hW₁ γ z) =
        asPsi D f₁ f₂ g₂ σS' W₂ hW₂ γ (Θ z)
      rw [hfix₁ z hz]
      exact (hfix₂ (Θ z) (hΘ z hz)).symm
    -- Both twisted actions act on the constants `L` by `γ`; `Θ` fixes them.
    have h2 : asLImageM D f₁ f₂ ≤ S := by
      intro z hz
      rw [asLImageM, AlgHom.mem_fieldRange] at hz
      obtain ⟨l, rfl⟩ := hz
      change Θ (asPsi D f₁ f₂ g₁ σS' W₁ hW₁ γ
          (algebraMap ↥(asL2 (𝕜 := 𝕜) f₁ f₂) (asML D f₁ f₂) l)) =
        asPsi D f₁ f₂ g₂ σS' W₂ hW₂ γ
          (Θ (algebraMap ↥(asL2 (𝕜 := 𝕜) f₁ f₂) (asML D f₁ f₂) l))
      have hψ₁ : asPsi D f₁ f₂ g₁ σS' W₁ hW₁ γ
          (algebraMap ↥(asL2 (𝕜 := 𝕜) f₁ f₂) (asML D f₁ f₂) l) =
          algebraMap ↥(asL2 (𝕜 := 𝕜) f₁ f₂) (asML D f₁ f₂) (γ l) :=
        asPsi_algebraMap D f₁ f₂ g₁ σS' W₁ hW₁ γ l
      have hψ₂ : asPsi D f₁ f₂ g₂ σS' W₂ hW₂ γ
          (algebraMap ↥(asL2 (𝕜 := 𝕜) f₁ f₂) (asML D f₁ f₂) l) =
          algebraMap ↥(asL2 (𝕜 := 𝕜) f₁ f₂) (asML D f₁ f₂) (γ l) :=
        asPsi_algebraMap D f₁ f₂ g₂ σS' W₂ hW₂ γ l
      have hT : Θ (algebraMap ↥(asL2 (𝕜 := 𝕜) f₁ f₂) (asML D f₁ f₂) l) =
          algebraMap ↥(asL2 (𝕜 := 𝕜) f₁ f₂) (asML D f₁ f₂) l :=
        AlgEquiv.commutes Θ l
      have hT' : Θ (algebraMap ↥(asL2 (𝕜 := 𝕜) f₁ f₂) (asML D f₁ f₂) (γ l)) =
          algebraMap ↥(asL2 (𝕜 := 𝕜) f₁ f₂) (asML D f₁ f₂) (γ l) :=
        AlgEquiv.commutes Θ (γ l)
      rw [hψ₁, hT, hψ₂, hT']
    -- `M` is generated by the first twist field together with the constants.
    have htop : (⊤ : IntermediateField (RatFunc 𝕜) (asML D f₁ f₂)) ≤ S := by
      rw [← hsup]
      exact sup_le h1 h2
    exact htop trivial
  refine AlgEquiv.ext (fun x => ?_)
  simpa only [AlgEquiv.mul_apply, AlgEquiv.restrictScalars_apply] using hpt x

end Work.MotV5.LamAS
