import Mathlib.Data.ZMod.Defs
import Mathlib.GroupTheory.FreeGroup.Basic
import Mathlib.GroupTheory.QuotientGroup.Defs
import Mathlib.LinearAlgebra.TensorPower.Basic
import Submission.Work.CohomologicalShrinking.Functorial
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

attribute [local instance] Classical.decEq

namespace Work.CohomologicalShrinking

set_option maxHeartbeats 800000

open scoped TensorProduct

universe u v w

variable {p : ℕ}

/-- **Proposition 5 of Schmidt–Wingberg, as structured data for a fixed `τ = (i,j)`.**

For every rank `d` we are given the canonical `G`-equivariant `𝔽_p`-linear surjection
`θ_τ(d) : (F(d)/F(d)^2)^{⊗j} ↠ E(d,τ)` of the paper, together with the naturality of this
family in `d` along surjective `G`-operator homomorphisms `F(m) → F(n)`:
`θ_τ(n) ∘ (ψ̄^{⊗j}) = ψ_* ∘ θ_τ(m)`.

(Only surjective operator homomorphisms occur in the shrinking procedure; the naturality is
therefore stated for those.) -/
structure Prop5Data (p : ℕ) [NeZero p] (G : Type*) [Group G] (i j : ℕ) where
  /-- The map `θ_τ(d) : (F(d)/F(d)^2)^{⊗j} → E(d,τ)`. -/
  θ : ∀ d : ℕ, (⨂[ZMod p]^j (squareQuotient p G d)) →ₗ[ZMod p] E p G d i j
  /-- `θ_τ(d)` is `G`-equivariant. -/
  θ_smul : ∀ (d : ℕ) (g : G) (x : ⨂[ZMod p]^j (squareQuotient p G d)),
    θ d (g • x) = g • θ d x
  /-- `θ_τ(d)` is surjective. -/
  θ_surjective : ∀ d : ℕ, Function.Surjective (θ d)
  /-- Naturality of `θ_τ` in the rank: for a surjective `G`-operator homomorphism
  `ψ : F(m) → F(n)` the square
  `θ_τ(n) ∘ (ψ̄^{⊗j}) = ψ_* ∘ θ_τ(m)` commutes. -/
  θ_natural : ∀ ⦃m n : ℕ⦄
      (ψ : Work.Shrinking.freeOperatorGroup G m →* Work.Shrinking.freeOperatorGroup G n)
      (hψ : Function.Surjective ψ)
      (hψG : ∀ (g : G) (y : Work.Shrinking.freeOperatorGroup G m), ψ (g • y) = g • ψ y),
    (θ n).comp (PiTensorProduct.map (fun _ : Fin j => quotMapLin p G ψ hψ))
      = (gradedMapLin p ψ hψ i j).comp (θ m)

end Work.CohomologicalShrinking
