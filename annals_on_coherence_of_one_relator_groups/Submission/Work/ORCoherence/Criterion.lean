import Submission.Work.ORCoherence.Imports
import Mathlib.Algebra.Homology.ShortComplex.Exact

set_option autoImplicit false

open CategoryTheory Limits
open scoped TensorProduct

namespace Work.ORCoherence

universe u v

/-- The hypothesis that the right `R`-module `S` has weak dimension at most one, in the form in
which it is used in the proof of JL Corollary 3.3: for every exact sequence of left `R`-modules
`0 → P₂ → P₁ → P₀ → M → 0` with `P₀`, `P₁`, `P₂` projective, the induced map
`S ⊗[R] P₂ → S ⊗[R] P₁` is injective.  This is `Tor₂^R(S, M) = 0` for every `M`. -/
def TorTwoVanishes {R : Type u} {S : Type v} [Ring R] [Ring S] (f : R →+* S) : Prop :=
  ∀ (M P₂ P₁ P₀ : ModuleCat.{u} R) [Projective P₂] [Projective P₁] [Projective P₀]
    (d₂ : P₂ ⟶ P₁) (d₁ : P₁ ⟶ P₀) (π : P₀ ⟶ M) (h : d₂ ≫ d₁ = 0) (h' : d₁ ≫ π = 0),
    Mono d₂ → (ShortComplex.mk d₂ d₁ h).Exact → (ShortComplex.mk d₁ π h').Exact → Epi π →
    Function.Injective ⇑(Balanced.map f d₂.hom)

end Work.ORCoherence
