import Mathlib
import Submission.Work.Frobenius.Pair

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `charPair σ.character ρ.character` is the dimension of `Hom_G(ρ, σ)`

The trace pairing `Work.Frobenius.charPair` is, by definition,

`charPair f g = |G|⁻¹ * ∑ x, f x * g x⁻¹`,

so `charPair σ.character ρ.character = |G|⁻¹ * ∑ x, χ_σ x * χ_ρ x⁻¹`.  Mathlib's
`Representation.card_inv_mul_sum_char_mul_char_eq_finrank` identifies this scalar product of
characters with the dimension of the space of `G`-equivariant maps `ρ → σ`.  Composing the two
gives the statement of the theorem below.
-/

@[expose] public section

noncomputable section

open Classical

namespace Work.Frobenius.Induction

/-- The bilinear trace pairing of the characters of two finite-dimensional complex
representations `ρ`, `σ` of a finite group is the dimension over `ℂ` of the space of
intertwining maps `ρ → σ`. -/
theorem charPair_eq_finrank_intertwiningMap {G : Type*} [Group G] [Fintype G]
    {V W : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    (ρ : Representation ℂ G V) (σ : Representation ℂ G W) :
    charPair σ.character ρ.character
      = (Module.finrank ℂ (Representation.IntertwiningMap ρ σ) : ℂ) := by
  rw [charPair_apply]
  exact Representation.card_inv_mul_sum_char_mul_char_eq_finrank ρ σ

end Work.Frobenius.Induction
