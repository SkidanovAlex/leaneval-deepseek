import Mathlib
import Submission.Work.Frobenius.Char

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# The principal character is an irreducible character

The constant function `1 : G → ℂ` is the character of the one-dimensional trivial complex
representation of `G`.  That representation is irreducible because its subrepresentations are
the `ℂ`-submodules of `ℂ` — of which there are only `⊥` and `⊤`, as `ℂ` is a simple module over
itself — and because the trivial representation is nontrivial.  Hence `1 ∈ Irr G`.
-/

namespace Work.Frobenius.Irr

variable {G : Type*} [Group G]

/-- The trivial complex representation of `G` on `ℂ` is irreducible: a subrepresentation of it
is a `ℂ`-submodule of `ℂ`, hence `⊥` or `⊤`. -/
theorem isIrreducible_trivial :
    Representation.IsIrreducible (Representation.trivial ℂ G ℂ) := by
  -- `⊥ ≠ ⊤` for subrepresentations, since already `⊥ ≠ ⊤` for their underlying submodules
  have hn : Nontrivial (Subrepresentation (Representation.trivial ℂ G ℂ)) :=
    ⟨⟨⊥, ⊤, fun h => by
      have h2 : (⊥ : Submodule ℂ ℂ) = ⊤ := congrArg Subrepresentation.toSubmodule h
      exact IsSimpleOrder.bot_ne_top h2⟩⟩
  refine IsSimpleOrder.of_forall_eq_top fun S hS => ?_
  rcases IsSimpleOrder.eq_bot_or_eq_top S.toSubmodule with h | h
  · exact absurd (by apply Subrepresentation.toSubmodule_injective; rw [h]; rfl) hS
  · exact (by apply Subrepresentation.toSubmodule_injective; rw [h]; rfl)

/-- The character of the trivial representation of `G` on `ℂ` is the constant function `1`. -/
theorem character_trivial :
    (Representation.trivial ℂ G ℂ).character = (1 : G → ℂ) := by
  ext g
  have h1 : (Representation.trivial ℂ G ℂ) g = 1 := rfl
  rw [Representation.character, h1, LinearMap.trace_one]
  simp

theorem isIrr_one {G : Type*} [Group G] : (1 : G → ℂ) ∈ Irr G := by
  refine ⟨{ V := ℂ, ρ := Representation.trivial ℂ G ℂ, irred := isIrreducible_trivial }, ?_⟩
  exact character_trivial

end Work.Frobenius.Irr
