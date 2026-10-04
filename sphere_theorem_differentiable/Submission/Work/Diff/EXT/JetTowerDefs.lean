import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Divisibility of a function on a slab by powers of the time coordinate

The single definition `Work.Diff.EXT.IsTowerInf` used by the two-sided extension lemma
`Work.Diff.EXT.twoSided_of_within`: a function `G` on a slab `s ⊆ ℝ × E` is divisible by every
power `z ↦ z.1 ^ N` of the time coordinate, with a smooth quotient on `s`.
-/

namespace Work.Diff.EXT

open Set
open scoped ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z]

/-- `G` is divisible on `s` by `z ↦ z.1 ^ N` for every `N`, with a `C^∞` quotient on `s`. -/
def IsTowerInf (s : Set (ℝ × E)) (G : ℝ × E → Z) : Prop :=
  ∀ N : ℕ, ∃ Ψ : ℝ × E → Z, ContDiffOn ℝ (⊤ : ℕ∞) Ψ s ∧ ∀ z ∈ s, G z = z.1 ^ N • Ψ z

end Work.Diff.EXT
