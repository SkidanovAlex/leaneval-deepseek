import Mathlib.Algebra.Field.ZMod
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal

namespace Commons.LinearAlgebra.Submodule

/-- No subspace `L'` of dimension `ℓ` can contain `W` and meet `L` in a hyperplane, when `W` and
`L` already have a codimension-`2` intersection inside `W`. -/
theorem card_neighbors_containing_eq_zero {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    [Finite V] (W L : Submodule (ZMod 2) V) (i ℓ : ℕ) (hW : Module.finrank (ZMod 2) W = i)
    (hL : Module.finrank (ZMod 2) L = ℓ)
    (hinf : Module.finrank (ZMod 2) ↥(W ⊓ L) + 2 ≤ i) :
    Nat.card {L' : Submodule (ZMod 2) V // Module.finrank (ZMod 2) L' = ℓ ∧
        Module.finrank (ZMod 2) ↥(L ⊓ L') = ℓ - 1 ∧ W ≤ L'} = 0 := by
  -- The defining type is empty: assume an `L'` and derive a dimension contradiction.
  rw [Nat.card_eq_zero]
  left
  refine ⟨fun L' => ?_⟩
  obtain ⟨hdimL', hdimInf, hWL'⟩ := L'.2
  -- Dimension formula for `W ⊔ L`.
  have h1 : Module.finrank (ZMod 2) ↥(W ⊔ L) + Module.finrank (ZMod 2) ↥(W ⊓ L) = i + ℓ := by
    rw [Submodule.finrank_sup_add_finrank_inf_eq, hW, hL]
  -- Dimension formula for `L ⊔ L'`.
  have h2 : Module.finrank (ZMod 2) ↥(L ⊔ (L' : Submodule (ZMod 2) V)) +
      Module.finrank (ZMod 2) ↥(L ⊓ (L' : Submodule (ZMod 2) V)) = ℓ + ℓ := by
    rw [Submodule.finrank_sup_add_finrank_inf_eq, hL, hdimL']
  -- Since `W ≤ L'`, we have `W ⊔ L ≤ L ⊔ L'`.
  have h3 : W ⊔ L ≤ L ⊔ (L' : Submodule (ZMod 2) V) := by
    apply sup_le
    · exact le_trans hWL' le_sup_right
    · exact le_sup_left
  have h4 : Module.finrank (ZMod 2) ↥(W ⊔ L) ≤
      Module.finrank (ZMod 2) ↥(L ⊔ (L' : Submodule (ZMod 2) V)) :=
    Submodule.finrank_mono h3
  -- `finrank (W ⊔ L) ≥ ℓ + 2` but `finrank (L ⊔ L') = ℓ + 1`: contradiction.
  omega

end Commons.LinearAlgebra.Submodule