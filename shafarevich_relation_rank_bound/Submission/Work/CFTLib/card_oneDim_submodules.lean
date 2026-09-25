import Mathlib

namespace Work.CFTLib

/-- The number of one-dimensional subspaces of a finite-dimensional vector space over `𝔽_p` is
`(p ^ dim - 1) / (p - 1)`. -/
theorem card_oneDim_submodules (p : ℕ) [Fact p.Prime] (V : Type) [AddCommGroup V]
    [Module (ZMod p) V] [Fintype V] :
    Nat.card {S : Submodule (ZMod p) V // Module.finrank (ZMod p) S = 1}
      = (p ^ Module.finrank (ZMod p) V - 1) / (p - 1) := by
  have : Module.Finite (ZMod p) V := Module.Finite.of_finite
  -- One-dimensional subspaces are the points of the projectivization of `V`.
  rw [← Nat.card_congr (Projectivization.equivSubmodule (ZMod p) V)]
  -- Count the points of `ℙ V`: `(Nat.card V - 1) / (Nat.card 𝔽_p - 1)`, then use
  -- `Nat.card V = p ^ finrank V` and `Nat.card 𝔽_p = p`.
  rw [Projectivization.card'', Module.natCard_eq_pow_finrank (K := ZMod p) (V := V),
    Nat.card_zmod]

end Work.CFTLib
