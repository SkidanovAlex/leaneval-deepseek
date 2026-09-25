import Mathlib

namespace NK.ProfiniteP.LinearAlgebra

open scoped LinearAlgebra.Projectivization

/-- The number of submodules `W` of a finite-dimensional `𝔽_p`-vector space `V` with
`dim (V / W) = 1` (i.e. the number of hyperplanes) equals the number of points of the
projective space `ℙ (V*)` of the dual, namely `(p ^ dim V - 1) / (p - 1)`.

Codimension-one submodules of `V` are in bijection with `𝔽_p`-lines in the dual `V*`,
via the annihilator `W ↦ Wᵃ` and coannihilator `Λ ↦ Λ_𝔞`; the projective space `ℙ V*`
is the set of one-dimensional subspaces of `V*`. -/
theorem natCard_submodule_finrank_quotient_eq_one {p : ℕ} [Fact p.Prime] {V : Type*}
    [AddCommGroup V] [Module (ZMod p) V] [FiniteDimensional (ZMod p) V] :
    Nat.card {W : Submodule (ZMod p) V // Module.finrank (ZMod p) (V ⧸ W) = 1} =
      (p ^ Module.finrank (ZMod p) V - 1) / (p - 1) := by
  -- Codimension-one subspaces of `V` correspond to one-dimensional subspaces of the dual.
  have e : {W : Submodule (ZMod p) V // Module.finrank (ZMod p) (V ⧸ W) = 1} ≃
      {H : Submodule (ZMod p) (Module.Dual (ZMod p) V) // Module.finrank (ZMod p) H = 1} :=
    { toFun := fun W => ⟨W.1.dualAnnihilator, by
          rw [← (Subspace.quotEquivAnnihilator W.1).finrank_eq]; exact W.2⟩
      invFun := fun H => ⟨H.1.dualCoannihilator, by
          rw [(Subspace.quotEquivAnnihilator H.1.dualCoannihilator).finrank_eq,
            Subspace.dualCoannihilator_dualAnnihilator_eq]
          exact H.2⟩
      left_inv := fun W => Subtype.ext (Subspace.dualAnnihilator_dualCoannihilator_eq)
      right_inv := fun H => Subtype.ext (Subspace.dualCoannihilator_dualAnnihilator_eq) }
  -- The dual has `p ^ dim V` elements.
  have h1 : Nat.card (Module.Dual (ZMod p) V) = p ^ Module.finrank (ZMod p) V := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod p) (V := Module.Dual (ZMod p) V),
        Subspace.dual_finrank_eq, Nat.card_zmod]
  rw [Nat.card_congr e,
    ← Nat.card_congr (Projectivization.equivSubmodule (ZMod p) (Module.Dual (ZMod p) V))]
  rw [Projectivization.card'', h1, Nat.card_zmod]

end NK.ProfiniteP.LinearAlgebra
