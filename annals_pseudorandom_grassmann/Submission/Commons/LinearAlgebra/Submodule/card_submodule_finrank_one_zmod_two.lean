import Mathlib.Algebra.Field.ZMod
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.LinearAlgebra.Projectivization.Cardinality
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal

namespace Commons.LinearAlgebra.Submodule

/-- A finite module over `𝔽₂` has as many elements as `2` raised to its `𝔽₂`-dimension.
This is the universe-polymorphic specialisation of
`Commons.LinearAlgebra.Module.natCard_eq_pow_finrank_zmod`, re-proved here so that it applies
to `V : Type*`. -/
theorem natCard_eq_two_pow_finrank_zmod {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    [Finite V] : Nat.card V = 2 ^ Module.finrank (ZMod 2) V := by
  calc Nat.card V = Nat.card (Fin (Module.finrank (ZMod 2) V) → ZMod 2) := by
        exact Nat.card_congr (((Module.finBasis (ZMod 2) V).repr).trans
          (Finsupp.linearEquivFunOnFinite (ZMod 2) (ZMod 2)
            (Fin (Module.finrank (ZMod 2) V)))).toEquiv
    _ = Nat.card (ZMod 2) ^ Nat.card (Fin (Module.finrank (ZMod 2) V)) := Nat.card_fun
    _ = 2 ^ Nat.card (Fin (Module.finrank (ZMod 2) V)) := by rw [Nat.card_zmod]
    _ = 2 ^ Module.finrank (ZMod 2) V := by rw [Nat.card_fin]

/-- Over `𝔽₂`, a one-dimensional subspace is determined by its unique nonzero vector, so the
number of one-dimensional subspaces of a finite `𝔽₂`-vector space equals the number of nonzero
vectors, namely `2 ^ finrank V - 1`.

The count is obtained from Mathlib's cardinality formula for the projectivization: the
equivalence `Projectivization.equivSubmodule` identifies one-dimensional subspaces with the
points of `ℙ 𝔽₂ V`, and `Projectivization.card''` computes `#ℙ 𝔽₂ V = (#V - 1)/(#𝔽₂ - 1)`,
which for `𝔽₂` is `#V - 1 = 2 ^ finrank V - 1`. -/
theorem card_submodule_finrank_one_zmod_two {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    [Finite V] :
    Nat.card {W : Submodule (ZMod 2) V // Module.finrank (ZMod 2) W = 1} =
      2 ^ Module.finrank (ZMod 2) V - 1 := by
  classical
  rw [← Nat.card_congr (Projectivization.equivSubmodule (ZMod 2) V)]
  rw [Projectivization.card'']
  rw [Nat.card_zmod]
  rw [show (2 - 1 : ℕ) = 1 from rfl, Nat.div_one]
  rw [natCard_eq_two_pow_finrank_zmod]

end Commons.LinearAlgebra.Submodule