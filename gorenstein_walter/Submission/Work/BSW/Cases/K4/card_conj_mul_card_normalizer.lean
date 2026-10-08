import Mathlib
import Submission.Work.BSW.Cases.K4.ConjAction
import Submission.Work.BSW.Cases.K4.card_orbit_eq_card_conjSet
import Submission.Work.BSW.Cases.K4.card_stabilizer_eq_card_normalizer_inf

open scoped Pointwise

namespace Work.BSW.Cases.K4

/-- **Orbit-stabiliser for conjugation by a subgroup.**
For subgroups `L, Y ≤ G` with `G` finite, the number of elements of `L` equals the number of
`L`-conjugates of `Y` (i.e. the subgroups `Y.map (MulAut.conj l)` with `l ∈ L`) times the number
of elements of `L` normalising `Y` (`Subgroup.normalizer Y ⊓ L`). -/
theorem card_conj_mul_card_normalizer {G : Type} [Group G] [Finite G] (L Y : Subgroup G) :
    Nat.card ↥L = Nat.card {Z : Subgroup G // ∃ l ∈ L, Z = Y.map (MulAut.conj (l : G)).toMonoidHom} *
      Nat.card ↥(Subgroup.normalizer (Y : Set G) ⊓ L) := by
  have hOS : Nat.card ↥L =
      Nat.card ↥(MulAction.orbit L Y) * Nat.card ↥(MulAction.stabilizer L Y) := by
    rw [← Nat.card_prod]
    exact Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup L Y).symm
  rw [hOS, card_orbit_eq_card_conjSet L Y, card_stabilizer_eq_card_normalizer_inf L Y]

end Work.BSW.Cases.K4
