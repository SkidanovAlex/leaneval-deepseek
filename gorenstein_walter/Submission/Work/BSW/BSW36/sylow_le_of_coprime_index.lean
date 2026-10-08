import Mathlib

namespace Work.BSW.BSW36

/-- If `P` is a Sylow `p`-subgroup and `H` is a normal subgroup of index coprime to `|P|`, then
`P` is contained in `H`: the image of `P` in `N ⧸ H` has order dividing both `|P|` and `H.index`. -/
theorem sylow_le_of_coprime_index {N : Type} [Group N] [Finite N] {p : ℕ} [Fact p.Prime]
    (P : Sylow p N) {H : Subgroup N} [H.Normal]
    (h : Nat.Coprime (Nat.card P) H.index) : (P : Subgroup N) ≤ H := by
  rw [← Subgroup.relIndex_eq_one]
  exact Nat.eq_one_of_dvd_coprimes h (Subgroup.relIndex_dvd_card H P)
    (Subgroup.relIndex_dvd_index_of_normal H P)

end Work.BSW.BSW36
