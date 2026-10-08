import Mathlib
import Submission.Work.GLUE.Defs

namespace Work.BG

/-- If a finite subgroup `S` of `G` is a `2`-group of order at least `4`, then `4 ∣ |S|`. -/
theorem four_dvd_card_of_isPGroup_two_of_four_le {G : Type} [Group G] [Finite G]
    (S : Subgroup G) (hpg : IsPGroup 2 S) (h4 : 4 ≤ Nat.card S) :
    4 ∣ Nat.card S := by
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hpg
  have hk2 : 2 ≤ k := by
    have hle : 2 ^ 2 ≤ 2 ^ k := by rw [← hk]; simpa using h4
    exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp hle
  rw [hk]
  simpa using pow_dvd_pow (2 : ℕ) hk2

/-- The Sylow `2`-subgroup `S` of the Bender–Glauberman data is dihedral of order `2n` with
`n ≥ 2`, hence has order at least `4`, whence `4 ∣ |S|` (a Sylow `2`-subgroup being a
`2`-group, its order is a power of `2`). -/
theorem four_dvd_card_S {G : Type} [Group G] [Finite G] (D : Work.GW2.BGData G) :
    4 ∣ Nat.card ↥(D.S : Subgroup G) := by
  obtain ⟨e⟩ := D.dih
  have hcard : Nat.card ↥(D.S : Subgroup G) = 2 * D.n := by
    rw [Nat.card_congr e.toEquiv, DihedralGroup.nat_card]
  have hpg : IsPGroup 2 ↥(D.S : Subgroup G) := D.S.isPGroup'
  refine four_dvd_card_of_isPGroup_two_of_four_le _ hpg ?_
  rw [hcard]
  have := D.two_le
  omega

end Work.BG
