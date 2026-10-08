import Mathlib
import Submission.Work.CORE4.Defs

namespace Work.CORE4.SevenRemain

/-- **`O_p(K) ≠ 1` for a finite nilpotent group `K` with `p ∣ |K|`.**  In a finite nilpotent
group every Sylow subgroup is normal, so a Sylow `p`-subgroup `P` (nontrivial because
`p ∣ |K|`) is a nontrivial normal `p`-subgroup of `K`, hence lies in `O_p(K)`.

(`Work.GW2.pCore p ↥K` is the `p`-core of the group `↥K`.) -/
theorem pCore_ne_bot_of_isNilpotent_of_dvd :
    ∀ (G : Type) [Group G] [Finite G] (p : ℕ) [Fact p.Prime] (K : Subgroup G),
      Group.IsNilpotent ↥K → p ∣ Nat.card ↥K → Work.GW2.pCore p ↥K ≠ ⊥ := by
  intro G _ _ p hp K hK hdvd
  haveI : Group.IsNilpotent ↥K := hK
  -- `K` has a normal subgroup `H` of order `p` (`p` prime, `p ∣ |K|`, `K` nilpotent)
  obtain ⟨H, hHcard, hHnormal⟩ :=
    Group.IsNilpotent.exists_normal_card_eq_of_dvd_card (G := ↥K) hdvd
  haveI : H.Normal := hHnormal
  have hHne : H ≠ ⊥ := by
    rw [← Subgroup.one_lt_card_iff_ne_bot, hHcard]
    exact hp.out.one_lt
  -- `H` is a `p`-group, since `|H| = p = p ^ 1`
  have hHp : IsPGroup p H := IsPGroup.of_card (n := 1) (by simpa using hHcard)
  -- every normal `p`-subgroup of `K` lies in `O_p(K)`
  have hle : H ≤ Work.GW2.pCore p ↥K := by
    rw [Work.GW2.pCore]
    exact Subgroup.normal_le_normalCore.mpr (le_sSup ⟨inferInstance, hHp⟩)
  intro hbot
  exact hHne (le_bot_iff.mp (hbot ▸ hle))

end Work.CORE4.SevenRemain
