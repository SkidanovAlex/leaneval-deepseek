import Mathlib
import Submission.Work.BMF.Defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF

/-- The primes of `[P, 2P]` that do *not* lie in `(⌊P⌋₊, ⌊2P⌋₊]` are all equal to `⌈P⌉₊`:
such a prime `p` satisfies `⌈P⌉₊ ≤ p` (from `p ∈ primesIn P (2P)`) and `p ≤ ⌊P⌋₊`
(from not lying in `Ioc ⌊P⌋₊ ⌊2P⌋₊` while still being `≤ ⌊2P⌋₊`), so
`⌊P⌋₊ ≤ ⌈P⌉₊ ≤ p ≤ ⌊P⌋₊` forces `p = ⌊P⌋₊ = ⌈P⌉₊`. -/
theorem primesIn_sdiff_subset_singleton (P : ℝ) :
    (Work.BMF.primesIn P (2 * P)) \
        ((Finset.Ioc ⌊P⌋₊ ⌊2 * P⌋₊).filter Nat.Prime) ⊆ ({⌈P⌉₊} : Finset ℕ) := by
  intro p hp
  rw [Finset.mem_sdiff, Finset.mem_filter] at hp
  obtain ⟨hp1, hp2⟩ := hp
  rw [primesIn, natIcc, Finset.mem_filter, Finset.mem_Icc] at hp1
  obtain ⟨⟨hlo, hhi⟩, hprime⟩ := hp1
  rw [Finset.mem_singleton]
  by_contra hne
  have hgt : ⌊P⌋₊ < p := by
    rcases lt_or_eq_of_le hlo with h | h
    · exact lt_of_le_of_lt (Nat.floor_le_ceil P) h
    · exact absurd h.symm hne
  exact hp2 ⟨by rw [Finset.mem_Ioc]; exact ⟨hgt, hhi⟩, hprime⟩

theorem primesIn_sdiff_card_le_one (P : ℝ) :
    ((Work.BMF.primesIn P (2 * P)) \ ((Finset.Ioc ⌊P⌋₊ ⌊2 * P⌋₊).filter Nat.Prime)).card ≤ 1 := by
  calc ((Work.BMF.primesIn P (2 * P)) \
          ((Finset.Ioc ⌊P⌋₊ ⌊2 * P⌋₊).filter Nat.Prime)).card
      ≤ ({⌈P⌉₊} : Finset ℕ).card := Finset.card_le_card (primesIn_sdiff_subset_singleton P)
    _ = 1 := Finset.card_singleton _

end Work.BMF
