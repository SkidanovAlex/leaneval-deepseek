import Mathlib
import Submission.Work.BMF.Defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF

/-- Any prime lying in `(⌊P⌋₊, ⌊2P⌋₊]` lies in the "primes in `[P, 2P]`" set: the lower
bound `p > ⌊P⌋₊` forces `p ≥ ⌈P⌉₊`, since `P < ⌊P⌋₊ + 1 ≤ p`. -/
theorem Ioc_filter_prime_subset_primesIn (P : ℝ) :
    (Finset.Ioc ⌊P⌋₊ ⌊2 * P⌋₊).filter Nat.Prime ⊆ Work.BMF.primesIn P (2 * P) := by
  intro p hp
  rw [Finset.mem_filter] at hp
  obtain ⟨hmem, hprime⟩ := hp
  rw [Finset.mem_Ioc] at hmem
  obtain ⟨hlo, hhi⟩ := hmem
  rw [primesIn, natIcc, Finset.mem_filter, Finset.mem_Icc]
  refine ⟨⟨?_, hhi⟩, hprime⟩
  rw [Nat.ceil_le]
  have h1 : P < (⌊P⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one P
  have h2 : ((⌊P⌋₊ + 1 : ℕ) : ℝ) ≤ (p : ℝ) := by
    exact_mod_cast Nat.succ_le_of_lt hlo
  push_cast at h2
  linarith

end Work.BMF
