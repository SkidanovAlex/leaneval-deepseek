import Mathlib
import Submission.Work.BMF.Defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF.mr_direct

open Finset

/-- Membership in `Work.BMF.primesIn P Q`, stated with the real bounds: a natural number `p`
lies in `primesIn P Q` exactly when it is prime, `P ≤ p`, and `p ≤ Q`.

(The two `floor`/`ceil` conversions are `Nat.ceil_le` and `Nat.le_floor`; in the direction
`p ≤ ⌊Q⌋₊ → (p:ℝ) ≤ Q` the hypothesis `0 ≤ Q` needed by `Nat.le_floor_iff` follows from
`p.Prime` via `2 ≤ p` and `Nat.floor_pos`.) -/
lemma mem_primesIn_iff {P Q : ℝ} {p : ℕ} :
    p ∈ Work.BMF.primesIn P Q ↔ p.Prime ∧ P ≤ (p : ℝ) ∧ (p : ℝ) ≤ Q := by
  rw [Work.BMF.primesIn, Work.BMF.natIcc, Finset.mem_filter, Finset.mem_Icc]
  constructor
  · rintro ⟨⟨h1, h2⟩, hp⟩
    have hp2 : 2 ≤ p := hp.two_le
    refine ⟨hp, Nat.ceil_le.mp h1, ?_⟩
    have hpos : 0 < ⌊Q⌋₊ := by omega
    exact (Nat.le_floor_iff (zero_le_one.trans (Nat.floor_pos.mp hpos))).mp h2
  · rintro ⟨hp, h1, h2⟩
    exact ⟨⟨Nat.ceil_le.mpr h1, Nat.le_floor h2⟩, hp⟩

/-- `n` is coprime to the product of the primes in `[P,Q]` exactly when no prime of `[P,Q]`
divides `n`.  (`Work.BMF.primesIn P Q` is the finset of primes in `[P,Q]`, and `natIcc P Q` is
`Finset.Icc ⌈P⌉₊ ⌊Q⌋₊`.)

Proof: `p ∈ primesIn P Q ↔ p.Prime ∧ P ≤ (p:ℝ) ∧ (p:ℝ) ≤ Q` (via `Nat.ceil_le` / `Nat.le_floor`),
then `Nat.coprime_prod_right_iff` and `Nat.Prime.coprime_iff_not_dvd`. -/
lemma coprime_primesIn_iff (n : ℕ) (P Q : ℝ) :
    n.Coprime (∏ p ∈ Work.BMF.primesIn P Q, p) ↔
      ∀ p : ℕ, Nat.Prime p → P ≤ (p : ℝ) → (p : ℝ) ≤ Q → ¬ p ∣ n := by
  rw [Nat.coprime_prod_right_iff]
  constructor
  · intro h p hp hP hQ
    have hmem : p ∈ Work.BMF.primesIn P Q := mem_primesIn_iff.mpr ⟨hp, hP, hQ⟩
    exact (hp.coprime_iff_not_dvd).mp ((h p hmem).symm)
  · intro h p hmem
    rw [mem_primesIn_iff] at hmem
    exact ((hmem.1).coprime_iff_not_dvd.mpr (h p hmem.1 hmem.2.1 hmem.2.2)).symm

end Work.BMF.mr_direct
