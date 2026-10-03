import Mathlib
import Submission.Commons.NumberTheory.FriedlanderIwaniec.sq_sum_sq_root_count_le_two_pow_omega

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option linter.style.haveILetI false

namespace Commons.NumberTheory.FriedlanderIwaniec

/-- `((b.natAbs ^ 2 : ℕ) : ZMod d) = (b : ZMod d) ^ 2`: the natural number
`b.natAbs ^ 2` represents the square of `b` modulo `d`. -/
lemma natCast_natAbs_sq_eq_sq (d : ℕ) (b : ℤ) :
    ((b.natAbs ^ 2 : ℕ) : ZMod d) = (b : ZMod d) ^ 2 := by
  have h2 : ((b.natAbs ^ 2 : ℕ) : ℤ) = b ^ 2 := by
    push_cast
    exact sq_abs b
  have := congrArg (fun z : ℤ => (z : ZMod d)) h2
  push_cast at this
  simpa using this

/-- The integers `r` in `[0, d)` with `d ∣ r ^ 2 + b ^ 4` are exactly the residues
`r mod d` that are roots of `X ^ 2 + (b ^ 2) ^ 2` in `ZMod d`. -/
lemma dvd_sq_add_pow_four_iff_zmod (d : ℕ) (b : ℤ) (r : ℕ) :
    ((d : ℤ) ∣ (r : ℤ) ^ 2 + b ^ 4) ↔
      ((r : ZMod d) ^ 2 + ((b.natAbs ^ 2 : ℕ) : ZMod d) ^ 2 = 0) := by
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd ((r : ℤ) ^ 2 + b ^ 4) d]
  rw [natCast_natAbs_sq_eq_sq]
  push_cast
  ring_nf

/-- Number of residues `r mod d` with `r ^ 2 + b ^ 4 ≡ 0`, bounded by
`2 ^ ω(d) · gcd (b ^ 2, d₂)`. -/
theorem card_residues_le_two_pow_omega_gcd {d : ℕ} (hd : 0 < d) (b : ℤ) :
    ((Finset.range d).filter (fun r : ℕ => (d : ℤ) ∣ ((r : ℤ) ^ 2 + b ^ 4))).card ≤
      2 ^ (Nat.primeFactors d).card *
        Nat.gcd (b.natAbs ^ 2)
          ((Nat.primeFactors d).prod (fun p => p ^ (d.factorization p / 2))) := by
  haveI : NeZero d := ⟨hd.ne'⟩
  have hbridge :=
    sq_sum_sq_root_count_le_two_pow_omega (d := d) (b := b.natAbs ^ 2) hd
  rw [ncard_zmod_eq_range (n := d)
        (fun α : ZMod d => α ^ 2 + ((b.natAbs ^ 2 : ℕ) : ZMod d) ^ 2 = 0)] at hbridge
  refine le_trans (le_of_eq ?_) hbridge
  congr 1
  apply Finset.filter_congr
  intro r _
  exact dvd_sq_add_pow_four_iff_zmod d b r

end Commons.NumberTheory.FriedlanderIwaniec
