import Mathlib
import Submission.Work.L2F.Defs

namespace Work.L2F.Props

/-- In the finite field `GaloisField p k` of odd order `p ^ k`, the element `-1` is a square
iff the order of the multiplicative group, `p ^ k - 1`, is divisible by `4`, i.e. iff
`p ^ k ≡ 1 (mod 4)`.  This is the classical criterion for `-1` being a quadratic residue.

The proof combines Mathlib's `FiniteField.isSquare_neg_one_iff` (`-1` is a square iff the
cardinality of the field is not `3` mod `4`) with `p ^ k` being odd (`p` is odd). -/
theorem mod_four_eq_one_iff_isSquare_neg_one (p k : ℕ) [Fact p.Prime] (hp : Odd p) (hk : 5 ≤ p ^ k) :
    p ^ k % 4 = 1 ↔ IsSquare (-1 : GaloisField p k) := by
  -- `p ^ k ≥ 5` forces `k ≠ 0`, so the field is genuinely finite.
  have hk0 : k ≠ 0 := by
    rintro rfl
    simp only [pow_zero] at hk
    omega
  have : Fintype (GaloisField p k) := Fintype.ofFinite _
  -- `p` odd makes `p ^ k` odd.
  have hpk : Odd (p ^ k) := hp.pow
  -- The cardinality of `GaloisField p k` is `p ^ k`.
  have hcard : Fintype.card (GaloisField p k) = p ^ k := by
    rw [Fintype.card_eq_nat_card, GaloisField.card p k hk0]
  rw [FiniteField.isSquare_neg_one_iff, hcard]
  -- An odd number is `1` mod `4` iff it is not `3` mod `4`.
  have h2 : p ^ k % 2 = 1 := Nat.odd_iff.mp hpk
  omega

end Work.L2F.Props
