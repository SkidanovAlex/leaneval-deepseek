import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The shift-and-reduce map `n ↦ (n + p^k - y % p^k) % p^k`

`shiftMod p k y n` is the representative in `[0, p^k)` of the residue class of `n - y`
modulo `p^k`.  It is the map used to shuffle the shifted count of `k`-tuples `a` with
entries in `[1,X]`, `X < p^k`, into the p-adic level set `Lvl p k k H`; see
`Submission/Work/BMF/recursion/linnik_reduce.lean` and `LinnikDefs.lean`.

Since `X < p^k` the entries of `a` and the shifted values `aᵢ - y` have at most one
representative in `[0, p^k)` each, so the map is injective on the tuples, and it preserves
all the congruences modulo `p^j`, `j ≤ k`, that define the level set.
-/

set_option autoImplicit false

namespace Work.BMF.recursion

/-- `shiftMod p k y n = (n + p^k - y % p^k) % p^k`, the representative in `[0, p^k)` of
`n - y` modulo `p^k`. -/
def shiftMod (p k y n : ℕ) : ℕ := (n + p ^ k - y % p ^ k) % p ^ k

/-- `shiftMod p k y n` lies in `[0, p^k)` when `p` is prime. -/
lemma shiftMod_lt (p k y n : ℕ) (hp : p.Prime) : shiftMod p k y n < p ^ k :=
  Nat.mod_lt _ (pow_pos hp.pos k)

/-- **Key congruence.**  `shiftMod p k y n ≡ n - y (mod p^k)`. -/
lemma shiftMod_modEq (p k y n : ℕ) (hp : p.Prime) :
    ((shiftMod p k y n : ℕ) : ℤ) ≡ (n : ℤ) - (y : ℤ) [ZMOD (p : ℤ) ^ k] := by
  have hpos : 0 < p ^ k := pow_pos hp.pos k
  have hle : y % p ^ k ≤ p ^ k := le_of_lt (Nat.mod_lt _ hpos)
  have hym : ((y % p ^ k : ℕ) : ℤ) ≡ (y : ℤ) [ZMOD (p : ℤ) ^ k] := by
    rw [show (p : ℤ) ^ k = ((p ^ k : ℕ) : ℤ) from (Nat.cast_pow p k).symm]
    exact Int.natCast_modEq_iff.mpr (Nat.mod_modEq y (p ^ k))
  have h1 : (p : ℤ) ^ k ∣ ((n + p ^ k - y % p ^ k : ℕ) : ℤ) - ((n : ℤ) - (y : ℤ)) := by
    rw [Nat.add_sub_assoc hle, Nat.cast_add, Nat.cast_sub hle, Nat.cast_pow]
    have : ((n : ℤ) + ((p : ℤ) ^ k - ((y % p ^ k : ℕ) : ℤ))) - ((n : ℤ) - (y : ℤ))
        = (p : ℤ) ^ k + ((y : ℤ) - ((y % p ^ k : ℕ) : ℤ)) := by ring
    rw [this]
    exact dvd_add (dvd_refl _) hym.dvd
  have h2 : (p : ℤ) ^ k ∣ ((n + p ^ k - y % p ^ k : ℕ) : ℤ)
      - (((n + p ^ k - y % p ^ k) % p ^ k : ℕ) : ℤ) := by
    rw [Int.natCast_emod, Nat.cast_pow]
    exact (Int.mod_modEq _ _).dvd
  rw [Int.modEq_iff_dvd, shiftMod]
  convert dvd_sub h2 h1 using 1
  ring

end Work.BMF.recursion
