import Mathlib

namespace Work.CORE4.DihFourConjAux

/-! ## The centre of a dihedral group of order at least `8`

For `n ≥ 4` the group `DihedralGroup n` has centre of order at most `2`: it is trivial when `n`
is odd, and `{1, r (n/2)}` when `n` is even.  Consequently the only central involution different
from `1` is the "central rotation" `r (n/2)`.

Mathlib's `DihedralGroup.center_eq_bot_of_odd_ne_one` and
`DihedralGroup.center_eq_closure_of_even_ne_two` give this description of the centre; what is left
is to identify the nontrivial element of `⟨r (n/2)⟩` with `r (n/2)` itself, which follows from the
general fact that the powers of an involution are only `1` and the involution.

Note that the hypothesis `z ^ 2 = 1` is redundant: it is *implied* by centrality, `z ≠ 1` and
`n ≥ 4` (the centre has exponent `2` for `n ≥ 4`).  It is kept because the statement is the one
requested by the caller. -/

/-- In any group, an involution `a ≠ 1` has only the powers `1` and `a`: the powers of `a` depend
only on the exponent modulo `2`. -/
lemma zpow_eq_one_or_eq_self_of_sq_eq_one {G : Type*} [Group G] {a : G} (ha2 : a ^ 2 = 1)
    (ha1 : a ≠ 1) (k : ℤ) : a ^ k = 1 ∨ a ^ k = a := by
  have hord : orderOf a = 2 := orderOf_eq_prime ha2 ha1
  have hmod : a ^ (k % 2) = a ^ k := by
    have h := zpow_mod_orderOf a k
    rwa [hord] at h
  rcases Int.emod_two_eq_zero_or_one k with h | h
  · exact Or.inl (by rw [← hmod, h]; simp)
  · exact Or.inr (by rw [← hmod, h]; simp)

/-- For even `n`, the central rotation `r (n/2)` is an involution (its angle is `n/2`, of order
`2` in `ZMod n`). -/
lemma centralRotation_sq {n : ℕ} (hn : Even n) :
    (DihedralGroup.r ((n / 2 : ℕ) : ZMod n) : DihedralGroup n) ^ 2 = 1 := by
  have h0 : ((n / 2 : ℕ) : ZMod n) + ((n / 2 : ℕ) : ZMod n) = 0 := by
    rw [← Nat.cast_add, ← two_mul, Nat.two_mul_div_two_of_even hn, ZMod.natCast_self]
  rw [pow_two, DihedralGroup.r_mul_r, h0, DihedralGroup.r_zero]

/-- For `n ≥ 4` the central rotation `r (n/2)` is different from `1`, because `n ∤ n/2`. -/
lemma centralRotation_ne_one {n : ℕ} [NeZero n] (hn : 4 ≤ n) :
    (DihedralGroup.r ((n / 2 : ℕ) : ZMod n) : DihedralGroup n) ≠ 1 := by
  intro h
  rw [DihedralGroup.one_def, DihedralGroup.r.injEq] at h
  have hdvd : n ∣ n / 2 := (ZMod.natCast_eq_zero_iff (n / 2) n).mp h
  have hpos : 0 < n / 2 := by omega
  have hle := Nat.le_of_dvd hpos hdvd
  omega

set_option linter.unusedVariables false in
/-- In `DihedralGroup n` with `n ≥ 4`, the only central involution different from `1` is the
central rotation `r (n/2)`. -/
theorem center_involution_eq_centralRotation {n : ℕ} [NeZero n] (hn : 4 ≤ n)
    {z : DihedralGroup n} (hz : z ∈ Subgroup.center (DihedralGroup n)) (hz2 : z ^ 2 = 1)
    (hz1 : z ≠ 1) :
    z = DihedralGroup.r ((n / 2 : ℕ) : ZMod n) := by
  rcases Nat.even_or_odd n with hn_even | hn_odd
  · -- `n` even: the centre is `⟨r (n/2)⟩`, whose nontrivial element is `r (n/2)` itself.
    have hn_ne_two : n ≠ 2 := by omega
    rw [DihedralGroup.center_eq_closure_of_even_ne_two hn_even hn_ne_two] at hz
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hz
    rcases zpow_eq_one_or_eq_self_of_sq_eq_one (centralRotation_sq hn_even)
      (centralRotation_ne_one hn) k with h | h
    · exact absurd (hk.symm.trans h) hz1
    · rw [← hk]; exact h
  · -- `n` odd: the centre is trivial, contradicting `z ≠ 1`.
    have hn_ne_one : n ≠ 1 := by omega
    rw [DihedralGroup.center_eq_bot_of_odd_ne_one hn_odd hn_ne_one] at hz
    exact absurd (Subgroup.mem_bot.mp hz) hz1

end Work.CORE4.DihFourConjAux
