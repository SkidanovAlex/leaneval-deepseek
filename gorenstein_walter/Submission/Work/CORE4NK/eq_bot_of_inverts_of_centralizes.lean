import Mathlib

namespace Work.CORE4NK

/-- A subgroup of odd order whose elements are simultaneously inverted and centralised by an
element `s` is trivial: each `y` in it satisfies `y = y⁻¹`, so `orderOf y ∣ 2`, while `orderOf y`
also divides the odd number `Nat.card Y`. -/
theorem eq_bot_of_inverts_of_centralizes {H : Type*} [Group H] (Y : Subgroup H) (s : H)
    (hYodd : Odd (Nat.card Y)) (hinv : ∀ y ∈ Y, s * y * s⁻¹ = y⁻¹)
    (hcent : ∀ y ∈ Y, s * y = y * s) : Y = ⊥ := by
  rw [eq_bot_iff]
  intro y hy
  rw [Subgroup.mem_bot]
  -- `s` both centralises and inverts `y`, so conjugation by `s` fixes `y` while it equals `y⁻¹`.
  have h1 : y = y⁻¹ := by
    have h := hinv y hy
    rw [hcent y hy] at h
    simpa using h
  -- hence `y` is an involution.
  have h2 : y ^ 2 = 1 := by
    rw [sq]
    nth_rewrite 1 [h1]
    exact inv_mul_cancel y
  have hdvd2 : orderOf y ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr h2
  have hdvdn : orderOf y ∣ Nat.card Y := Y.orderOf_dvd_natCard hy
  have hodd : Odd (orderOf y) := hYodd.of_dvd_nat hdvdn
  -- an odd divisor of `2` is `1`.
  have hone : orderOf y = 1 := by
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd2 with h | h
    · exact h
    · exact absurd h (hYodd.ne_two_of_dvd_nat hdvdn)
  exact orderOf_eq_one_iff.mp hone

end Work.CORE4NK
