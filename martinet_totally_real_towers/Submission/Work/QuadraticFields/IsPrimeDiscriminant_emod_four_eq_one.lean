import Mathlib
import Submission.Work.QuadraticFields.MultiquadraticInside

namespace Work.QuadraticFields

/-- **A prime discriminant which is odd is `≡ 1 (mod 4)`.**

The odd prime discriminants are exactly the numbers `(-1)^((p-1)/2) * p` with `p` an odd prime
(the three remaining values `-4`, `8`, `-8` of `IsPrimeDiscriminant` are even).  If `p ≡ 1 (mod 4)`
the sign is `+1` and the value is `p ≡ 1`; if `p ≡ 3 (mod 4)` the sign is `-1` and the value is
`-p ≡ -3 ≡ 1`. -/
theorem IsPrimeDiscriminant_emod_four_eq_one {d : ℤ} (hd : IsPrimeDiscriminant d)
    (h : Odd d) : d % 4 = 1 := by
  rcases hd with h4 | h8 | hm8 | ⟨p, _hp, hodd, hd⟩
  · -- `d = -4` is even, contradicting `Odd d`
    subst h4
    exfalso
    obtain ⟨k, hk⟩ := h
    omega
  · -- `d = 8` is even
    subst h8
    exfalso
    obtain ⟨k, hk⟩ := h
    omega
  · -- `d = -8` is even
    subst hm8
    exfalso
    obtain ⟨k, hk⟩ := h
    omega
  · -- `d = (-1)^((p-1)/2) * p` with `p` an odd prime
    rw [hd]
    obtain ⟨j, hj⟩ := hodd
    have hk : (p - 1) / 2 = j := by omega
    rw [hk]
    by_cases hev : Even j
    · -- `(p-1)/2` even: the sign is `+1` and `p = 4j' + 1`
      rw [hev.neg_one_pow, one_mul]
      obtain ⟨m, hm⟩ := hev
      have hp_eq : p = 4 * m + 1 := by omega
      rw [hp_eq]
      push_cast
      rw [show (4 : ℤ) * ↑m + 1 = 1 + 4 * ↑m by ring, Int.add_mul_emod_self_left]
      norm_num
    · -- `(p-1)/2` odd: the sign is `-1` and `p = 4j' + 3`, so `d = -p ≡ 1`
      have hjo : Odd j := Nat.not_even_iff_odd.mp hev
      rw [hjo.neg_one_pow]
      obtain ⟨m, hm⟩ := hjo
      have hp_eq : p = 4 * m + 3 := by omega
      rw [hp_eq]
      push_cast
      rw [show (-1 : ℤ) * (4 * ↑m + 3) = -3 + 4 * (-↑m) by ring,
        Int.add_mul_emod_self_left]
      norm_num

end Work.QuadraticFields
