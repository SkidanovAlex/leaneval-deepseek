import Mathlib

namespace Work.DSTR.M110

/-- LTE (Lifting The Exponent) in the case `d ∣ y + 1`, `d` an odd prime:
`v_d (y^d + 1) = v_d (y + 1) + 1`.

This is an immediate specialization of Mathlib's `padicValNat.pow_add_pow`, applied with
`x = y`, `y = 1`, `n = d`. The only side condition to check is `¬ d ∣ y`, which follows
from `d ∣ y + 1` because then `d ∣ (y + 1) - y = 1`, impossible for a prime `d`. -/
theorem padicValNatPowAddOne (y d : ℕ) (hd : d.Prime) (hdo : Odd d) (h : d ∣ y + 1) :
    padicValNat d (y^d + 1) = padicValNat d (y + 1) + 1 := by
  have _hF : Fact d.Prime := ⟨hd⟩
  have hdy : ¬ d ∣ y := by
    intro hdvd
    have h1 : d ∣ 1 := by
      have := Nat.dvd_sub h hdvd
      simpa using this
    exact absurd (Nat.le_of_dvd one_pos h1) (by have := hd.one_lt; omega)
  have key := padicValNat.pow_add_pow (p := d) (x := y) (y := 1) (n := d) hdo h hdy hdo
  simp only [one_pow] at key
  rw [key, padicValNat.self hd.one_lt]

end Work.DSTR.M110
