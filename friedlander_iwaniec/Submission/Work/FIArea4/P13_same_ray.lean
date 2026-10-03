import Mathlib

namespace Work.FIArea4

/-- Two fractions `r1/s1` and `r2/s2`, both in lowest terms with respect to a
common numerator/denominator structure (`Coprime rᵢ (2 * sᵢ)`), that are equal
must share numerator and denominator. -/
lemma P13_same_ray {r1 r2 s1 s2 : ℕ} (h1 : Nat.Coprime r1 (2 * s1))
    (h2 : Nat.Coprime r2 (2 * s2)) (h : r1 * s2 = r2 * s1) : r1 = r2 ∧ s1 = s2 := by
  -- Coprimality with `2 * sᵢ` descends to coprimality with `sᵢ`.
  have hc1 : Nat.Coprime r1 s1 := h1.coprime_dvd_right (Dvd.intro 2 (by ring))
  have hc2 : Nat.Coprime r2 s2 := h2.coprime_dvd_right (Dvd.intro 2 (by ring))
  -- `r1 ∣ r2 * s1` with `r1` coprime to `s1` yields `r1 ∣ r2`.
  have hd1 : r1 ∣ r2 := hc1.dvd_of_dvd_mul_right ⟨s2, h.symm⟩
  have hd2 : r2 ∣ r1 := hc2.dvd_of_dvd_mul_right ⟨s1, h⟩
  have hr : r1 = r2 := Nat.dvd_antisymm hd1 hd2
  -- `r1 ≠ 0`: otherwise `Nat.gcd 0 (2 * s1) = 1` would force `2 * s1 = 1`.
  have hr1 : 0 < r1 := by
    rcases Nat.eq_zero_or_pos r1 with h0 | hp
    · exfalso
      rw [h0] at h1
      simp at h1
    · exact hp
  refine ⟨hr, ?_⟩
  have hs : r1 * s2 = r1 * s1 := by rw [h, hr]
  exact (Nat.mul_left_cancel hr1 hs).symm

end Work.FIArea4
