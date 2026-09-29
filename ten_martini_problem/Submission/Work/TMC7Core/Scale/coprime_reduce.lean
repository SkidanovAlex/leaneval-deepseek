import Mathlib

namespace Work.TMC7Core.Scale

/-- Reduction of `m / k`, `k ≥ 1`, to lowest terms: there are `a : ℤ`, `q : ℕ` with
`1 ≤ q ≤ k`, `Nat.Coprime a.natAbs q`, and `a/q = m/k`. -/
theorem coprime_reduce {m : ℤ} {k : ℕ} (hk : 1 ≤ k) :
    ∃ (a : ℤ) (q : ℕ), 1 ≤ q ∧ q ≤ k ∧ Nat.Coprime (Int.natAbs a) q ∧
      (a : ℝ) / (q : ℝ) = (m : ℝ) / (k : ℝ) := by
  -- Write `g = gcd m.natAbs k` and reduce by it.
  have hkpos : 0 < k := by omega
  set g : ℕ := Nat.gcd m.natAbs k with hg
  have hgpos : 0 < g := by rw [hg]; exact Nat.gcd_pos_of_pos_right _ hkpos
  have hgdvdm : g ∣ m.natAbs := by rw [hg]; exact Nat.gcd_dvd_left _ _
  have hgdvdk : g ∣ k := by rw [hg]; exact Nat.gcd_dvd_right _ _
  have hgzdvdm : (g : ℤ) ∣ m := by
    rw [← Int.natAbs_dvd_natAbs]
    simpa using hgdvdm
  have hm_eq : (g : ℤ) * (m / (g : ℤ)) = m := Int.mul_ediv_cancel' hgzdvdm
  have hk_eq : g * (k / g) = k := Nat.mul_div_cancel' hgdvdk
  refine ⟨m / (g : ℤ), k / g, ?_, ?_, ?_, ?_⟩
  · exact Nat.div_pos (Nat.le_of_dvd hkpos hgdvdk) hgpos
  · exact Nat.div_le_self k g
  · -- the reduced numerator and denominator are coprime
    have hnat : (m / (g : ℤ)).natAbs = m.natAbs / g := by
      have h1 : m.natAbs = g * (m / (g : ℤ)).natAbs := by
        conv_lhs => rw [← hm_eq]
        rw [Int.natAbs_mul, Int.natAbs_natCast]
      rw [h1, Nat.mul_div_cancel_left _ hgpos]
    rw [hnat]
    simpa [hg] using
      Nat.coprime_div_gcd_div_gcd (m := m.natAbs) (n := k) (by simpa [hg] using hgpos)
  · -- both fractions equal `m / k`
    have hmc : (m : ℝ) = (g : ℝ) * ((m / (g : ℤ) : ℤ) : ℝ) := by
      conv_lhs => rw [← hm_eq]
      push_cast; ring
    have hkc : (k : ℝ) = (g : ℝ) * ((k / g : ℕ) : ℝ) := by
      conv_lhs => rw [← hk_eq]
      push_cast; ring
    have hgne : (g : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hgpos)
    rw [hmc, hkc]
    exact (mul_div_mul_left _ _ hgne).symm

end Work.TMC7Core.Scale
