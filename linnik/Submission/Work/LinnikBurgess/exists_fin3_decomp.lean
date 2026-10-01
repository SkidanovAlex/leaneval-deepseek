import Mathlib

namespace Work.LinnikBurgess

/-- Splitting lemma: if `m` divides a product `u * w`, then `m` factors as
`m1 * m2` with `m1 ∣ u` and `m2 ∣ w`.  (This is the divisor-lattice property of
`ℕ`; the `m = 0` case is handled separately since `Nat.gcd 0 0 = 0`.) -/
lemma two_factor {m u w : ℕ} (h : m ∣ u * w) : ∃ m1 m2 : ℕ, m1 ∣ u ∧ m2 ∣ w ∧ m1 * m2 = m := by
  rcases eq_zero_or_pos m with hm | hm
  · subst hm
    rw [zero_dvd_iff] at h
    rcases mul_eq_zero.mp h with hu | hw
    · exact ⟨0, 1, by rw [hu], one_dvd _, by simp⟩
    · exact ⟨1, 0, one_dvd _, by rw [hw], by simp⟩
  · refine ⟨Nat.gcd m u, m / Nat.gcd m u, Nat.gcd_dvd_right m u, ?_, ?_⟩
    · have hg : 0 < Nat.gcd m u := Nat.pos_of_dvd_of_pos (Nat.gcd_dvd_left m u) hm
      have key : Nat.gcd m u * (m / Nat.gcd m u) ∣ Nat.gcd m u * (u / Nat.gcd m u) * w := by
        rw [Nat.mul_div_cancel' (Nat.gcd_dvd_left m u), Nat.mul_div_cancel' (Nat.gcd_dvd_right m u)]
        exact h
      rw [mul_assoc] at key
      have h2 : m / Nat.gcd m u ∣ (u / Nat.gcd m u) * w := (Nat.mul_dvd_mul_iff_left hg).mp key
      exact (Nat.coprime_div_gcd_div_gcd hg).dvd_of_dvd_mul_left h2
    · exact Nat.mul_div_cancel' (Nat.gcd_dvd_left m u)

/-- Every divisor `g` of a product of three natural numbers decomposes as a
product `a 0 * a 1 * a 2` with `a l ∣ v l` for each `l : Fin 3`. -/
theorem exists_fin3_decomp {g : ℕ} (hg : 0 < g) (v : Fin 3 → ℕ)
    (h : g ∣ ∏ l : Fin 3, v l) :
    ∃ a : Fin 3 → ℕ, (∏ l : Fin 3, a l = g) ∧ ∀ l : Fin 3, a l ∣ v l := by
  rw [Fin.prod_univ_three] at h
  have h' : g ∣ v 0 * (v 1 * v 2) := by rw [← mul_assoc]; exact h
  obtain ⟨b0, r, hb0, hr, hbr⟩ := two_factor h'
  obtain ⟨a1, a2, ha1, ha2, ha12⟩ := two_factor hr
  refine ⟨![b0, a1, a2], ?_, ?_⟩
  · have hp : (∏ l : Fin 3, (![b0, a1, a2] : Fin 3 → ℕ) l) = b0 * a1 * a2 := by
      rw [Fin.prod_univ_three]; simp
    rw [hp]
    calc b0 * a1 * a2 = b0 * (a1 * a2) := by rw [mul_assoc]
      _ = b0 * r := by rw [ha12]
      _ = g := hbr
  · intro l
    fin_cases l <;> simp [hb0, ha1, ha2]

end Work.LinnikBurgess
