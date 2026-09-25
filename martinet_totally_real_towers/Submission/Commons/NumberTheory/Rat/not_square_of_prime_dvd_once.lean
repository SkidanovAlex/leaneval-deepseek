import Mathlib

namespace Commons.NumberTheory.Rat

theorem not_square_of_prime_dvd_once {m q : ℕ} (hq : Nat.Prime q) (hdiv : q ∣ m)
    (hnot : ¬ q ^ 2 ∣ m) : ∀ x : ℚ, x ^ 2 ≠ (m : ℚ) := by
  intro x hx
  have hx' : ((x.num : ℚ) / (x.den : ℚ)) ^ 2 = (m : ℚ) := by
    simpa [Rat.num_div_den] using hx
  have hden : (x.den : ℚ) ≠ 0 := by
    exact_mod_cast x.den_ne_zero
  have hnum_sq_rat : ((x.num : ℚ) ^ 2) = (m : ℚ) * (x.den : ℚ) ^ 2 := by
    rw [div_pow] at hx'
    field_simp [hden] at hx'
    ring_nf at hx' ⊢
    linarith
  have hnum_int : x.num ^ 2 = (m : ℤ) * (x.den : ℤ) ^ 2 := by
    exact_mod_cast hnum_sq_rat
  have hnat_eq : x.num.natAbs ^ 2 = m * x.den ^ 2 := by
    have h : ((x.num.natAbs ^ 2 : ℕ) : ℤ) = ((m * x.den ^ 2 : ℕ) : ℤ) := by
      calc
        ((x.num.natAbs ^ 2 : ℕ) : ℤ) = (x.num.natAbs : ℤ) ^ 2 := by norm_num
        _ = x.num ^ 2 := by exact Int.natAbs_sq x.num
        _ = (m : ℤ) * (x.den : ℤ) ^ 2 := hnum_int
        _ = ((m * x.den ^ 2 : ℕ) : ℤ) := by norm_num
    exact Int.natCast_inj.mp h
  have hq_dvd_num_abs : q ∣ x.num.natAbs := by
    have hqint_dvd_m : (q : ℤ) ∣ (m : ℤ) := by
      exact_mod_cast hdiv
    have hqint_dvd_rhs : (q : ℤ) ∣ (m : ℤ) * (x.den : ℤ) ^ 2 := by
      exact dvd_mul_of_dvd_left hqint_dvd_m _
    have hqint_dvd_num_sq : (q : ℤ) ∣ x.num ^ 2 := by
      rwa [← hnum_int] at hqint_dvd_rhs
    have hq_dvd_natAbs_num_sq : q ∣ (x.num ^ 2).natAbs := by
      exact Int.natCast_dvd.mp hqint_dvd_num_sq
    have hnatAbs_sq : (x.num ^ 2).natAbs = x.num.natAbs ^ 2 := Int.natAbs_pow x.num 2
    have hq_dvd_natAbs_num_sq2 : q ∣ x.num.natAbs ^ 2 := by
      rwa [hnatAbs_sq] at hq_dvd_natAbs_num_sq
    exact hq.dvd_of_dvd_pow hq_dvd_natAbs_num_sq2
  have hq_coprime_den : q.Coprime x.den := by
    exact Nat.Coprime.coprime_dvd_left hq_dvd_num_abs x.reduced
  have hq_not_dvd_den : ¬ q ∣ x.den := by
    exact (hq.coprime_iff_not_dvd).mp hq_coprime_den
  have hq_sq_dvd_a_sq : q ^ 2 ∣ x.num.natAbs ^ 2 := by
    exact pow_dvd_pow_of_dvd hq_dvd_num_abs 2
  have hq_sq_dvd_mul : q ^ 2 ∣ m * x.den ^ 2 := by
    rwa [hnat_eq] at hq_sq_dvd_a_sq
  have hq_sq_coprime_den_sq : (q ^ 2).Coprime (x.den ^ 2) := by
    exact hq_coprime_den.pow 2 2
  have hq_sq_dvd_m : q ^ 2 ∣ m := by
    exact hq_sq_coprime_den_sq.dvd_of_dvd_mul_right hq_sq_dvd_mul
  exact hnot hq_sq_dvd_m

end Commons.NumberTheory.Rat
