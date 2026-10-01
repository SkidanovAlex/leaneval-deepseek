import Mathlib
import Submission.Work.LinnikBurgess.lf_defs
import Submission.Work.LinnikBurgess.critN_ne_zero_of_unique
import Submission.Work.LinnikBurgess.critN_content_iff

-- The index `i` and the singleton hypothesis `hi` are not needed for this divisibility statement.
set_option linter.unusedVariables false

namespace Work.LinnikBurgess.lfSmall

open Work.LinnikBurgess.critNcontent

/-- **Triple-vanishing content bound, `p = 3`.**  If every coefficient of the Wronskian
`critN a b = f_a' f_b - f_a f_b'` is divisible by `3 ^ h`, then the content `contAB a b` is
divisible by `3 ^ (h - 1)`.

This is the `p = 3` counterpart of the forward direction of `critN_content_iff`, and it loses
exactly one power of `3`: degree `4` gives `3 ^ h ∣ A₁ - B₁` and degree `3` gives `3 ^ h ∣ A₂ - B₂`
(the factor `2` is still invertible modulo `3 ^ h`), but at degree `2` the coefficient
`A₁B₂ - A₂B₁ + 3(B₃ - A₃)` only yields `3 ^ h ∣ 3(A₃ - B₃)`, i.e. `3 ^ (h - 1) ∣ A₃ - B₃`. -/
theorem content_three {a b : Fin 3 → ℕ} (i : Fin 6)
    (hi : ∀ j : Fin 6, j ≠ i → shift a b i ≠ shift a b j) {h : ℕ}
    (hc : ∀ n : ℕ, ((3 ^ h : ℕ) : ℤ) ∣ (critN a b).coeff n) :
    (3 ^ (h - 1) : ℕ) ∣ contAB a b := by
  rcases Nat.eq_zero_or_pos h with rfl | hpos
  · rw [show (3 : ℕ) ^ (0 - 1) = 1 by rw [Nat.zero_sub, pow_zero]]
    exact one_dvd _
  have h3ne : (3 : ℤ) ≠ 0 := by norm_num
  have hcop2 : IsCoprime (((3 ^ h : ℕ) : ℤ)) (2 : ℤ) :=
    (Nat.isCoprime_iff_coprime).mpr (Nat.Coprime.pow_left h (by norm_num : Nat.Coprime 3 2))
  -- degree `4`: `3 ^ h ∣ A₁ - B₁`
  have h4 : ((3 ^ h : ℕ) : ℤ) ∣ esymm3 a 0 - esymm3 b 0 := by
    have hh := hc 4
    rw [critN_eq_expand, coeff_four_exp] at hh
    have := (dvd_neg).mpr hh
    rwa [neg_sub] at this
  -- degree `3`: `3 ^ h ∣ 2(A₂ - B₂)`, and `2` is invertible modulo `3 ^ h`
  have h3 : ((3 ^ h : ℕ) : ℤ) ∣ esymm3 a 1 - esymm3 b 1 := by
    have hh := hc 3
    rw [critN_eq_expand, coeff_three_exp] at hh
    have hh2 : ((3 ^ h : ℕ) : ℤ) ∣ esymm3 b 1 - esymm3 a 1 :=
      hcop2.dvd_of_dvd_mul_left hh
    have := (dvd_neg).mpr hh2
    rwa [neg_sub] at this
  -- degree `2`: `3 ^ h ∣ 3(A₃ - B₃)`, hence `3 ^ (h - 1) ∣ A₃ - B₃`
  have h2 : ((3 ^ (h - 1) : ℕ) : ℤ) ∣ esymm3 a 2 - esymm3 b 2 := by
    have h2c : ((3 ^ h : ℕ) : ℤ) ∣ -esymm3 a 1 * esymm3 b 0 + esymm3 a 0 * esymm3 b 1
        + 3 * (esymm3 b 2 - esymm3 a 2) := by
      have hh := hc 2
      rw [critN_eq_expand, coeff_two_exp] at hh
      exact hh
    have hbase : ((3 ^ h : ℕ) : ℤ) ∣ (esymm3 a 0 - esymm3 b 0) * esymm3 b 1
        - (esymm3 a 1 - esymm3 b 1) * esymm3 b 0 :=
      dvd_sub (dvd_mul_of_dvd_left h4 _) (dvd_mul_of_dvd_left h3 _)
    have hdiff : -esymm3 a 1 * esymm3 b 0 + esymm3 a 0 * esymm3 b 1
          + 3 * (esymm3 b 2 - esymm3 a 2)
        - ((esymm3 a 0 - esymm3 b 0) * esymm3 b 1
            - (esymm3 a 1 - esymm3 b 1) * esymm3 b 0)
        = 3 * (esymm3 b 2 - esymm3 a 2) := by ring
    have h3mul : ((3 ^ h : ℕ) : ℤ) ∣ 3 * (esymm3 b 2 - esymm3 a 2) := by
      have := dvd_sub h2c hbase
      rwa [hdiff] at this
    have hnat : 3 ^ h = 3 * 3 ^ (h - 1) := by
      obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : h ≠ 0)
      rw [Nat.succ_eq_add_one, Nat.add_sub_cancel, pow_succ]; ring
    have hdiv : ((3 ^ h : ℕ) : ℤ) = (3 : ℤ) * ((3 ^ (h - 1) : ℕ) : ℤ) := by
      rw [hnat]; push_cast; ring
    have h3mul' : (3 : ℤ) * ((3 ^ (h - 1) : ℕ) : ℤ)
        ∣ 3 * (esymm3 b 2 - esymm3 a 2) := by
      rwa [← hdiv]
    have hd3b : ((3 ^ (h - 1) : ℕ) : ℤ) ∣ esymm3 b 2 - esymm3 a 2 :=
      (mul_dvd_mul_iff_left h3ne).mp h3mul'
    have := (dvd_neg).mpr hd3b
    rwa [neg_sub] at this
  rw [contAB_eq]
  refine Nat.dvd_gcd ?_ (Nat.dvd_gcd ?_ ?_)
  · exact dvd_trans (pow_dvd_pow 3 (by omega : h - 1 ≤ h))
      ((nat_dvd_natAbs_iff (3 ^ h) (esymm3 a 0 - esymm3 b 0)).mpr h4)
  · exact dvd_trans (pow_dvd_pow 3 (by omega : h - 1 ≤ h))
      ((nat_dvd_natAbs_iff (3 ^ h) (esymm3 a 1 - esymm3 b 1)).mpr h3)
  · exact (nat_dvd_natAbs_iff (3 ^ (h - 1)) (esymm3 a 2 - esymm3 b 2)).mpr h2

end Work.LinnikBurgess.lfSmall
