/-
# Arithmetic helpers for the `C₄` cover count

Two elementary number-theoretic facts used in `c4_cover_card_eq_cube`.
-/
import Mathlib

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

namespace Work.Higman.C4Cover

/-- Number theory: `2^n - 1 ∣ 2^k - 1` implies `n ∣ k` (for `n ≥ 1`). -/
theorem two_pow_sub_one_dvd_imp {n k : ℕ} (hn : 0 < n)
    (hdiv : 2 ^ n - 1 ∣ 2 ^ k - 1) : n ∣ k := by
  have h1 : (2 : ℕ) ^ n ≡ 1 [MOD 2 ^ n - 1] :=
    (Nat.modEq_of_dvd' (n := 2 ^ n - 1) (a := 1) (b := 2 ^ n) Nat.one_le_two_pow
      (by simpa using dvd_refl (2 ^ n - 1))).symm
  have hcomp : (2 : ℕ) ^ k = (2 ^ n) ^ (k / n) * 2 ^ (k % n) := by
    have hdec : k = n * (k / n) + k % n := (Nat.div_add_mod k n).symm
    conv_lhs => rw [hdec]
    rw [pow_add, pow_mul]
  have h3 : (2 : ℕ) ^ k ≡ 2 ^ (k % n) [MOD 2 ^ n - 1] := by
    rw [hcomp]
    simpa using (h1.pow (k / n)).mul (Nat.ModEq.refl (2 ^ (k % n)))
  have h4 : (2 : ℕ) ^ k ≡ 1 [MOD 2 ^ n - 1] :=
    (Nat.modEq_of_dvd' (n := 2 ^ n - 1) (a := 1) (b := 2 ^ k) Nat.one_le_two_pow hdiv).symm
  have h5 : (2 : ℕ) ^ (k % n) ≡ 1 [MOD 2 ^ n - 1] := h3.symm.trans h4
  have h6 : 2 ^ n - 1 ∣ 2 ^ (k % n) - 1 :=
    (Nat.modEq_iff_dvd' (n := 2 ^ n - 1) (a := 1) (b := 2 ^ (k % n))
      Nat.one_le_two_pow).mp h5.symm
  have h7 : 2 ^ (k % n) - 1 < 2 ^ n - 1 := by
    have hlt : 2 ^ (k % n) < 2 ^ n := Nat.pow_lt_pow_right (by norm_num) (Nat.mod_lt k hn)
    have hlt2 : 1 ≤ 2 ^ (k % n) := Nat.one_le_two_pow
    omega
  have h8 : 2 ^ (k % n) - 1 = 0 := Nat.eq_zero_of_dvd_of_lt h6 h7
  have h9 : 2 ^ (k % n) = 1 := by
    have h10 : 1 ≤ 2 ^ (k % n) := Nat.one_le_two_pow
    omega
  have h10 : k % n = 0 := by
    rcases Nat.pow_eq_one.mp h9 with hh | hh
    · norm_num at hh
    · exact hh
  exact Nat.dvd_of_mod_eq_zero h10

/-- If `a ≡ 1 (mod q - 1)` and `q - 1 ∣ c - 1` where `c = X * a`, then `q - 1 ∣ X - 1`. -/
theorem index_sub_one_dvd {q X a c : ℕ} (hc : c = X * a) (ha : a ≡ 1 [MOD q - 1])
    (hc1 : 1 ≤ c) (hX1 : 1 ≤ X) (hdvd : q - 1 ∣ c - 1) : q - 1 ∣ X - 1 := by
  have h1 : X * a ≡ X [MOD q - 1] := by
    simpa using (Nat.ModEq.refl X).mul ha
  have h2 : c ≡ X [MOD q - 1] := by
    rw [hc]
    exact h1
  have h3 : c ≡ 1 [MOD q - 1] :=
    ((Nat.modEq_iff_dvd' (n := q - 1) (a := 1) (b := c) hc1).mpr hdvd).symm
  have h4 : X ≡ 1 [MOD q - 1] := h2.symm.trans h3
  exact (Nat.modEq_iff_dvd' (n := q - 1) (a := 1) (b := X) hX1).mp h4.symm

end Work.Higman.C4Cover
