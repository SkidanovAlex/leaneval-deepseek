import Mathlib
import Submission.Work.PTCert.Interfaces
import Submission.Work.PTCert.digits.sum_mul_pow_lt_pow
import Submission.Work.PTCert.digits.sum_mul_pow_div_mod

/-!
# Digit arithmetic for the permutation/sign codes (`pdig`, `sbit`, `idPC`)

Three facts about the packing of a permutation into base `8` (`idPC`) and of a sign vector
into base `2` (`sbit`):

* `pdig (idPC r) i = i` for `i < r ≤ 8`: the identity permutation code has base-8 digits
  `0, 1, …, r-1` (the bound `i < 8` is essential — the digits are read modulo `8`);
* `sbit (∑ t, s t * 2 ^ t) i = s t i`: the bits of the packed sign code are the sign vector;
* `∑ t, s t * 2 ^ t < 2 ^ r`: the packed sign code fits in `r` bits.

All three are instances of the standard base-`b` digit facts
(`Work.PTCert.digits.sum_mul_pow_lt_pow`, `Work.PTCert.digits.sum_mul_pow_div_mod`).
-/

namespace Work.PTCert

/-- The `j`-th bit of the sign vector `s`, as `0` or `1`; digits outside `Fin r` are `0`. -/
def sdigit (r : ℕ) (s : Fin r → Bool) (j : ℕ) : ℕ :=
  if h : j < r then (if s ⟨j, h⟩ then 1 else 0) else 0

theorem sdigit_lt_two (r : ℕ) (s : Fin r → Bool) (j : ℕ) : sdigit r s j < 2 := by
  unfold sdigit
  split_ifs <;> omega

/-- The `j`-th bit of the sign vector is `s j` on `Fin r`. -/
theorem sdigit_eq (r : ℕ) (s : Fin r → Bool) (j : Fin r) :
    sdigit r s (j : ℕ) = if s j then 1 else 0 := by
  simp [sdigit]

/-- The packed sign code of `s` is the base-`2` number with digits `sdigit r s`. -/
theorem sum_fin_eq_sum_range (r : ℕ) (s : Fin r → Bool) :
    (∑ t : Fin r, (if s t then 1 else 0) * 2 ^ (t : ℕ))
      = ∑ j ∈ Finset.range r, sdigit r s j * 2 ^ j := by
  rw [← Fin.sum_univ_eq_sum_range (fun j => sdigit r s j * 2 ^ j) r]
  exact Finset.sum_congr rfl (fun t _ => by rw [sdigit_eq])

theorem digitArith (r : ℕ) (hr : r ≤ 8) :
    (∀ i : ℕ, i < r → Submission.PTCert.pdig (Submission.PTCert.idPC r) i = i) ∧
    (∀ (s : Fin r → Bool) (i : Fin r),
      Submission.PTCert.sbit (∑ t : Fin r, (if s t then 1 else 0) * 2 ^ (t : ℕ)) (i : ℕ) = if s i then 1 else 0) ∧
    (∀ s : Fin r → Bool, (∑ t : Fin r, (if s t then 1 else 0) * 2 ^ (t : ℕ)) < 2 ^ r) := by
  refine ⟨?_, ?_, ?_⟩
  · -- `pdig (idPC r) i = i`: `idPC r` is the base-8 number with digits `j ↦ j`.
    intro i hi
    have h := digits.sum_mul_pow_div_mod (b := 8) (d := fun j => j) (n := r) (i := i)
      (by norm_num) (fun j hj => by omega) hi
    simp only [Submission.PTCert.pdig, Submission.PTCert.idPC]
    rw [Nat.shiftRight_eq_div_pow,
      show (2 : ℕ) ^ (3 * i) = 8 ^ i from by
        rw [Nat.pow_mul, show (2 : ℕ) ^ 3 = 8 from by norm_num]]
    exact h
  · -- the bits of the packed sign code are the sign vector
    intro s i
    rw [sum_fin_eq_sum_range r s, Submission.PTCert.sbit, Nat.shiftRight_eq_div_pow]
    rw [digits.sum_mul_pow_div_mod (b := 2) (d := sdigit r s) (n := r) (i := (i : ℕ))
      (by norm_num) (fun j _ => sdigit_lt_two r s j) i.isLt]
    exact sdigit_eq r s i
  · -- the packed sign code fits in `r` bits
    intro s
    rw [sum_fin_eq_sum_range r s]
    exact digits.sum_mul_pow_lt_pow (by norm_num) (sdigit r s) r (fun j _ => sdigit_lt_two r s j)

end Work.PTCert
