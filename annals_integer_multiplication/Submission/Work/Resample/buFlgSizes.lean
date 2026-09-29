import Mathlib
import Submission.Work.Resample.buWtKit

namespace Work.Resample

open HvdH

/-!
# `Work.Resample.buFlgSizes`: the size certificate for the guard-flag word

Every value occurring in the guard-flag word `buFlgW` (`Z`, `p`, the intermediate
`3p`, `3p+100`, `p+10`, `(p+10)·2^(3p+100) = auBnd p`, and `auBnd p + 1`) has `isz ≤ buSZ p`
for `p ≥ 100`.  This is the side condition under which each primitive step of the word costs at
most `buSBW p Λ` and hence can be absorbed into the uniform `K (p+1)^K` budget.

All bounds are elementary: `p` and `3p` have `≤ 2p` bits (`3p ≤ 4^p`), the constants `3`, `10`,
`100` and the affine values `p+10`, `3p+100` have `≤ p+O(1)` bits, and the two large values
`auBnd p`, `auBnd p + 1` have `≤ 4p+105` bits (`natAbs_auBnd_le`).
-/

/-- `3p ≤ 4^p`, hence `3p < 2^(2p)`. -/
theorem buFlgSizes_three_mul_le_four_pow (p : ℕ) : 3 * p ≤ 4 ^ p := by
  have hp : p ≤ 2 ^ p := le_of_lt (Nat.lt_two_pow_self)
  rcases Nat.lt_or_ge p 2 with h | h
  · interval_cases p <;> norm_num
  · have h3 : (3 : ℕ) ≤ 2 ^ p := by
      calc (3 : ℕ) ≤ 2 ^ 2 := by norm_num
        _ ≤ 2 ^ p := Nat.pow_le_pow_right (by norm_num) h
    calc 3 * p ≤ 3 * 2 ^ p := Nat.mul_le_mul_left 3 hp
      _ = 2 ^ p * 3 := by ring
      _ ≤ 2 ^ p * 2 ^ p := Nat.mul_le_mul_left _ h3
      _ = 4 ^ p := by
          rw [show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_mul, ← pow_add]
          congr 1
          ring

/-- `3p + 100 ≤ 2^(2p)` for `p ≥ 100`. -/
theorem buFlgSizes_three_p_add_100_le (p : ℕ) (hp : 100 ≤ p) : 3 * p + 100 ≤ 2 ^ (2 * p) := by
  calc 3 * p + 100 ≤ 103 * 2 ^ p := three_mul_add_le p
    _ ≤ 2 ^ 7 * 2 ^ p := Nat.mul_le_mul_right _ (by norm_num)
    _ = 2 ^ (7 + p) := by rw [pow_add]
    _ ≤ 2 ^ (2 * p) := Nat.pow_le_pow_right (by norm_num) (by omega)

/-- `p` itself. -/
theorem buFlgSizes_p (p : ℕ) : isz (p : ℤ) ≤ buSZ p :=
  isz_le_buSZ_pow_p (by rw [Int.natAbs_natCast]; exact le_of_lt (Nat.lt_two_pow_self))

/-- `3p`. -/
theorem buFlgSizes_three_mul_p (p : ℕ) : isz ((3 : ℤ) * (p : ℤ)) ≤ buSZ p := by
  have hcast : (3 : ℤ) * (p : ℤ) = ((3 * p : ℕ) : ℤ) := by push_cast; ring
  rw [hcast]
  refine isz_le_buSZ_pow_2p ?_
  rw [Int.natAbs_natCast]
  calc 3 * p ≤ 4 ^ p := buFlgSizes_three_mul_le_four_pow p
    _ = 2 ^ (2 * p) := by rw [show (4 : ℕ) = 2 ^ 2 by norm_num, pow_mul]

/-- `100 + 3p`. -/
theorem buFlgSizes_100_add_three_mul_p (p : ℕ) (hp : 100 ≤ p) :
    isz ((100 : ℤ) + (3 : ℤ) * (p : ℤ)) ≤ buSZ p := by
  have hcast : (100 : ℤ) + (3 : ℤ) * (p : ℤ) = ((3 * p + 100 : ℕ) : ℤ) := by push_cast; ring
  rw [hcast]
  refine isz_le_buSZ_pow_2p ?_
  rw [Int.natAbs_natCast]
  exact buFlgSizes_three_p_add_100_le p hp

/-- `10 + p`. -/
theorem buFlgSizes_ten_add_p (p : ℕ) : isz ((10 : ℤ) + (p : ℤ)) ≤ buSZ p := by
  have hcast : (10 : ℤ) + (p : ℤ) = ((p + 10 : ℕ) : ℤ) := by push_cast; ring
  rw [hcast]
  refine isz_le_buSZ_of_lin (A := p + 4) (by omega) ?_
  rw [Int.natAbs_natCast]
  have hp1 : 1 ≤ 2 ^ p := Nat.one_le_two_pow
  have hple : p ≤ 2 ^ p := le_of_lt (Nat.lt_two_pow_self)
  calc p + 10 ≤ 16 * 2 ^ p := by nlinarith
    _ = 2 ^ (p + 4) := by rw [pow_add]; norm_num; ring

/-- `3p + 100`, as an inequality in `ℕ`. -/
theorem buFlgSizes_three_p_add_100_le_buSZ (p : ℕ) : 3 * p + 100 ≤ buSZ p := by
  simp only [buSZ]; omega

/-- `3p + 100`, as a natural cast. -/
theorem buFlgSizes_nat_three_p_add_100 (p : ℕ) (hp : 100 ≤ p) :
    isz (((3 * p + 100 : ℕ)) : ℤ) ≤ buSZ p := by
  refine isz_le_buSZ_pow_2p ?_
  rw [Int.natAbs_natCast]
  exact buFlgSizes_three_p_add_100_le p hp

/-- `(p + 10)·2^(3p+100) = auBnd p`.  Stated with the sum `10 + p` of the word. -/
theorem buFlgSizes_mul_pow (p : ℕ) :
    isz (((10 : ℤ) + (p : ℤ)) * (2 : ℤ) ^ (3 * p + 100)) ≤ buSZ p := by
  have he : ((10 : ℤ) + (p : ℤ)) * (2 : ℤ) ^ (3 * p + 100) = auBnd p := by
    rw [auBnd, auEn, auPrec]; push_cast; ring
  rw [he]
  exact isz_auBnd_le_buSZ p

/-- The guard bound shifted by one: `auBnd p + 1`. -/
theorem buFlgSizes_auBnd_add_one (p : ℕ) : isz (auBnd p + 1) ≤ buSZ p := by
  refine isz_le_buSZ_of (A := 4 * p + 105) (by simp only [buSZ]; omega) ?_
  refine le_trans (Int.natAbs_add_le (auBnd p) 1) ?_
  have h1 : (1 : ℤ).natAbs = 1 := rfl
  rw [h1]
  calc (auBnd p).natAbs + 1 ≤ 2 ^ (4 * p + 104) + 1 := Nat.add_le_add_right (natAbs_auBnd_le p) 1
    _ ≤ 2 ^ (4 * p + 104) + 2 ^ (4 * p + 104) := by
        have hpos : 1 ≤ 2 ^ (4 * p + 104) := Nat.one_le_two_pow
        omega
    _ = 2 ^ (4 * p + 105) := by rw [← two_mul, pow_succ]; ring

/-- Size certificate for the values occurring in the guard-flag word `Work.Resample.buFlgW`
(and in the bound sub-word `Work.Resample.buBndW`): every one of them has `isz ≤ buSZ p` at
`p ≥ 100`. -/
theorem buFlgSizes (p : ℕ) (hp : 100 ≤ p) :
    HvdH.isz (p : ℤ) ≤ Work.Resample.buSZ p ∧
    HvdH.isz ((3 : ℤ) * (p : ℤ)) ≤ Work.Resample.buSZ p ∧
    HvdH.isz ((100 : ℤ) + (3 : ℤ) * (p : ℤ)) ≤ Work.Resample.buSZ p ∧
    HvdH.isz ((10 : ℤ) + (p : ℤ)) ≤ Work.Resample.buSZ p ∧
    3 * p + 100 ≤ Work.Resample.buSZ p ∧
    HvdH.isz ((3 * p + 100 : ℕ) : ℤ) ≤ Work.Resample.buSZ p ∧
    HvdH.isz (((10 : ℤ) + (p : ℤ)) * (2 : ℤ) ^ (3 * p + 100)) ≤ Work.Resample.buSZ p ∧
    HvdH.isz (Work.Resample.auBnd p + 1) ≤ Work.Resample.buSZ p :=
  ⟨buFlgSizes_p p, buFlgSizes_three_mul_p p, buFlgSizes_100_add_three_mul_p p hp,
   buFlgSizes_ten_add_p p, buFlgSizes_three_p_add_100_le_buSZ p,
   buFlgSizes_nat_three_p_add_100 p hp, buFlgSizes_mul_pow p, buFlgSizes_auBnd_add_one p⟩

end Work.Resample
