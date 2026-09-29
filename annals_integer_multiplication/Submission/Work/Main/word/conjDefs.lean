import Mathlib
import Submission.HvdH.Interfaces
import Submission.Work.Main.defs

/-!
# `Work.Main.word`: conjugating a vector of fixed-point complex numbers

Definitions and size lemmas shared by the files proving `Work.Main.word.conjVec`, the
"conjugation" word of step 4 of the main step (paper Prop 5.2): `F̃*_s(u) := conj(F̃_s(conj u))`,
where conjugation is exact on fixed-point values.

A coefficient is the value `cfxVal z = cons (int z.1) (int z.2)`, so conjugating it means
negating its **second** component; `conjVal` does that on integer-pair values and is the
identity on every other value (those never occur in a `cvecVal`).
-/

set_option autoImplicit false

namespace Work.Main.word

open HvdH

/-- Conjugate an integer-pair value: negate the imaginary part.  The identity on every other
value (only `cons (int ·) (int ·)` values occur in `cvecVal`). -/
def conjVal (v : Val) : Val :=
  match v with
  | .cons (.int a) (.int b) => .cons (.int a) (.int (-b))
  | v => v

@[simp] theorem conjVal_cons_int (a b : ℤ) :
    conjVal (Val.cons (Val.int a) (Val.int b)) = Val.cons (Val.int a) (Val.int (-b)) := rfl

@[simp] theorem conjVal_cfxVal (z : ℤ × ℤ) : conjVal (cfxVal z) = cfxVal (z.1, -z.2) := rfl

/-- Conjugation preserves the disc condition `C̃◦`. -/
theorem inDisc_conj {p : ℕ} {z : ℤ × ℤ} (h : inDisc p z) : inDisc p (z.1, -z.2) := by
  simp only [inDisc] at h ⊢
  nlinarith [h]

/-! ## Size bounds for fixed-point numbers in the disc -/

/-- `|z| ≤ 2^p` as soon as `z² ≤ 4^p`. -/
theorem natAbs_le_two_pow {p : ℕ} {z : ℤ} (h : z ^ 2 ≤ (4 : ℤ) ^ p) : z.natAbs ≤ 2 ^ p := by
  have h3 : ((z.natAbs : ℤ)) ^ 2 ≤ (((2 ^ p : ℕ)) : ℤ) ^ 2 := by
    have e : ((z.natAbs : ℤ)) ^ 2 = z ^ 2 := by
      rw [← Int.natCast_pow, ← Int.natAbs_pow, Int.natAbs_of_nonneg (sq_nonneg z)]
    have e2 : (((2 ^ p : ℕ) : ℤ)) ^ 2 = (4 : ℤ) ^ p := by
      have h1 : (((2 ^ p : ℕ) : ℤ)) = (2 : ℤ) ^ p := Int.natCast_pow 2 p
      rw [h1, ← pow_mul, mul_comm, pow_mul, show (4 : ℤ) = (2 : ℤ) ^ 2 by norm_num]
    rw [e, e2]
    exact h
  exact (Nat.pow_le_pow_iff_left (show (2 : ℕ) ≠ 0 by norm_num)).mp (by exact_mod_cast h3)

/-- `isz z ≤ p + 3` for `|z| ≤ 2^p`. -/
private theorem isz_le_of_natAbs_le {z : ℤ} {p : ℕ} (h : z.natAbs ≤ 2 ^ p) : isz z ≤ p + 3 := by
  have h1 : z.natAbs.size ≤ p + 1 := by
    rw [Nat.size_le]
    exact lt_of_le_of_lt h (Nat.pow_lt_pow_right (by norm_num) (Nat.lt_succ_self p))
  simp only [isz]
  omega

/-- A fixed-point complex number in the disc has encoding size `≤ 2p + 8`. -/
theorem vsz_cfxVal_le {p : ℕ} {z : ℤ × ℤ} (h : inDisc p z) : vsz (cfxVal z) ≤ 2 * p + 8 := by
  have h1 : z.1.natAbs ≤ 2 ^ p := by
    have h2 : z.1 ^ 2 ≤ (4 : ℤ) ^ p := by
      simp only [inDisc] at h
      nlinarith [sq_nonneg z.2]
    exact natAbs_le_two_pow h2
  have h2 : z.2.natAbs ≤ 2 ^ p := by
    have h3 : z.2 ^ 2 ≤ (4 : ℤ) ^ p := by
      simp only [inDisc] at h
      nlinarith [sq_nonneg z.1]
    exact natAbs_le_two_pow h3
  have i1 := isz_le_of_natAbs_le h1
  have i2 := isz_le_of_natAbs_le h2
  rw [show cfxVal z = Val.cons (.int z.1) (.int z.2) from rfl, vsz_cons, vsz_int, vsz_int]
  omega

/-- The encoding size of a conjugated fixed-point number in the disc. -/
theorem vsz_conjVal_cfxVal {p : ℕ} {z : ℤ × ℤ} (h : inDisc p z) :
    vsz (conjVal (cfxVal z)) ≤ 2 * p + 8 := by
  rw [conjVal_cfxVal]
  exact vsz_cfxVal_le (inDisc_conj h)

end Work.Main.word
