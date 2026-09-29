import Mathlib
import Submission.Work.Fx.FxLin

/-!
# Shared arithmetic helpers for the fixed-point scalar scaling word (paper Lemma 2.2)

Sizes (`isz`), the disc condition `inDisc`, and the round-towards-zero division `Int.tdiv`
(error `< 1` per coordinate, and `|trunc(A/b)| ≤ |A|/b`).
-/

set_option autoImplicit false

namespace Work.Fx

open HvdH

/-- `isz` bound from a modulus bound: `|z| ≤ 2^k` gives `isz z ≤ k + 3`. -/
theorem isz_le_of_natAbs_le {z : ℤ} {k : ℕ} (h : z.natAbs ≤ 2 ^ k) : isz z ≤ k + 3 := by
  have h1 : z.natAbs.size ≤ k + 1 := by
    rw [Nat.size_le]
    exact lt_of_le_of_lt h (Nat.pow_lt_pow_right (by norm_num) (Nat.lt_succ_self k))
  simp only [isz]
  omega

/-- A fixed-point number of the disc has coordinates of modulus `≤ 2^p`. -/
theorem natAbs_le_of_inDisc {p : ℕ} {z : ℤ × ℤ} (h : inDisc p z) :
    z.1.natAbs ≤ 2 ^ p ∧ z.2.natAbs ≤ 2 ^ p := by
  have key : ∀ w : ℤ × ℤ, inDisc p w → w.1.natAbs ≤ 2 ^ p := by
    intro w hw
    simp only [inDisc] at hw
    have h2 : w.1 ^ 2 ≤ (4 : ℤ) ^ p := by nlinarith [sq_nonneg w.2]
    have h3 : ((w.1.natAbs : ℤ)) ^ 2 ≤ (((2 ^ p : ℕ) : ℤ)) ^ 2 := by
      have e : ((w.1.natAbs : ℤ)) ^ 2 = w.1 ^ 2 := by
        rw [← Int.natCast_pow, ← Int.natAbs_pow, Int.natAbs_of_nonneg (sq_nonneg w.1)]
      have e2 : (((2 ^ p : ℕ) : ℤ)) ^ 2 = (4 : ℤ) ^ p := by
        have h1 : (((2 ^ p : ℕ) : ℤ)) = (2 : ℤ) ^ p := Int.natCast_pow 2 p
        rw [h1, ← pow_mul, mul_comm, pow_mul, show (4 : ℤ) = (2 : ℤ) ^ 2 by norm_num]
      rw [e, e2]
      exact h2
    exact (Nat.pow_le_pow_iff_left (show (2 : ℕ) ≠ 0 by norm_num)).mp (by exact_mod_cast h3)
  refine ⟨key z h, ?_⟩
  have h' : inDisc p (z.2, z.1) := by simp only [inDisc] at h ⊢; linarith
  exact key (z.2, z.1) h'

/-- Truncating division leaves a remainder of modulus `< b`. -/
theorem tmod_abs_lt (A : ℤ) {b : ℤ} (hb : 0 < b) : |A.tmod b| < b := by
  have h1 : (A.tmod b).natAbs = A.natAbs % b.natAbs := Int.natAbs_tmod A b
  have hbn : b.natAbs = b.toNat := by
    have h1' : ((b.natAbs : ℕ) : ℤ) = b := Int.natAbs_of_nonneg (le_of_lt hb)
    have h2' : ((b.toNat : ℕ) : ℤ) = b := Int.toNat_of_nonneg (le_of_lt hb)
    omega
  have h2 : A.natAbs % b.natAbs < b.natAbs := Nat.mod_lt _ (by omega)
  have h3 : (A.tmod b).natAbs < b.toNat := by rw [h1, ← hbn]; exact h2
  have h4 : (((A.tmod b).natAbs : ℕ) : ℤ) < b := by
    have : (((b.toNat : ℕ)) : ℤ) = b := Int.toNat_of_nonneg (le_of_lt hb)
    omega
  rw [Int.abs_eq_natAbs]
  exact h4

/-- Truncating division leaves a remainder of modulus `< b` (real form). -/
theorem tmod_abs_lt_R (A : ℤ) {b : ℤ} (hb : 0 < b) : |((A.tmod b : ℤ) : ℝ)| < (b : ℝ) := by
  have h := tmod_abs_lt A hb
  have h' : (((|A.tmod b| : ℤ)) : ℝ) < (b : ℝ) := by exact_mod_cast h
  rwa [Int.cast_abs] at h'

/-- Round towards zero: `|trunc(A/b) - A/b| < 1` (as real numbers), for `b > 0`. -/
theorem tdiv_sub_div_lt_one (A : ℤ) {b : ℤ} (hb : 0 < b) :
    |((A.tdiv b : ℤ) : ℝ) - (A : ℝ) / b| < 1 := by
  have hdec := Int.tdiv_mul_add_tmod A b
  have hbR : (0 : ℝ) < (b : ℝ) := by exact_mod_cast hb
  have hbne : (b : ℝ) ≠ 0 := ne_of_gt hbR
  have hsplit : (A : ℝ) / b = ((A.tdiv b : ℤ) : ℝ) + ((A.tmod b : ℤ) : ℝ) / b := by
    rw [div_eq_iff hbne]
    have hcast : ((A : ℤ) : ℝ) = ((A.tdiv b : ℤ) : ℝ) * b + ((A.tmod b : ℤ) : ℝ) := by
      have h := congrArg (fun z : ℤ => (z : ℝ)) hdec
      push_cast at h
      linarith [h]
    rw [hcast, add_mul, div_mul_cancel₀ _ hbne]
  rw [hsplit]
  have hrw : ((A.tdiv b : ℤ) : ℝ) - (((A.tdiv b : ℤ) : ℝ) + ((A.tmod b : ℤ) : ℝ) / b)
      = -(((A.tmod b : ℤ) : ℝ) / b) := by ring
  rw [hrw, abs_neg, abs_div, abs_of_pos hbR, div_lt_one hbR]
  exact tmod_abs_lt_R A hb

/-- `|trunc(A/b)|·b ≤ |A|` for `b > 0`. -/
theorem natAbs_tdiv_mul_le (A : ℤ) {b : ℤ} (hb : 0 < b) : (A.tdiv b).natAbs * b.natAbs ≤ A.natAbs := by
  rw [Int.natAbs_tdiv]
  have hbn : b.natAbs = b.toNat := by
    have h1' : ((b.natAbs : ℕ) : ℤ) = b := Int.natAbs_of_nonneg (le_of_lt hb)
    have h2' : ((b.toNat : ℕ) : ℤ) = b := Int.toNat_of_nonneg (le_of_lt hb)
    omega
  rw [hbn]
  exact Nat.div_mul_le_self _ _

/-- `|trunc(A/b)| ≤ |A|/b` for `b > 0`. -/
theorem natAbs_tdiv_le_div (A : ℤ) {b : ℤ} (hb : 0 < b) :
    ((A.tdiv b).natAbs : ℝ) ≤ (A.natAbs : ℝ) / b := by
  have h := natAbs_tdiv_mul_le A hb
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  have hbn : ((b.natAbs : ℕ) : ℝ) = (b : ℝ) := by
    have h3 : (b.natAbs : ℤ) = |b| := (Int.abs_eq_natAbs b).symm
    have h4 : ((b.natAbs : ℕ) : ℝ) = ((b.natAbs : ℤ) : ℝ) := by norm_num
    rw [h4, h3, Int.cast_abs, abs_of_pos hbR]
  have := (Nat.cast_le (α := ℝ)).mpr h
  push_cast at this
  rw [hbn] at this
  rw [le_div_iff₀ hbR]
  linarith [this]

end Work.Fx
