import Mathlib
import Submission.Work.TameArithmetic.VSDefs

/-!
# `-1` is a square in `ℚ_p` for `p ≡ 1 (mod 4)`

The local condition of Koch's group `V_S` (see `Submission/Work/TameArithmetic/VSDefs.lean`):
for a prime `p ≡ 1 (mod 4)` the field `ℚ_p` contains a square root of `-1`.

The proof is Hensel's lemma.  Since `p ≡ 1 (mod 4)` (and `p` is prime, so `p ≠ 3 mod 4`),
`-1` is a square modulo `p` (`ZMod.exists_sq_eq_neg_one_iff`): say `n ^ 2 ≡ -1 (mod p)`.
Then `n` is a unit of `ℤ_[p]` (as `p ∤ n`), and the polynomial `X ^ 2 + 1` has
`‖aeval n (X ^ 2 + 1)‖ < 1` while `‖aeval n (2 * X)‖ = 1`, so Hensel
(`hensels_lemma`) produces a root `z ∈ ℤ_[p]`, whence `z ^ 2 = -1` in `ℚ_[p]`.
-/

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

namespace Work.TameArithmetic

/-- **`-1` is a square in `ℚ_p` when `p ≡ 1 (mod 4)`** (Euler's criterion plus Hensel). -/
theorem isSquare_neg_one_padic {p : ℕ} [Fact p.Prime] (hp : p % 4 = 1) :
    ∃ y : ℚ_[p], y * y = -(1 : ℚ_[p]) := by
  have hpp : Nat.Prime p := Fact.out
  -- `p ≠ 2`
  have hnotdvd2 : ¬ p ∣ 2 := by
    intro hd
    have hle := Nat.le_of_dvd (by norm_num) hd
    have hge := hpp.two_le
    omega
  -- `-1` is a square mod `p`
  have h4 : p % 4 ≠ 3 := by omega
  obtain ⟨y0, hy0⟩ := (ZMod.exists_sq_eq_neg_one_iff (p := p)).mpr h4
  have hn : p ∣ y0.val ^ 2 + 1 := by
    rw [← CharP.cast_eq_zero_iff (ZMod p) p]
    rw [Nat.cast_add, Nat.cast_pow, ZMod.natCast_zmod_val, pow_two, ← hy0]
    simp
  -- norms in `ℤ_[p]`
  have h2 : ‖((2 : ℕ) : ℤ_[p])‖ = 1 := by
    rw [PadicInt.norm_natCast_eq_one_iff]
    exact hpp.coprime_iff_not_dvd.mpr hnotdvd2
  have hn1 : ‖((y0.val : ℕ) : ℤ_[p])‖ = 1 := by
    rw [PadicInt.norm_natCast_eq_one_iff]
    refine hpp.coprime_iff_not_dvd.mpr (fun hd => hpp.not_dvd_one ?_)
    exact (Nat.dvd_add_iff_right (dvd_pow hd (by norm_num : (2 : ℕ) ≠ 0))).mpr hn
  -- the value of `X ^ 2 + 1` at `y0` is small
  have hnlt : ‖(Polynomial.aeval ((y0.val : ℕ) : ℤ_[p]))
      ((Polynomial.X : Polynomial ℤ_[p]) ^ 2 + 1)‖ < 1 := by
    rw [show (Polynomial.aeval ((y0.val : ℕ) : ℤ_[p]))
      ((Polynomial.X : Polynomial ℤ_[p]) ^ 2 + 1) = ((y0.val ^ 2 + 1 : ℕ) : ℤ_[p]) by simp,
      PadicInt.norm_natCast_lt_one_iff]
    exact hn
  -- the derivative `2 * X` at `y0` is a unit
  have hderiv : ‖(Polynomial.aeval ((y0.val : ℕ) : ℤ_[p]))
      (Polynomial.derivative ((Polynomial.X : Polynomial ℤ_[p]) ^ 2 + 1))‖ = 1 := by
    rw [show (Polynomial.aeval ((y0.val : ℕ) : ℤ_[p]))
      (Polynomial.derivative ((Polynomial.X : Polynomial ℤ_[p]) ^ 2 + 1)) =
        ((2 * y0.val : ℕ) : ℤ_[p]) by
        simp [Polynomial.derivative_add, Polynomial.derivative_pow]]
    rw [Nat.cast_mul, norm_mul, h2, hn1, one_mul]
  have hnorm : ‖(Polynomial.aeval ((y0.val : ℕ) : ℤ_[p]))
      ((Polynomial.X : Polynomial ℤ_[p]) ^ 2 + 1)‖ <
      ‖(Polynomial.aeval ((y0.val : ℕ) : ℤ_[p]))
      (Polynomial.derivative ((Polynomial.X : Polynomial ℤ_[p]) ^ 2 + 1))‖ ^ 2 := by
    rw [hderiv, one_pow]
    exact hnlt
  -- Hensel
  obtain ⟨z, hz, -⟩ := hensels_lemma (F := (Polynomial.X : Polynomial ℤ_[p]) ^ 2 + 1)
    (a := ((y0.val : ℕ) : ℤ_[p])) hnorm
  have hz2 : z ^ 2 + 1 = 0 := by simpa using hz
  have hz3 : z ^ 2 = -1 := eq_neg_of_add_eq_zero_left hz2
  refine ⟨(z : ℚ_[p]), ?_⟩
  rw [← pow_two, ← PadicInt.coe_pow, hz3]
  simp

end Work.TameArithmetic
