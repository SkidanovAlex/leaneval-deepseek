/-
# Assembling Pólya–Vinogradov for the Jacobi character `(·|b)`

Elementary reductions from a general modulus `b` to the *primitive* Jacobi character of the
squarefree kernel of the odd part of `b`:

* `oddPart` facts (`oddPart b = b / 2 ^ (b.factorization 2)`, so Mathlib's
  `Nat.ordProj_mul_ordCompl_eq_self` and friends apply verbatim);
* `J(n | 2 ^ e) = 1` for odd `n` (so `J(n | b) = J(n | m)` for `n` coprime to `b`,
  `m = oddPart b`);
* therefore `J(n | b) = J(n | sqfreeKernel m)` for `n` coprime to `b`, and `J(n | b) = 0`
  otherwise.
-/
import Mathlib
import Submission.Work.FIPlan.Interface
import Submission.Work.FIArea4.JacobiChar
import Submission.Work.FIArea4.SqfreeKernel

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.FIArea4

open Work.FIPlan

open scoped BigOperators

noncomputable section

/-! ### The odd part -/

lemma oddPart_pos {b : ℕ} (hb : b ≠ 0) : 0 < oddPart b := Nat.ordCompl_pos 2 hb

lemma oddPart_dvd (b : ℕ) : oddPart b ∣ b := Nat.ordCompl_dvd b 2

lemma oddPart_le (b : ℕ) : oddPart b ≤ b := Nat.ordCompl_le b 2

lemma oddPart_odd {b : ℕ} (hb : b ≠ 0) : Odd (oddPart b) := by
  rw [Nat.odd_iff]
  have h2 : oddPart b % 2 ≠ 0 :=
    fun h0 => Nat.not_dvd_ordCompl Nat.prime_two hb (Nat.dvd_of_mod_eq_zero h0)
  omega

lemma oddPart_mul_two_pow (b : ℕ) : 2 ^ (b.factorization 2) * oddPart b = b :=
  Nat.ordProj_mul_ordCompl_eq_self b 2

lemma oddPart_ne_zero {b : ℕ} (hb : b ≠ 0) : oddPart b ≠ 0 := (oddPart_pos hb).ne'

/-! ### The two-adic factor of the Jacobi symbol -/

lemma jacobiSym_two_eq_one_of_odd {n : ℕ} (hn : Odd n) : jacobiSym (n : ℤ) 2 = 1 := by
  have h2 : (n : ZMod 2) = 1 := by
    have h : n % 2 = 1 := Nat.odd_iff.mp hn
    rw [show (1 : ZMod 2) = ((1 : ℕ) : ZMod 2) from by norm_num,
      ZMod.natCast_eq_natCast_iff]
    show n % 2 = 1 % 2
    omega
  have hJ : jacobiSym (n : ℤ) 2 = legendreSym 2 (n : ℤ) :=
    (jacobiSym.legendreSym.to_jacobiSym 2 (n : ℤ)).symm
  rw [hJ, legendreSym]
  simp [h2]

lemma jacobiSym_two_pow_eq_one_of_odd {n e : ℕ} (hn : Odd n) :
    jacobiSym (n : ℤ) (2 ^ e) = 1 := by
  rw [jacobiSym.pow_right, jacobiSym_two_eq_one_of_odd hn, one_pow]

end

end Work.FIArea4
