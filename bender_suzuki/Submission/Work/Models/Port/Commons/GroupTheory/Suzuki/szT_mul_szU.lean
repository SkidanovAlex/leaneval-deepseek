import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Submission.Work.Models.Port.Commons.FieldTheory.FiniteField.galoisField_pow_two_pow_succ_succ

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Commons.GroupTheory.Suzuki

open Matrix

set_option linter.unusedSimpArgs false

theorem szT_mul_szU (n : ℕ) (x : (GaloisField 2 (2 * n + 1))ˣ)
    (a b : GaloisField 2 (2 * n + 1)) :
    !![(x : GaloisField 2 (2 * n + 1)) ^ (1 + 2 ^ n), 0, 0, 0;
       0, (x : GaloisField 2 (2 * n + 1)) ^ (2 ^ n), 0, 0;
       0, 0, ((x : GaloisField 2 (2 * n + 1)) ^ (2 ^ n))⁻¹, 0;
       0, 0, 0, ((x : GaloisField 2 (2 * n + 1)) ^ (1 + 2 ^ n))⁻¹] *
    !![1, a, b, a ^ (2 + 2 ^ (n + 1)) + a * b + b ^ (2 ^ (n + 1));
       0, 1, a ^ (2 ^ (n + 1)), a ^ (1 + 2 ^ (n + 1)) + b;
       0, 0, 1, a;
       0, 0, 0, 1]
    =
    !![1, (x : GaloisField 2 (2 * n + 1)) * a,
         (x : GaloisField 2 (2 * n + 1)) ^ (1 + 2 ^ (n + 1)) * b,
         ((x : GaloisField 2 (2 * n + 1)) * a) ^ (2 + 2 ^ (n + 1))
           + (x : GaloisField 2 (2 * n + 1)) * a
             * ((x : GaloisField 2 (2 * n + 1)) ^ (1 + 2 ^ (n + 1)) * b)
           + ((x : GaloisField 2 (2 * n + 1)) ^ (1 + 2 ^ (n + 1)) * b) ^ (2 ^ (n + 1));
       0, 1, ((x : GaloisField 2 (2 * n + 1)) * a) ^ (2 ^ (n + 1)),
         ((x : GaloisField 2 (2 * n + 1)) * a) ^ (1 + 2 ^ (n + 1))
           + (x : GaloisField 2 (2 * n + 1)) ^ (1 + 2 ^ (n + 1)) * b;
       0, 0, 1, (x : GaloisField 2 (2 * n + 1)) * a;
       0, 0, 0, 1] *
    !![(x : GaloisField 2 (2 * n + 1)) ^ (1 + 2 ^ n), 0, 0, 0;
       0, (x : GaloisField 2 (2 * n + 1)) ^ (2 ^ n), 0, 0;
       0, 0, ((x : GaloisField 2 (2 * n + 1)) ^ (2 ^ n))⁻¹, 0;
       0, 0, 0, ((x : GaloisField 2 (2 * n + 1)) ^ (1 + 2 ^ n))⁻¹] := by
  set z : GaloisField 2 (2 * n + 1) := (x : GaloisField 2 (2 * n + 1)) with hzdef
  have hz : z ≠ 0 := by rw [hzdef]; exact Units.ne_zero x
  set y : GaloisField 2 (2 * n + 1) := z ^ (2 ^ n) with hydef
  have hy : y ≠ 0 := by rw [hydef]; exact pow_ne_zero _ hz
  have hpow : 2 ^ n + 2 ^ n = 2 ^ (n + 1) := by rw [← two_mul, ← pow_succ']
  have hA : z ^ (2 ^ (n + 1)) = y ^ 2 := by rw [hydef, pow_two, ← pow_add, hpow]
  have hy_pow : y ^ (2 ^ (n + 1)) = z := by
    rw [hydef, ← pow_mul]
    rw [show 2 ^ n * 2 ^ (n + 1) = 2 ^ (2 * n + 1) by rw [← pow_add]; congr 1; omega]
    exact Commons.FieldTheory.FiniteField.galoisField_pow_card_pow_self (p := 2) (2 * n + 1)
      (by omega) z
  have hy_pow6 : y ^ (2 * 2 ^ n) = z := by
    rw [show 2 * 2 ^ n = 2 ^ (n + 1) by rw [← pow_succ'], hy_pow]
  have hy_pow5 : (y ^ 2) ^ (2 ^ n) = z := by
    rw [← pow_mul, show 2 * 2 ^ n = 2 ^ (n + 1) by rw [← pow_succ'], hy_pow]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_four]
  all_goals
    simp only [mul_pow, pow_add, pow_one, pow_mul, ← hydef, hA, hy_pow6, hy_pow5, hy_pow]
    try field_simp [hz, hy]
    try ring


end Commons.GroupTheory.Suzuki