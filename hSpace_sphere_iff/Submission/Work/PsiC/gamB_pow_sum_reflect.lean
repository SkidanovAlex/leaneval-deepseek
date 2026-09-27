import Mathlib
import Submission.Work.KT.PsiC.BFrame
import Submission.Work.PsiC.gamB_decomp

namespace Work.PsiC

/-- **Reflection of a six-term geometric sum.**  For an element `M` of order six and a sixth root
of unity `q`, the geometric sum `∑_{k<6} q^k • (M^5)^k` is unchanged when `q` is replaced by `q⁻¹`
and simultaneously the powers of `M` are reflected.  This is just the substitution `k ↦ 6 - k` on
the six indices, using `M^6 = 1` and `q^6 = 1`. -/
theorem geom6_smul_reflect {B : Type} [Ring B] [Algebra ℂ B] (M : B) (hM : M ^ 6 = 1)
    (q : ℂ) (hq : q ^ 6 = 1) :
    (∑ k ∈ Finset.range 6, q ^ k • (M ^ 5) ^ k) = ∑ k ∈ Finset.range 6, (q⁻¹) ^ k • M ^ k := by
  have hMp : ∀ j : ℕ, M ^ (6 * j) = 1 := by
    intro j; rw [pow_mul, hM, one_pow]
  have hp2 : (M ^ 5) ^ 2 = M ^ 4 := by
    rw [← pow_mul, show (5 * 2 : ℕ) = 10 from rfl, show (10 : ℕ) = 6 + 4 from rfl, pow_add, hM,
      one_mul]
  have hp3 : (M ^ 5) ^ 3 = M ^ 3 := by
    rw [← pow_mul, show (5 * 3 : ℕ) = 15 from rfl, show (15 : ℕ) = 12 + 3 from rfl, pow_add,
      show (12 : ℕ) = 6 * 2 from rfl, hMp 2, one_mul]
  have hp4 : (M ^ 5) ^ 4 = M ^ 2 := by
    rw [← pow_mul, show (5 * 4 : ℕ) = 20 from rfl, show (20 : ℕ) = 18 + 2 from rfl, pow_add,
      show (18 : ℕ) = 6 * 3 from rfl, hMp 3, one_mul]
  have hp5 : (M ^ 5) ^ 5 = M := by
    rw [← pow_mul, show (5 * 5 : ℕ) = 25 from rfl, show (25 : ℕ) = 24 + 1 from rfl, pow_add,
      show (24 : ℕ) = 6 * 4 from rfl, hMp 4, one_mul, pow_one]
  have hqi : ∀ k : ℕ, k ≤ 6 → (q⁻¹) ^ k = q ^ (6 - k) := by
    intro k hk
    rw [inv_pow]
    exact inv_eq_of_mul_eq_one_right (by rw [← pow_add, show k + (6 - k) = 6 from by omega, hq])
  have hq1 : q⁻¹ = q ^ 5 := by simpa using hqi 1 (by norm_num)
  have hq2 : (q⁻¹) ^ 2 = q ^ 4 := by simpa using hqi 2 (by norm_num)
  have hq3 : (q⁻¹) ^ 3 = q ^ 3 := by simpa using hqi 3 (by norm_num)
  have hq4 : (q⁻¹) ^ 4 = q ^ 2 := by simpa using hqi 4 (by norm_num)
  have hq5 : (q⁻¹) ^ 5 = q := by simpa using hqi 5 (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, pow_zero, pow_one, one_smul]
  rw [hp2, hp3, hp4, hp5, hq5, hq4, hq3, hq2, hq1]
  abel

theorem gamB_pow_sum_reflect (A : Type) [Ring A] [Algebra ℂ A] (n : ℕ) (q : ℂ) (hq : q ^ 6 = 1) :
    (∑ k ∈ Finset.range 6, q ^ k • (((Work.KT.PsiC.gamB n).permMatrix A) ^ 5) ^ k) =
      ∑ k ∈ Finset.range 6, (q⁻¹) ^ k • ((Work.KT.PsiC.gamB n).permMatrix A) ^ k :=
  geom6_smul_reflect ((Work.KT.PsiC.gamB n).permMatrix A)
    (Work.PsiC.GamBDecomp.gamB_permMatrix_pow_six A n) q hq

end Work.PsiC
