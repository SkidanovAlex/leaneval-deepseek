import Mathlib
import Submission.Work.Resample.auCWDefs

namespace Work.Resample

/-- `4^p = (2^p)^2` over `ℤ`. -/
private theorem four_pow_eq (p : ℕ) : (4 : ℤ) ^ p = ((2 : ℤ) ^ p) ^ 2 := by
  rw [show (4 : ℤ) = (2 : ℤ) ^ 2 by norm_num, ← pow_mul, Nat.mul_comm, pow_mul]

/-- From `z^2 ≤ 4^p` (over `ℤ`) deduce `|z| ≤ 2^p`. -/
private theorem natAbs_le_two_pow_of_sq_le (p : ℕ) (z : ℤ) (hz : z ^ 2 ≤ (4 : ℤ) ^ p) :
    z.natAbs ≤ 2 ^ p := by
  have hz2 : (z.natAbs : ℤ) ^ 2 ≤ ((2 : ℤ) ^ p) ^ 2 := by
    rw [Int.natAbs_sq z, ← four_pow_eq p]
    exact hz
  have h := sq_le_sq.mp hz2
  simp only [abs_of_nonneg (by positivity : (0 : ℤ) ≤ (z.natAbs : ℤ)),
    abs_of_nonneg (by positivity : (0 : ℤ) ≤ (2 : ℤ) ^ p)] at h
  exact_mod_cast h

/-- `(2^p * 2^p : ℕ)` cast to `ℤ` is the shift `awSh p = 2^{2p}`. -/
private theorem cast_two_pow_mul (p : ℕ) : ((2 ^ p * 2 ^ p : ℕ) : ℤ) = awSh p := by
  have h1 : (2 ^ p * 2 ^ p : ℕ) = 2 ^ (2 * p) := by
    rw [← pow_two, ← pow_mul]
    congr 1
    ring
  rw [h1, awSh]
  exact_mod_cast rfl

theorem auCWDisc (p : ℕ) (W x y : ℤ) (hp : 1 ≤ p) (hW : W.natAbs ≤ 2 ^ p) (hxy : x ^ 2 + y ^ 2 ≤ 4 ^ p) :
    x.natAbs ≤ 2 ^ p ∧ y.natAbs ≤ 2 ^ p ∧
    0 ≤ W * x + Work.Resample.awSh p ∧ W * x + Work.Resample.awSh p ≤ Work.Resample.awMod p ∧
    0 ≤ W * y + Work.Resample.awSh p ∧ W * y + Work.Resample.awSh p ≤ Work.Resample.awMod p := by
  have hx : x.natAbs ≤ 2 ^ p :=
    natAbs_le_two_pow_of_sq_le p x (by linarith [sq_nonneg y])
  have hy : y.natAbs ≤ 2 ^ p :=
    natAbs_le_two_pow_of_sq_le p y (by linarith [sq_nonneg x])
  -- `|W * z| ≤ awSh p` whenever `|z| ≤ 2^p`
  have key : ∀ z : ℤ, z.natAbs ≤ 2 ^ p → -(awSh p) ≤ W * z ∧ W * z ≤ awSh p := by
    intro z hz
    have hwz : (W * z).natAbs ≤ 2 ^ p * 2 ^ p := by
      rw [Int.natAbs_mul]; exact Nat.mul_le_mul hW hz
    have hAbs : |W * z| ≤ awSh p := by
      rw [Int.abs_eq_natAbs]
      calc ((W * z).natAbs : ℤ) ≤ ((2 ^ p * 2 ^ p : ℕ) : ℤ) := by exact_mod_cast hwz
        _ = awSh p := cast_two_pow_mul p
    exact abs_le.mp hAbs
  obtain ⟨hWx1, hWx2⟩ := key x hx
  obtain ⟨hWy1, hWy2⟩ := key y hy
  refine ⟨hx, hy, by linarith, ?_, by linarith, ?_⟩
  · rw [awMod_eq_shift]; linarith
  · rw [awMod_eq_shift]; linarith

end Work.Resample
