import Submission.Commons.NumberTheory.GaussianInt.ncard_assoc_norm_mul
import Submission.Commons.NumberTheory.GaussianInt.two_squares_repr_count

namespace Commons.NumberTheory.GaussianInt

open Zsqrtd

/-- **Splitting a Gaussian integer along coprime factors of its norm.**
If `‖u‖ = m * n` with `m`, `n` coprime and `≥ 1`, then `u` factors as a product
`w * z` with `‖w‖ = m` and `‖z‖ = n`. -/
theorem factor_exists_of_norm_mul {m n : ℕ} (hm : 1 ≤ m) (hn : 1 ≤ n) (hcop : Nat.Coprime m n)
    (u : GaussianInt) (hu : u.norm.natAbs = m * n) :
    ∃ w z : GaussianInt, u = w * z ∧ w.norm.natAbs = m ∧ z.norm.natAbs = n := by
  obtain ⟨hm', hn', hassoc⟩ := norm_gPart_eq_and_associated hm hn hcop hu
  obtain ⟨ε, hε⟩ := hassoc
  refine ⟨gPart m u * (ε : GaussianInt), gPart n u, ?_, ?_, hn'⟩
  · rw [mul_assoc, mul_comm (ε : GaussianInt) (gPart n u), ← mul_assoc]
    exact hε.symm
  · rw [Zsqrtd.norm_mul, Int.natAbs_mul, isUnit_norm_natAbs (ε.isUnit), mul_one, hm']

end Commons.NumberTheory.GaussianInt
