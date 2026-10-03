import Mathlib
import Submission.Work.FIPlan.Interface

namespace Work.FIArea2

/-- **`z₁ ≡ z₂ (mod 8)` forces `8 ∣ |Δ|`**: if `z₂ − z₁ = 8m` then `8 ∣ Im(z̄₁z₂)`.  This is the paper's "`z₂/z₁ ≡ 1 (mod 8)` … so `ν ⩾ 3`": it gives `ν = ord₂Δ ⩾ 3`, hence `4 ∣ |Δ|`, which is the hypothesis `h4` of the corrected (8.16) `Cnt_eq_two_sum` (and of `Nsol_eq_two_sum_jacobi`).

Sketch: `z̄₁z₂ = z̄₁z₁ + 8z̄₁m` and `z̄₁z₁ = |z₁|² ∈ ℤ`, so `Im(z̄₁z₂) = 8·Im(z̄₁m)`; `absDelta = |Im(z̄₁z₂)|`. -/
theorem eight_dvd_absDelta_of_congr {z1 z2 m : GaussianInt} (h : z2 - z1 = 8 * m) :
    8 ∣ Work.FIPlan.absDelta z1 z2 := by
  have hz2 : z2 = z1 + 8 * m := by rw [← h]; abel
  have hd : Work.FIPlan.Delta z1 z2 = 8 * (star z1 * m).im := by
    rw [Work.FIPlan.Delta, hz2, mul_add]
    simp
    ring
  rw [Work.FIPlan.absDelta, hd, Int.natAbs_mul]
  have h8 : (8 : ℤ).natAbs = 8 := by norm_num
  rw [h8]
  exact dvd_mul_right 8 _

end Work.FIArea2
