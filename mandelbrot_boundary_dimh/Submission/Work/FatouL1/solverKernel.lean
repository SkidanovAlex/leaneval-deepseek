import Mathlib

/-!
# FATOU-L1: the Cauchy–Heine / translation solver kernel

The linear difference operator `Δ u = u (· + 1) - u` on a vertical strip `(a,b) × ℝ` is inverted
by the *Cauchy–Heine* kernel: for `h` holomorphic on the strip and `L¹` along its vertical lines,

  `hcSolver h z = (I/2) * ∫ y, h (z - 1/2 + y*I) * tanh (π y) dy`,

which is holomorphic on the shifted strip `(a + 1/2, b + 1/2) × ℝ`, satisfies
`hcSolver h (z+1) - hcSolver h z = - h z` (so `-hcSolver h` is a right inverse of `Δ`), and obeys
the sharp *mass* bound

  `‖hcSolver h z‖ ≤ (1/2) * ∫ ‖h (z - 1/2 + y*I)‖ dy`.

The contour is placed at distance `1/2` from `z`, i.e. the kernel is `cot (π (s - z))` at
`Re s = Re z - 1/2`; the identity `cot (π (-1/2 + I y)) = -I tanh (π y)` is what makes the kernel
*bounded* (by `1`), and the factor `1/2` is the sharp constant (it is the value of the kernel
`1/(1 - e^{2πi t})` averaged symmetrically, and matches the classical `Σ_n 1/(σ+n) = π cot (πσ)`).

The difference equation is the residue/contour-shift computation: moving the contour from
`Re z - 1/2` to `Re z + 1/2` crosses exactly the simple pole of `cot (π (s-z))` at `s = z`
(residue `1/π`), producing `-h z`.

Compare `Work.FatouCH.kappa` (`κ t = 1 / (1 - e^{2πi t})`), the `1`-periodic form of the same
kernel.
-/

open MeasureTheory
open scoped Topology ENNReal

namespace Work.FatouL1

noncomputable section

/-- The Cauchy–Heine / translation solver of the difference operator `Δ` on a vertical strip. -/
def hcSolver (h : ℂ → ℂ) (z : ℂ) : ℂ :=
  (Complex.I / 2) * ∫ y : ℝ, h (z - 1 / 2 + y * Complex.I) * (Real.tanh (Real.pi * y) : ℂ)

/-- `|tanh| ≤ 1` on the real line (the boundedness of the kernel). -/
lemma abs_tanh_le_one (y : ℝ) : |Real.tanh y| ≤ 1 :=
  abs_le.mpr ⟨le_of_lt (Real.neg_one_lt_tanh y), le_of_lt (Real.tanh_lt_one y)⟩

/-- The kernel is bounded by `1/2`: `‖(I/2) * tanh (π y)‖ ≤ 1/2`. -/
lemma norm_kernel_le (y : ℝ) : ‖(Complex.I / 2) * (Real.tanh (Real.pi * y) : ℂ)‖ ≤ 1 / 2 := by
  have h := abs_tanh_le_one (Real.pi * y)
  have h2 : ‖(2 : ℂ)‖ = 2 := by norm_num
  have h3 : ‖((Real.tanh (Real.pi * y) : ℝ) : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs]; exact h
  calc ‖(Complex.I / 2) * (Real.tanh (Real.pi * y) : ℂ)‖
      = ‖Complex.I‖ / ‖(2 : ℂ)‖ * ‖((Real.tanh (Real.pi * y) : ℝ) : ℂ)‖ := by
        rw [norm_mul, norm_div]
    _ = 1 / 2 * ‖((Real.tanh (Real.pi * y) : ℝ) : ℂ)‖ := by rw [Complex.norm_I, h2]
    _ ≤ 1 / 2 * 1 := by
        exact mul_le_mul_of_nonneg_left h3 (by norm_num)
    _ = 1 / 2 := by norm_num

end

end Work.FatouL1
