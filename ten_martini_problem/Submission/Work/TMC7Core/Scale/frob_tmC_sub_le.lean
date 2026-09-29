import Mathlib
import Submission.Work.TMC7Core.Cocycle

namespace Work.TMC7Core.Scale

/-- `‖(r : ℂ)‖ = |r|`. -/
private lemma norm_ofReal (r : ℝ) : ‖(r : ℂ)‖ = |r| := by
  rw [Complex.norm_def, Complex.normSq_ofReal, ← sq, Real.sqrt_sq_eq_abs]

/-- The difference of two transfer matrices `tmC lam E y - tmC lam E' y'` has a
single nonzero entry, namely `(E - E') - 2λ(cos 2πy - cos 2πy')`, so its Frobenius
norm is the modulus of that entry. -/
private lemma frob_tmC_sub (lam : ℝ) (E E' : ℂ) (y y' : ℝ) :
    Work.TMC7Core.frob (Work.TMC7Core.tmC lam E y - Work.TMC7Core.tmC lam E' y') =
      ‖(E - E') - ((2 * lam * (Real.cos (2 * Real.pi * y) - Real.cos (2 * Real.pi * y')) : ℝ) : ℂ)‖ := by
  have hmat : Work.TMC7Core.tmC lam E y - Work.TMC7Core.tmC lam E' y' =
      !![(E - E') - ((2 * lam * (Real.cos (2 * Real.pi * y) - Real.cos (2 * Real.pi * y')) : ℝ) : ℂ), 0; 0, 0] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Work.TMC7Core.tmC] <;> ring
  rw [hmat, Work.TMC7Core.frob]
  simp

/-- The transfer matrix `tmC lam E y` is Lipschitz in `(E, y)` with constant
`max 1 (4π|λ|)`. -/
theorem frob_tmC_sub_le (lam : ℝ) (E E' : ℂ) (y y' : ℝ) :
    Work.TMC7Core.frob (Work.TMC7Core.tmC lam E y - Work.TMC7Core.tmC lam E' y') ≤
      max 1 (4 * Real.pi * |lam|) * (‖E - E'‖ + |y - y'|) := by
  rw [frob_tmC_sub]
  calc ‖(E - E') - ((2 * lam * (Real.cos (2 * Real.pi * y) - Real.cos (2 * Real.pi * y')) : ℝ) : ℂ)‖
      ≤ ‖E - E'‖ + ‖((2 * lam * (Real.cos (2 * Real.pi * y) - Real.cos (2 * Real.pi * y')) : ℝ) : ℂ)‖ :=
        norm_sub_le _ _
    _ = ‖E - E'‖ + 2 * |lam| * |Real.cos (2 * Real.pi * y) - Real.cos (2 * Real.pi * y')| := by
        rw [norm_ofReal, abs_mul, abs_mul]; norm_num
    _ ≤ ‖E - E'‖ + 2 * |lam| * (2 * Real.pi * |y - y'|) := by
        have h1 : |Real.cos (2 * Real.pi * y) - Real.cos (2 * Real.pi * y')| ≤
            |2 * Real.pi * y - 2 * Real.pi * y'| := Real.abs_cos_sub_cos_le _ _
        have h2 : |2 * Real.pi * y - 2 * Real.pi * y'| = 2 * Real.pi * |y - y'| := by
          rw [show 2 * Real.pi * y - 2 * Real.pi * y' = 2 * Real.pi * (y - y') by ring, abs_mul, abs_mul,
              abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2), abs_of_nonneg Real.pi_pos.le]
        have h3 : (0 : ℝ) ≤ 2 * |lam| := by positivity
        have h4 := mul_le_mul_of_nonneg_left (h2 ▸ h1) h3
        linarith
    _ = ‖E - E'‖ + 4 * Real.pi * |lam| * |y - y'| := by ring
    _ ≤ max 1 (4 * Real.pi * |lam|) * (‖E - E'‖ + |y - y'|) := by
        have h1 : ‖E - E'‖ ≤ max 1 (4 * Real.pi * |lam|) * ‖E - E'‖ :=
          le_mul_of_one_le_left (norm_nonneg _) (le_max_left _ _)
        have h2 : 4 * Real.pi * |lam| * |y - y'| ≤ max 1 (4 * Real.pi * |lam|) * |y - y'| :=
          mul_le_mul_of_nonneg_right (le_max_right _ _) (abs_nonneg _)
        calc ‖E - E'‖ + 4 * Real.pi * |lam| * |y - y'|
            ≤ max 1 (4 * Real.pi * |lam|) * ‖E - E'‖ + max 1 (4 * Real.pi * |lam|) * |y - y'| :=
              add_le_add h1 h2
          _ = max 1 (4 * Real.pi * |lam|) * (‖E - E'‖ + |y - y'|) := by ring

end Work.TMC7Core.Scale
