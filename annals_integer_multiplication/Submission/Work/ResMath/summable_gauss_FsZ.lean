import Mathlib
import Submission.Work.ResMath.resamplingDefs
import Submission.Work.ResMath.gaussianPoisson
import Submission.Work.ResMath.gaussSumm

/-!
# Summability of a Gaussian times `FsZ` over `ℤ`

`Work.ResMath.summable_gauss_FsZ`: for `s, t, α > 0`, `u : Fin s → ℂ` and `x : ℝ`, the
sequence
`n ↦ exp (-π α² t² (x - n/s)²) * FsZ s u (t n)`
is summable over `ℤ`.

The Gaussian factor is summable (`Work.ResMath.gaussSumm`) and `FsZ s u` is bounded
independently of the index (`Work.ResMath.FsZ_norm_le`, a consequence of the triangle
inequality in the DFT sum), so the product is summable by comparison
(`Summable.of_norm_bounded`).
-/

namespace Work.ResMath

theorem summable_gauss_FsZ (s t α : ℕ) (hs : 0 < s) (ht : 0 < t) (hα : 0 < α)
    (u : Fin s → ℂ) (x : ℝ) :
    Summable (fun n : ℤ =>
      ((Real.exp (-Real.pi * (α : ℝ) ^ 2 * (t : ℝ) ^ 2 * (x - (n : ℝ) / (s : ℝ)) ^ 2)) : ℂ) *
        FsZ s u (t * n)) := by
  have hsR : (0 : ℝ) < (s : ℝ) := by exact_mod_cast hs
  -- The uniform bound on `FsZ`.
  set C : ℝ := (∑ i : Fin s, ‖u i‖) / (s : ℝ) with hCdef
  have hF : ∀ n : ℤ, ‖FsZ s u (t * n)‖ ≤ C := fun n => by
    rw [hCdef]
    exact FsZ_norm_le s hs u (t * n)
  -- Summability of the pure Gaussian factor, written in the centre form `c + n`.
  have hgauss : Summable fun n : ℤ =>
      Real.exp (-Real.pi * (α : ℝ) ^ 2 * (t : ℝ) ^ 2 * (x - (n : ℝ) / (s : ℝ)) ^ 2) := by
    refine (gaussSumm (Real.pi * (α : ℝ) ^ 2 * (t : ℝ) ^ 2 / (s : ℝ) ^ 2)
      (by positivity) (-(x * (s : ℝ)))).congr fun n => ?_
    congr 1
    have hsne : (s : ℝ) ≠ 0 := ne_of_gt hsR
    field_simp
    ring
  -- Comparison against the Gaussian factor times the constant `C`.
  refine Summable.of_norm_bounded (g := fun n : ℤ =>
      Real.exp (-Real.pi * (α : ℝ) ^ 2 * (t : ℝ) ^ 2 * (x - (n : ℝ) / (s : ℝ)) ^ 2) * C)
    (hgauss.mul_right C) ?_
  intro n
  rw [norm_mul]
  have h1 : ‖(((Real.exp (-Real.pi * (α : ℝ) ^ 2 * (t : ℝ) ^ 2 *
        (x - (n : ℝ) / (s : ℝ)) ^ 2)) : ℝ) : ℂ)‖
      = Real.exp (-Real.pi * (α : ℝ) ^ 2 * (t : ℝ) ^ 2 * (x - (n : ℝ) / (s : ℝ)) ^ 2) :=
    by rw [Complex.ofReal_exp, Complex.norm_exp, Complex.ofReal_re]
  rw [h1]
  exact mul_le_mul_of_nonneg_left (hF n) (Real.exp_nonneg _)

end Work.ResMath
