import Mathlib
import Submission.Work.FatouL1.hcDerivKernel
import Submission.Work.FatouL1.normSqSinComplex
import Submission.Work.FatouL1.normSqCosComplex
import Submission.Work.FatouL1.integral_cosh_div_sinh3
import Submission.Work.FatouL1.sinSqPiLamLower

/-!
# The derivative kernel `2π² cos (π w) / sin (π w)³` on a vertical line inside the fundamental
strip, at distance `lam ∈ [1/8, 7/8]` to the left of the pole

Shishikura's proof needs the Cauchy-derivative kernel `-2π² cos (π (w - z)) / sin (π (w - z))³`
bound along the vertical line `Re w = c`, where `Re z = c + lam`.  The companion file
`Work.FatouL1.hcDerivKernel` treats the rigid case `lam = 1/2`; here `lam` is only assumed to lie
in `[1/8, 7/8]`, so `w - z = -lam + i t` stays at distance at least `1/8` from the pole lattice.

Writing `u = π t`, the modulus of the kernel is

  `2π² √(cos (π lam)² + sinh u²) / (sin (π lam)² + sinh u²)^{3/2}`

(by `normSqSinComplex` / `normSqCosComplex`), which we dominate by replacing `cos (π lam)²` with
`1` and `sin (π lam)²` with `1/7 ≤ sin (π lam)²` (`sinSqPiLamLower`), giving

  `2π² cosh u / (1/7 + sinh u²)^{3/2}`.

The integral of this majorant over `ℝ` is `4π / (1/7) = 28π ≈ 88 < 100`
(`integral_cosh_div_sinh3` with `A = 1/7`), which yields the stated bound `100 · S`.
-/

namespace Work.FatouL1

open MeasureTheory

/-- The universal majorant for the kernel, with `A = 1/7`:
`cosh (π t) / ((1/7 + sinh (π t)²) √(1/7 + sinh (π t)²))`. -/
noncomputable def lamMajorant (t : ℝ) : ℝ :=
  Real.cosh (Real.pi * t) /
    ((1 / 7 + Real.sinh (Real.pi * t) ^ 2) * Real.sqrt (1 / 7 + Real.sinh (Real.pi * t) ^ 2))

/-- Pointwise bound for the kernel on a vertical line at distance `lam ∈ [1/8, 7/8]` to the left of
the pole.  For `w : ℂ` with `w.re = -lam` one has
`‖sin (π w)‖² = sin (π lam)² + sinh (π w.im)²` and
`‖cos (π w)‖² = cos (π lam)² + sinh (π w.im)²`; since `sin (π lam)² ≥ 1/7` the quotient is dominated
by `2π² · lamMajorant w.im`. -/
lemma norm_ker_le_aux {lam t : ℝ} (w : ℂ)
    (hA : 1 / 7 ≤ Real.sin (Real.pi * lam) ^ 2) (hwre : w.re = -lam) (hwim : w.im = t) :
    ‖(2 : ℂ) * (Real.pi : ℂ) ^ 2 * Complex.cos (Real.pi * w) /
        (Complex.sin (Real.pi * w)) ^ 3‖ ≤ 2 * Real.pi ^ 2 * lamMajorant t := by
  have hpwre : (Real.pi * w).re = -(Real.pi * lam) := by
    rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, hwre]; ring
  have hpwim : (Real.pi * w).im = Real.pi * t := by
    rw [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, hwim]; ring
  have hcos2 : ‖Complex.cos (Real.pi * w)‖ ^ 2
      = Real.cos (Real.pi * lam) ^ 2 + Real.sinh (Real.pi * t) ^ 2 := by
    rw [normSqCosComplex, hpwre, hpwim, Real.cos_neg]
  have hsin2 : ‖Complex.sin (Real.pi * w)‖ ^ 2
      = Real.sin (Real.pi * lam) ^ 2 + Real.sinh (Real.pi * t) ^ 2 := by
    rw [normSqSinComplex, hpwre, hpwim, Real.sin_neg]
    ring
  have hcos_le : ‖Complex.cos (Real.pi * w)‖ ≤ Real.cosh (Real.pi * t) := by
    have hsq : ‖Complex.cos (Real.pi * w)‖ ^ 2 ≤ Real.cosh (Real.pi * t) ^ 2 := by
      rw [hcos2, Real.cosh_sq]
      nlinarith [Real.cos_sq_le_one (Real.pi * lam)]
    have h := Real.sqrt_le_sqrt hsq
    rwa [Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq (Real.cosh_pos _).le] at h
  have hsin_lb : 1 / 7 + Real.sinh (Real.pi * t) ^ 2 ≤ ‖Complex.sin (Real.pi * w)‖ ^ 2 := by
    rw [hsin2]; linarith
  have hsin_ge : Real.sqrt (1 / 7 + Real.sinh (Real.pi * t) ^ 2)
      ≤ ‖Complex.sin (Real.pi * w)‖ := by
    have h := Real.sqrt_le_sqrt hsin_lb
    rwa [Real.sqrt_sq (norm_nonneg _)] at h
  have hDpos : 0 < (1 / 7 + Real.sinh (Real.pi * t) ^ 2)
      * Real.sqrt (1 / 7 + Real.sinh (Real.pi * t) ^ 2) := by positivity
  have hDle : (1 / 7 + Real.sinh (Real.pi * t) ^ 2)
      * Real.sqrt (1 / 7 + Real.sinh (Real.pi * t) ^ 2)
      ≤ ‖Complex.sin (Real.pi * w)‖ ^ 3 := by
    have h := mul_le_mul hsin_lb hsin_ge (Real.sqrt_nonneg _) (sq_nonneg _)
    calc (1 / 7 + Real.sinh (Real.pi * t) ^ 2)
          * Real.sqrt (1 / 7 + Real.sinh (Real.pi * t) ^ 2)
        ≤ ‖Complex.sin (Real.pi * w)‖ ^ 2 * ‖Complex.sin (Real.pi * w)‖ := h
      _ = ‖Complex.sin (Real.pi * w)‖ ^ 3 := by ring
  have hker : ‖(2 : ℂ) * (Real.pi : ℂ) ^ 2 * Complex.cos (Real.pi * w) /
      (Complex.sin (Real.pi * w)) ^ 3‖
      = 2 * Real.pi ^ 2 * (‖Complex.cos (Real.pi * w)‖ / ‖Complex.sin (Real.pi * w)‖ ^ 3) := by
    rw [norm_div, norm_mul, norm_mul, norm_pow, norm_pow, Complex.norm_ofNat,
      Complex.norm_of_nonneg Real.pi_pos.le]
    ring_nf
  rw [hker, lamMajorant]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact div_le_div₀ (Real.cosh_pos _).le hcos_le hDpos hDle

theorem hcDerivKernelLam {c lam S : ℝ} {z : ℂ} {h : ℂ → ℂ}
    (hlam : z.re = c + lam) (hlam1 : 1 / 8 ≤ lam) (hlam2 : lam ≤ 7 / 8) (hS : 0 ≤ S)
    (hh : ∀ y : ℝ, ‖h ((c : ℂ) + (y : ℂ) * Complex.I)‖ ≤ S) :
    ‖∫ y : ℝ, h ((c : ℂ) + (y : ℂ) * Complex.I) *
        ((2 : ℂ) * (Real.pi : ℂ) ^ 2 * Complex.cos (Real.pi * ((c : ℂ) + (y : ℂ) * Complex.I - z)) /
          (Complex.sin (Real.pi * ((c : ℂ) + (y : ℂ) * Complex.I - z))) ^ 3)‖ ≤ 100 * S := by
  have hA : 1 / 7 ≤ Real.sin (Real.pi * lam) ^ 2 := sinSqPiLamLower hlam1 hlam2
  obtain ⟨hInt, hVal⟩ := integral_cosh_div_sinh3 z.im (1 / 7) (by norm_num)
  have hIntL : Integrable (fun y : ℝ => lamMajorant (y - z.im)) := by
    simpa [lamMajorant] using hInt
  have hvalL : ∫ y : ℝ, lamMajorant (y - z.im) = 2 / (Real.pi * (1 / 7)) := by
    simpa [lamMajorant] using hVal
  have hGintS : Integrable
      (fun y : ℝ => S * (2 * Real.pi ^ 2 * lamMajorant (y - z.im))) :=
    (hIntL.const_mul (2 * Real.pi ^ 2)).const_mul S
  have hpt : ∀ y : ℝ, ‖h ((c : ℂ) + (y : ℂ) * Complex.I) *
      ((2 : ℂ) * (Real.pi : ℂ) ^ 2 * Complex.cos (Real.pi * ((c : ℂ) + (y : ℂ) * Complex.I - z)) /
        (Complex.sin (Real.pi * ((c : ℂ) + (y : ℂ) * Complex.I - z))) ^ 3)‖
      ≤ S * (2 * Real.pi ^ 2 * lamMajorant (y - z.im)) := by
    intro y
    rw [norm_mul]
    have hwre : (((c : ℂ) + (y : ℂ) * Complex.I - z)).re = -lam := by
      have : (((c : ℂ) + (y : ℂ) * Complex.I - z)).re = c - z.re := by simp
      rw [this, hlam]; ring
    have hwim : (((c : ℂ) + (y : ℂ) * Complex.I - z)).im = y - z.im := by simp
    have hker := norm_ker_le_aux ((c : ℂ) + (y : ℂ) * Complex.I - z) hA hwre hwim
    exact mul_le_mul (hh y) hker (norm_nonneg _) hS
  calc ‖∫ y : ℝ, h ((c : ℂ) + (y : ℂ) * Complex.I) *
        ((2 : ℂ) * (Real.pi : ℂ) ^ 2 * Complex.cos (Real.pi * ((c : ℂ) + (y : ℂ) * Complex.I - z)) /
          (Complex.sin (Real.pi * ((c : ℂ) + (y : ℂ) * Complex.I - z))) ^ 3)‖
      ≤ ∫ y : ℝ, S * (2 * Real.pi ^ 2 * lamMajorant (y - z.im)) :=
        norm_integral_le_of_norm_le hGintS (Filter.Eventually.of_forall hpt)
    _ = S * (2 * Real.pi ^ 2 * (2 / (Real.pi * (1 / 7)))) := by
        rw [integral_const_mul, integral_const_mul, hvalL]
    _ ≤ 100 * S := by
        have hSle : 2 * Real.pi ^ 2 * (2 / (Real.pi * (1 / 7))) ≤ 100 := by
          have heq : 2 * Real.pi ^ 2 * (2 / (Real.pi * (1 / 7))) = 28 * Real.pi := by
            field_simp; ring
          rw [heq]; nlinarith [Real.pi_lt_d2]
        have h := mul_le_mul_of_nonneg_left hSle hS
        rwa [mul_comm S 100] at h

end Work.FatouL1
