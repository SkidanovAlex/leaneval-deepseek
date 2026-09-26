import Mathlib
import Submission.Work.Kernels.LogLambda.ThetaLaws

/-!
# Positivity of the Jacobi theta functions on the imaginary axis

For `y > 0` the three functions

* `θ₃(iy) = jacobiTheta (i y) = ∑_{n ∈ ℤ} exp (-π y n²)`,
* `θ₄(iy) = jacobiTheta₂ (1/2) (i y) = ∑_{n ∈ ℤ} (-1)^n exp (-π y n²)`,
* `θ₂(iy) = jacobiTheta₂ (i y / 2) (i y) = 2 (1 + ∑_{k ≥ 1} exp (-π y (k² + k)))`

are positive real numbers.  The first and the third are manifestly sums of positive real
summands.  For `θ₄` we use Jacobi's imaginary transformation
`jacobiTheta₂ z τ = (-i τ)^{-1/2} exp (-π i z²/τ) jacobiTheta₂ (z/τ) (-1/τ)`
with `z = 1/2`, `τ = i y`: it expresses `θ₄(iy)` as
`y^{-1/2} exp (-π/(4y)) · θ₂(i/y)`, a product of three positive real numbers.
-/

namespace Work.Analysis.ThetaReal

/-- A sum of nonnegative real numbers one of which is positive is a positive real number,
and its image under the cast `ℝ → ℂ` is the sum of the images. -/
lemma exists_pos_real_tsum_ofReal {ι : Type*} (g : ι → ℝ) (hsum : Summable g)
    (hnn : ∀ i, 0 ≤ g i) (i₀ : ι) (hpos : 0 < g i₀) :
    ∃ r : ℝ, 0 < r ∧ (∑' i, (g i : ℂ)) = (r : ℂ) :=
  ⟨∑' i, g i, Summable.tsum_pos hsum hnn i₀ hpos, (Complex.ofReal_tsum g).symm⟩

/-- The imaginary part of `i y`, for `y` real. -/
@[simp] lemma mul_I_im (y : ℝ) : ((y : ℂ) * Complex.I).im = y := by
  simp

/-! ### The individual summands on the imaginary axis -/

/-- The `n`-th summand of `jacobiTheta (i y) = jacobiTheta₂ 0 (i y)` is the positive real
number `exp (-π y n²)`. -/
lemma jacobiTheta₂_term_imag_zero (y : ℝ) (n : ℤ) :
    jacobiTheta₂_term n 0 ((y : ℂ) * Complex.I) =
      ((Real.exp (-(Real.pi * y * (n : ℝ) ^ 2)) : ℝ) : ℂ) := by
  rw [jacobiTheta₂_term]
  rw [show 2 * ↑Real.pi * Complex.I * ↑n * (0 : ℂ) +
        ↑Real.pi * Complex.I * ↑n ^ 2 * ((y : ℂ) * Complex.I)
        = ↑(-(Real.pi * y * (n : ℝ) ^ 2)) from by
      push_cast; ring_nf; rw [Complex.I_sq]; ring]
  rw [Complex.ofReal_exp]

/-- The `n`-th summand of `jacobiTheta₂ (i y / 2) (i y)` is the positive real number
`exp (-π y (n² + n))`. -/
lemma jacobiTheta₂_term_imag_half (y : ℝ) (n : ℤ) :
    jacobiTheta₂_term n (((y : ℂ) * Complex.I) / 2) ((y : ℂ) * Complex.I) =
      ((Real.exp (-(Real.pi * y * ((n : ℝ) ^ 2 + (n : ℝ)))) : ℝ) : ℂ) := by
  rw [jacobiTheta₂_term]
  rw [show 2 * ↑Real.pi * Complex.I * ↑n * (((y : ℂ) * Complex.I) / 2) +
        ↑Real.pi * Complex.I * ↑n ^ 2 * ((y : ℂ) * Complex.I)
        = ↑(-(Real.pi * y * ((n : ℝ) ^ 2 + (n : ℝ)))) from by
      push_cast; ring_nf; rw [Complex.I_sq]; ring]
  rw [Complex.ofReal_exp]

/-! ### The three positivities -/

/-- `θ₃(i y) = jacobiTheta (i y)` is a positive real number for `y > 0`. -/
lemma jacobiTheta_imag_pos (y : ℝ) (hy : 0 < y) :
    ∃ r : ℝ, 0 < r ∧ jacobiTheta ((y : ℂ) * Complex.I) = ↑r := by
  have hterm : ∀ n : ℤ, jacobiTheta₂_term n 0 ((y : ℂ) * Complex.I)
      = ((Real.exp (-(Real.pi * y * (n : ℝ) ^ 2)) : ℝ) : ℂ) :=
    fun n => jacobiTheta₂_term_imag_zero y n
  have hsumm : Summable (fun n : ℤ => jacobiTheta₂_term n 0 ((y : ℂ) * Complex.I)) :=
    (summable_jacobiTheta₂_term_iff 0 _).mpr (by simpa using hy)
  have hsummR : Summable (fun n : ℤ => Real.exp (-(Real.pi * y * (n : ℝ) ^ 2))) :=
    Complex.summable_ofReal.mp (hsumm.congr hterm)
  obtain ⟨r, hr, hreq⟩ :=
    exists_pos_real_tsum_ofReal _ hsummR (fun n => (Real.exp_pos _).le) 0 (by simp)
  refine ⟨r, hr, ?_⟩
  rw [jacobiTheta_eq_jacobiTheta₂, jacobiTheta₂,
    show (∑' n : ℤ, jacobiTheta₂_term n 0 ((y : ℂ) * Complex.I))
        = ∑' n : ℤ, ((Real.exp (-(Real.pi * y * (n : ℝ) ^ 2)) : ℝ) : ℂ) from
      tsum_congr hterm,
    hreq]

/-- `jacobiTheta₂ (i y / 2) (i y)` is a positive real number for `y > 0`; equivalently,
`θ₂(i y) / 2 = 1 + ∑_{k ≥ 1} exp (-π y (k² + k))`. -/
lemma jacobiTheta₂_half_arg_imag_pos (y : ℝ) (hy : 0 < y) :
    ∃ r : ℝ, 0 < r ∧ jacobiTheta₂ (((y : ℂ) * Complex.I) / 2) ((y : ℂ) * Complex.I) = ↑r := by
  have hterm : ∀ n : ℤ, jacobiTheta₂_term n (((y : ℂ) * Complex.I) / 2) ((y : ℂ) * Complex.I)
      = ((Real.exp (-(Real.pi * y * ((n : ℝ) ^ 2 + (n : ℝ)))) : ℝ) : ℂ) :=
    fun n => jacobiTheta₂_term_imag_half y n
  have hsumm : Summable
      (fun n : ℤ => jacobiTheta₂_term n (((y : ℂ) * Complex.I) / 2) ((y : ℂ) * Complex.I)) :=
    (summable_jacobiTheta₂_term_iff _ _).mpr (by simpa using hy)
  have hsummR : Summable (fun n : ℤ => Real.exp (-(Real.pi * y * ((n : ℝ) ^ 2 + (n : ℝ))))) :=
    Complex.summable_ofReal.mp (hsumm.congr hterm)
  obtain ⟨r, hr, hreq⟩ :=
    exists_pos_real_tsum_ofReal _ hsummR (fun n => (Real.exp_pos _).le) 0 (by simp)
  refine ⟨r, hr, ?_⟩
  rw [jacobiTheta₂,
    show (∑' n : ℤ, jacobiTheta₂_term n (((y : ℂ) * Complex.I) / 2) ((y : ℂ) * Complex.I))
        = ∑' n : ℤ, ((Real.exp (-(Real.pi * y * ((n : ℝ) ^ 2 + (n : ℝ)))) : ℝ) : ℂ) from
      tsum_congr hterm,
    hreq]

/-- `θ₄(i y) = jacobiTheta₂ (1/2) (i y)` is a positive real number for `y > 0`. -/
lemma jacobiTheta₂_one_half_imag_pos (y : ℝ) (hy : 0 < y) :
    ∃ r : ℝ, 0 < r ∧ jacobiTheta₂ (1 / 2) ((y : ℂ) * Complex.I) = ↑r := by
  obtain ⟨b, hb, hbeq⟩ := jacobiTheta₂_half_arg_imag_pos (1 / y) (one_div_pos.mpr hy)
  have hA : -Complex.I * ((y : ℂ) * Complex.I) = (y : ℂ) := by
    rw [show -Complex.I * (↑y * Complex.I) = -(↑y * (Complex.I * Complex.I)) by ring,
      Complex.I_mul_I]
    ring
  have hE : (1 : ℂ) / ((y : ℂ)) ^ (1 / 2 : ℂ) = ↑(1 / Real.sqrt y) := by
    rw [show ((y : ℂ)) ^ (1 / 2 : ℂ) = ↑(Real.sqrt y) from by
          rw [show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by norm_num,
            ← Complex.ofReal_cpow hy.le (1 / 2), Real.sqrt_eq_rpow]]
    rw [← Complex.ofReal_one, ← Complex.ofReal_div]
  have hB : Complex.exp (-↑Real.pi * Complex.I * (1 / 2 : ℂ) ^ 2 / ((y : ℂ) * Complex.I))
      = ↑(Real.exp (-(Real.pi / (4 * y)))) := by
    rw [show -↑Real.pi * Complex.I * (1 / 2 : ℂ) ^ 2 / ((y : ℂ) * Complex.I)
          = ↑(-(Real.pi / (4 * y))) from by
        field_simp; push_cast; ring, Complex.ofReal_exp]
  have hC : (1 / 2 : ℂ) / ((y : ℂ) * Complex.I) = -((((1 / y : ℝ) : ℂ) * Complex.I) / 2) := by
    field_simp; rw [Complex.I_sq]; push_cast; ring
  have hD : -1 / ((y : ℂ) * Complex.I) = ((1 / y : ℝ) : ℂ) * Complex.I := by
    field_simp; rw [Complex.I_sq]; push_cast; ring
  refine ⟨1 / Real.sqrt y * Real.exp (-(Real.pi / (4 * y))) * b, ?_, ?_⟩
  · exact mul_pos (mul_pos (one_div_pos.mpr (Real.sqrt_pos.mpr hy)) (Real.exp_pos _)) hb
  · rw [jacobiTheta₂_functional_equation, hA, hE, hB, hC, hD, jacobiTheta₂_neg_left, hbeq]
    push_cast
    ring

theorem imagAxis_theta_pos (y : ℝ) (hy : 0 < y) :
    (∃ r : ℝ, 0 < r ∧ jacobiTheta ((y : ℂ) * Complex.I) = ↑r) ∧
    (∃ r : ℝ, 0 < r ∧ jacobiTheta₂ (1 / 2) ((y : ℂ) * Complex.I) = ↑r) ∧
    (∃ r : ℝ, 0 < r ∧ jacobiTheta₂ (((y : ℂ) * Complex.I) / 2) ((y : ℂ) * Complex.I) / 2 = ↑r) := by
  refine ⟨jacobiTheta_imag_pos y hy, jacobiTheta₂_one_half_imag_pos y hy, ?_⟩
  obtain ⟨r, hr, hreq⟩ := jacobiTheta₂_half_arg_imag_pos y hy
  refine ⟨r / 2, by linarith, ?_⟩
  rw [hreq]
  push_cast
  ring

end Work.Analysis.ThetaReal
