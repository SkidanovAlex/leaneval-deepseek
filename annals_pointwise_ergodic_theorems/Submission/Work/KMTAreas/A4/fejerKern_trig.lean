import Mathlib
import Submission.Work.KMTAreas.A4.denseMultiples_kern

/-!
# The trigonometric (tent-coefficient) form of the Fejér kernel

`Work.KMTAreas.A4.fejerKern N x = (N+1) * Work.Analysis.Fourier.fejerWin N x` is the classical
(mass `1`) Fejér kernel.  Here we record its trigonometric expansion

`fejerKern N x = ∑_{|n| ≤ N} (1 - |n|/(N+1)) * cos (2 π n x)`,

i.e. the triangular ("tent") coefficients `1 - |n|/(N+1)` on the frequencies `|n| ≤ N`.

The proof goes through the Fourier side: `Work.Analysis.Fourier.fejerPoly N` is the trigonometric
polynomial with coefficients `fejerCoeff N n = (N+1)⁻¹ * max 0 (1 - |n|/(N+1))`, and
`fejer_poly_eq_win` identifies it with `fejerWin N` (as a real number).  Taking real parts of the
exponential sum and multiplying by `(N+1)` gives the statement, because on `|n| ≤ N` the `max` is
inactive: `(N+1) * fejerCoeff N n = 1 - |n|/(N+1)`.
-/

namespace Work.KMTAreas.A4

open scoped BigOperators

noncomputable section

/-- Real part of the character `e^{-2πinx}` is `cos (2πnx)`. -/
private lemma exp_re_cos (n : ℤ) (x : ℝ) :
    (Complex.exp (-(2 * Real.pi * Complex.I * (n : ℂ) * (x : ℂ)))).re
      = Real.cos (2 * Real.pi * (n : ℝ) * x) := by
  have h : -(2 * Real.pi * Complex.I * (n : ℂ) * (x : ℂ))
      = (((-(2 * Real.pi * (n : ℝ) * x)) : ℝ) : ℂ) * Complex.I := by
    push_cast; ring
  rw [h, Complex.exp_ofReal_mul_I,
    Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im]
  simp only [mul_zero, zero_sub]
  rw [Real.cos_neg]; ring

/-- On the support `|n| ≤ N` the normalised Fejér coefficient times `(N+1)` is the tent
coefficient `1 - |n|/(N+1)`. -/
private lemma coeff_mul (N : ℕ) {n : ℤ} (hn : n ∈ Finset.Icc (-(N : ℤ)) (N : ℤ)) :
    ((N : ℝ) + 1) * Work.Analysis.Fourier.fejerCoeff N n = 1 - |(n : ℝ)| / ((N : ℝ) + 1) := by
  obtain ⟨h1, h2⟩ := Finset.mem_Icc.mp hn
  have hle : |(n : ℝ)| ≤ (N : ℝ) := by
    rw [abs_le]
    constructor
    · have h1' : ((-(N : ℤ) : ℤ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast h1
      push_cast at h1'
      linarith
    · have h2' : (n : ℝ) ≤ (N : ℝ) := by exact_mod_cast h2
      linarith
  have hNpos : (0 : ℝ) < (N : ℝ) + 1 := by positivity
  have hpos : 0 ≤ 1 - |(n : ℝ)| / ((N : ℝ) + 1) := by
    have : |(n : ℝ)| / ((N : ℝ) + 1) ≤ 1 := by
      rw [div_le_one hNpos]
      linarith
    linarith
  unfold Work.Analysis.Fourier.fejerCoeff
  rw [max_eq_right hpos]
  have hNne : ((N : ℝ) + 1) ≠ 0 := ne_of_gt hNpos
  field_simp

/-- Real part of the Fejér polynomial, in cosine form. -/
private lemma fejerPoly_re (N : ℕ) (x : ℝ) :
    (Work.Analysis.Fourier.fejerPoly N x).re
      = ∑ n ∈ Finset.Icc (-(N : ℤ)) (N : ℤ),
          Work.Analysis.Fourier.fejerCoeff N n * Real.cos (2 * Real.pi * (n : ℝ) * x) := by
  rw [Work.Analysis.Fourier.fejerPoly, Complex.re_sum]
  refine Finset.sum_congr rfl (fun n _ => ?_)
  rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, exp_re_cos n x]
  ring

theorem fejerKern_trig (N : ℕ) (x : ℝ) : fejerKern N x = ∑ n ∈ Finset.Icc (-(N:ℤ)) (N:ℤ), (1 - |(n:ℝ)|/((N:ℝ)+1)) * Real.cos (2*Real.pi*(n:ℝ)*x) := by
  have hwin : Work.Analysis.Fourier.fejerWin N x = (Work.Analysis.Fourier.fejerPoly N x).re := by
    rw [Work.Analysis.Fourier.fejer_poly_eq_win N x, Complex.ofReal_re]
  unfold fejerKern
  rw [hwin, fejerPoly_re, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun n hn => ?_)
  rw [← mul_assoc, coeff_mul N hn]

end

end Work.KMTAreas.A4
