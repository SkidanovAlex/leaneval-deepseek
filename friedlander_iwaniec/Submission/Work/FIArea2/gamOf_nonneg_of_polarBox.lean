import Mathlib
import Submission.Work.FIArea2.sec9_error_Hweight

namespace Work.FIArea2

/-! ## Auxiliary identities about `γ = Re(z̄₁z₂)/(|z₁||z₂|)`

`γ` is the cosine of the angle between `z₁` and `z₂`, and both `gamOf_eq_cos_arg` and the
`Re`-identity it is built on are the "geometric" half of the polar-box lemma: they identify the
algebraic expression `gamOf` with `cos(arg z₂ − arg z₁)`, whose sign on a sector of width
`2πθ ≤ π/2` is then immediate. -/

/-- `‖z‖ = √(gnorm z)` for a Gaussian integer, read through `toComplex`. -/
private lemma sqrt_gnorm_of_cast (z : GaussianInt) :
    Real.sqrt ((Work.FIPlan.gnorm z : ℝ)) = ‖z.toComplex‖ := by
  have h : (Work.FIPlan.gnorm z : ℝ) = ‖z.toComplex‖ ^ 2 := by
    rw [Work.FIPlan.gnorm, GaussianInt.natCast_natAbs_norm, GaussianInt.intCast_real_norm,
      Complex.normSq_eq_norm_sq]
  rw [h, Real.sqrt_sq (norm_nonneg _)]

/-- `Re(z̄₁z₂) = |z₁||z₂|·cos(arg z₂ − arg z₁)`: the real part of `z̄₁z₂` is the scalar product
of the two vectors, i.e. the product of the moduli times the cosine of the angle between them
(the analogue, for the real part, of
`Work.FIArea4.im_star_mul`/`Work.FIArea4.im_starRingEnd_mul` for the imaginary part). -/
lemma re_star_mul (z1 z2 : GaussianInt) :
    ((star z1 * z2 : GaussianInt) : ℂ).re
      = ‖(z1 : ℂ)‖ * ‖(z2 : ℂ)‖
        * Real.cos (Complex.arg (z2 : ℂ) - Complex.arg (z1 : ℂ)) := by
  have h1 := Complex.norm_mul_cos_arg (z1 : ℂ)
  have h2 := Complex.norm_mul_sin_arg (z1 : ℂ)
  have h3 := Complex.norm_mul_cos_arg (z2 : ℂ)
  have h4 := Complex.norm_mul_sin_arg (z2 : ℂ)
  rw [GaussianInt.toComplex_mul, GaussianInt.toComplex_star, Complex.mul_re,
    Complex.conj_re, Complex.conj_im, Real.cos_sub, ← h1, ← h4, ← h3, ← h2]
  ring

/-- `γ = gamOf z₁ z₂ = cos(arg z₂ − arg z₁)` for nonzero Gaussian integers: the normalised real
part of `z̄₁z₂` is the cosine of the angle between the two arguments.  (Both `z_j` must be
nonzero; `gamOf` is `0` as soon as one of them vanishes, while the cosine need not be.) -/
lemma gamOf_eq_cos_arg (z1 z2 : GaussianInt) (h1 : z1 ≠ 0) (h2 : z2 ≠ 0) :
    gamOf z1 z2
      = Real.cos (Complex.arg z2.toComplex - Complex.arg z1.toComplex) := by
  have hnum : (((star z1 * z2).re : ℤ) : ℝ)
      = ‖z1.toComplex‖ * ‖z2.toComplex‖
        * Real.cos (Complex.arg z2.toComplex - Complex.arg z1.toComplex) := by
    rw [← Complex.ofReal_re (((star z1 * z2).re : ℤ) : ℝ), GaussianInt.intCast_re]
    simp only [Complex.ofReal_re]
    have h1' := Complex.norm_mul_cos_arg z1.toComplex
    have h2' := Complex.norm_mul_sin_arg z1.toComplex
    have h3' := Complex.norm_mul_cos_arg z2.toComplex
    have h4' := Complex.norm_mul_sin_arg z2.toComplex
    rw [GaussianInt.toComplex_mul, GaussianInt.toComplex_star, Complex.mul_re,
      Complex.conj_re, Complex.conj_im, Real.cos_sub, ← h1', ← h4', ← h3', ← h2']
    ring
  have hden : Real.sqrt ((((Work.FIPlan.gnorm z1 : ℕ) : ℝ))
        * (((Work.FIPlan.gnorm z2 : ℕ) : ℝ)))
      = ‖z1.toComplex‖ * ‖z2.toComplex‖ := by
    rw [Real.sqrt_mul (by positivity), sqrt_gnorm_of_cast z1, sqrt_gnorm_of_cast z2]
  rw [gamOf, hnum, hden]
  exact mul_div_cancel_left₀ _
    (mul_ne_zero (ne_of_gt (norm_pos_iff.mpr (by simpa using h1)))
      (ne_of_gt (norm_pos_iff.mpr (by simpa using h2))))

/-- **`γ ≥ 0` on the polar box.**  If `z₁,z₂` lie in the same polar box (5.14) — the sector
`φ < arg z ≤ φ + 2πθ` of width `≤ π/2` intersected with the annulus `(N,(1+θ)N]` — then
`γ = Re(z̄₁z₂)/(|z₁||z₂|) = cos(arg z₂ − arg z₁) ≥ 0`, as `cos` is non-negative on `[−π/2,π/2]`
(the two arguments lie in an interval of length `2πθ ≤ π/2`).  This is one of the standing
hypotheses of (9.1) (`hγ0` of `Work.FIArea2.sec9_error_of_pair_H`), and it must be discharged for
*every* pair in the support of `β`; `Work.FITop3.InPolarBox` supplies exactly the two conditions
needed. -/
theorem gamOf_nonneg_of_polarBox (Pa : Work.FITop.Params) (φ : ℝ) (z1 z2 : GaussianInt)
    (h1 : Work.FITop3.InPolarBox Pa φ z1) (h2 : Work.FITop3.InPolarBox Pa φ z2)
    (hθ : 2 * Real.pi * Pa.θ ≤ Real.pi / 2) :
    0 ≤ Work.FIArea2.gamOf z1 z2 := by
  obtain ⟨-, hgn1lo, -, harg1lo, harg1hi⟩ := h1
  obtain ⟨-, hgn2lo, -, harg2lo, harg2hi⟩ := h2
  -- `1 ≤ Pa.N < |z_j|²`, so both `z_j` are nonzero
  have hgn1pos : (0 : ℝ) < ((Work.FIPlan.gnorm z1 : ℕ) : ℝ) := by
    linarith [Pa.hN1, hgn1lo]
  have hgn2pos : (0 : ℝ) < ((Work.FIPlan.gnorm z2 : ℕ) : ℝ) := by
    linarith [Pa.hN1, hgn2lo]
  have hz1 : z1 ≠ 0 := by
    intro hz
    have : Work.FIPlan.gnorm z1 = 0 := by simp [Work.FIPlan.gnorm, hz]
    rw [this] at hgn1pos
    simp at hgn1pos
  have hz2 : z2 ≠ 0 := by
    intro hz
    have : Work.FIPlan.gnorm z2 = 0 := by simp [Work.FIPlan.gnorm, hz]
    rw [this] at hgn2pos
    simp at hgn2pos
  rw [gamOf_eq_cos_arg z1 z2 hz1 hz2]
  -- the two arguments differ by less than `2πθ ≤ π/2` in absolute value
  apply Real.cos_nonneg_of_mem_Icc
  constructor <;> linarith

end Work.FIArea2
