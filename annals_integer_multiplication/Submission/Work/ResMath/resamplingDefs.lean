import Mathlib
import Submission.Work.ResMath.defs

/-!
# Shared definitions for the resampling identity (paper Thm 4.2)

`FsZ s u m` is the DFT `F_s u` extended from `Fin s` to an arbitrary integer index
`m ↦ s⁻¹ Σ_i u_i e^{-2πi m i/s}` (so it is `s`-periodic and agrees with `dftMat s` on `Fin s`);
`FtZ` is the same gadget for length `t`.
-/

namespace Work.ResMath

open HvdH

/-- `(F_s u)_m = s⁻¹ Σ_i u_i e^{-2πi m i/s}` for an arbitrary integer index `m`. -/
noncomputable def FsZ (s : ℕ) (u : Fin s → ℂ) (m : ℤ) : ℂ :=
  (1 / (s : ℂ)) * ∑ i : Fin s,
    u i * Complex.exp (-2 * (Real.pi : ℂ) * Complex.I * ((m : ℂ) * ((i : ℕ) : ℂ)) / (s : ℂ))

/-- `(F_t w)_m = t⁻¹ Σ_l w_l e^{-2πi m l/t}` for an arbitrary integer index `m`. -/
noncomputable def FtZ (t : ℕ) (w : Fin t → ℂ) (m : ℤ) : ℂ :=
  (1 / (t : ℂ)) * ∑ l : Fin t,
    w l * Complex.exp (-2 * (Real.pi : ℂ) * Complex.I * ((m : ℂ) * ((l : ℕ) : ℂ)) / (t : ℂ))

/-- `FsZ` agrees with the DFT matrix on `Fin s`. -/
lemma dftMat_mulVec_FsZ (s : ℕ) (u : Fin s → ℂ) (j : Fin s) :
    (dftMat s).mulVec u j = FsZ s u (j : ℤ) := by
  rw [FsZ]
  simp only [Matrix.mulVec, dotProduct]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [dftMat]
  have h : ((j * i : ℕ) : ℂ) = ((j : ℤ) : ℂ) * ((i : ℕ) : ℂ) := by push_cast; ring
  rw [h]; ring

/-- `FtZ` agrees with the DFT matrix on `Fin t`. -/
lemma dftMat_mulVec_FtZ (t : ℕ) (w : Fin t → ℂ) (l : Fin t) :
    (dftMat t).mulVec w l = FtZ t w (l : ℤ) := by
  rw [FtZ]
  simp only [Matrix.mulVec, dotProduct]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [dftMat]
  have h : ((l * i : ℕ) : ℂ) = ((l : ℤ) : ℂ) * ((i : ℕ) : ℂ) := by push_cast; ring
  rw [h]; ring

/-- The exponential of a DFT, shifted by a multiple of the period. -/
private lemma cexp_shift (n : ℕ) (hn : 0 < n) (i : ℕ) (m q : ℤ) :
    Complex.exp (-2 * (Real.pi : ℂ) * Complex.I * (((m + (n : ℤ) * q : ℤ) : ℂ) * ((i : ℕ) : ℂ)) / (n : ℂ))
      = Complex.exp (-2 * (Real.pi : ℂ) * Complex.I * ((m : ℂ) * ((i : ℕ) : ℂ)) / (n : ℂ)) := by
  have hnne : ((n : ℂ)) ≠ 0 := by
    simp only [ne_eq, Nat.cast_eq_zero]; omega
  have hsplit : -2 * (Real.pi : ℂ) * Complex.I * (((m + (n : ℤ) * q : ℤ) : ℂ) * ((i : ℕ) : ℂ)) / (n : ℂ)
      = -2 * (Real.pi : ℂ) * Complex.I * ((m : ℂ) * ((i : ℕ) : ℂ)) / (n : ℂ)
        + (((-(q * ((i : ℕ) : ℤ)) : ℤ)) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by
    push_cast
    field_simp
    ring
  rw [hsplit, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

/-- `FsZ` is periodic of period `s`. -/
lemma FsZ_period (s : ℕ) (hs : 0 < s) (u : Fin s → ℂ) (m : ℤ) (q : ℤ) :
    FsZ s u (m + (s : ℤ) * q) = FsZ s u m := by
  rw [FsZ, FsZ, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [cexp_shift s hs (i : ℕ) m q]

/-- `FtZ` is periodic of period `t`. -/
lemma FtZ_period (t : ℕ) (ht : 0 < t) (w : Fin t → ℂ) (m : ℤ) (q : ℤ) :
    FtZ t w (m + (t : ℤ) * q) = FtZ t w m := by
  rw [FtZ, FtZ, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [cexp_shift t ht (i : ℕ) m q]

/-- Norm bound for `FsZ`. -/
lemma FsZ_norm_le (s : ℕ) (hs : 0 < s) (u : Fin s → ℂ) (m : ℤ) :
    ‖FsZ s u m‖ ≤ (∑ i : Fin s, ‖u i‖) / s := by
  rw [FsZ, norm_mul]
  have hsC : ‖(1 / (s : ℂ))‖ = 1 / (s : ℝ) := by
    rw [norm_div, norm_one, Complex.norm_natCast]
  rw [hsC]
  calc (1 / (s : ℝ)) * ‖∑ i : Fin s, u i * Complex.exp (-2 * (Real.pi : ℂ) * Complex.I * ((m : ℂ) * ((i : ℕ) : ℂ)) / (s : ℂ))‖
      ≤ (1 / (s : ℝ)) * ∑ i : Fin s, ‖u i * Complex.exp (-2 * (Real.pi : ℂ) * Complex.I * ((m : ℂ) * ((i : ℕ) : ℂ)) / (s : ℂ))‖ := by
        gcongr
        exact norm_sum_le _ _
    _ = (1 / (s : ℝ)) * ∑ i : Fin s, ‖u i‖ := by
        congr 1
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [norm_mul, Complex.norm_exp]
        have hre : (-2 * (Real.pi : ℂ) * Complex.I * ((m : ℂ) * ((i : ℕ) : ℂ)) / (s : ℂ)).re = 0 := by
          have h1 : ((m : ℂ) * ((i : ℕ) : ℂ)) = (((m : ℝ) * (i : ℝ) : ℝ) : ℂ) := by push_cast; ring
          rw [h1]
          have h2 : -2 * (Real.pi : ℂ) * Complex.I * ((↑((m : ℝ) * (i : ℝ)) : ℂ)) / (s : ℂ)
              = (( -2 * Real.pi * ((m : ℝ) * (i : ℝ)) / (s : ℝ) : ℝ) : ℂ) * Complex.I := by
            push_cast; ring
          rw [h2, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re]
          ring
        rw [hre, Real.exp_zero, mul_one]
    _ = (∑ i : Fin s, ‖u i‖) / s := by ring


/-- The Gaussian factor `exp(-π α² m²/s²)` as a complex number. -/
noncomputable def Gz (s α : ℕ) (m : ℤ) : ℂ :=
  (Real.exp (-Real.pi * (α : ℝ) ^ 2 * (m : ℝ) ^ 2 / (s : ℝ) ^ 2) : ℂ)

/-- The Fourier phase `e^{2πi c l/t}`. -/
noncomputable def Phz (t : ℕ) (c : ℂ) (l : ℕ) : ℂ :=
  Complex.exp (2 * (Real.pi : ℂ) * Complex.I * c * ((l : ℂ) / (t : ℂ)))

/-- The Gaussian factor `exp(-π α² t² (k/t - j/s)²)`. -/
noncomputable def Gzk (s t α : ℕ) (k : ℕ) (j : ℤ) : ℂ :=
  (Real.exp (-Real.pi * (α : ℝ) ^ 2 * (t : ℝ) ^ 2 * ((k : ℝ) / (t : ℝ) - (j : ℝ) / (s : ℝ)) ^ 2) : ℂ)

end Work.ResMath
