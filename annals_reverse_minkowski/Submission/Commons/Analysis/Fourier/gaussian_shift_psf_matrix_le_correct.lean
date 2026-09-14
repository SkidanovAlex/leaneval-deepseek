import Mathlib
import Submission.Commons.Analysis.Fourier.gaussian_psf_matrix
import Submission.Commons.Analysis.Fourier.gaussian_psf_core

noncomputable section
open scoped BigOperators Topology ENNReal
open MeasureTheory Filter Complex
open Matrix

set_option autoImplicit false

namespace Commons.Analysis.Fourier

/-! ## The shifted Gaussian lattice sum is maximised at the lattice point

We prove that, for an invertible real matrix `C` and every shift `z`,
`Σ'_k exp (-π · ‖C · (k - z)‖²) ≤ Σ'_k exp (-π · ‖C · k‖²)`.

The argument is Fourier analytic: the periodicised Gaussian `pgauss C x` is
expanded in its Fourier series on the torus `UnitAddTorus (Fin n)`, whose
coefficients are all nonnegative real numbers times monomials of modulus ≤ 1.
-/

/-- The norm of the `m`-th Fourier coefficient of the periodicised Gaussian. -/
lemma norm_coeff_pgaussTorus (n : ℕ) (C : Matrix (Fin n) (Fin n) ℝ) (hC : C.det ≠ 0)
    (m : Fin n → ℤ) :
    ‖UnitAddTorus.mFourierCoeff (⇑(pgaussTorus n C hC)) m‖ =
      (|C.det| : ℝ)⁻¹ * Real.exp (-Real.pi * sqNormMat (C⁻¹)ᵀ (intToReal m)) := by
  have hcoef : UnitAddTorus.mFourierCoeff (⇑(pgaussTorus n C hC)) m =
      ((|C.det| : ℝ)⁻¹ : ℂ) * cexp (-(Real.pi : ℂ) * ↑(sqNormMat (C⁻¹)ᵀ (intToReal m))) := by
    rw [mFourierCoeff_pgaussTorus n C hC m]
    exact coeffIntegral_eq n C hC m
  rw [hcoef]
  rw [norm_mul]
  rw [Complex.norm_exp]
  have hnn : 0 ≤ (|C.det| : ℝ)⁻¹ := inv_nonneg.mpr (abs_nonneg _)
  have h1 : ‖((|C.det| : ℝ)⁻¹ : ℂ)‖ = (|C.det| : ℝ)⁻¹ := by
    simp
  have h2 : ((-(Real.pi : ℂ) * ↑(sqNormMat (C⁻¹)ᵀ (intToReal m))).re)
      = -Real.pi * sqNormMat (C⁻¹)ᵀ (intToReal m) := by
    simp
  rw [h1, h2]

/-- Fourier coefficient decay for the periodicised Gaussian. -/
lemma summable_coeff_norm_pgaussTorus (n : ℕ) (C : Matrix (Fin n) (Fin n) ℝ) (hC : C.det ≠ 0) :
    Summable (fun m : Fin n → ℤ =>
      ‖UnitAddTorus.mFourierCoeff (⇑(pgaussTorus n C hC)) m‖) := by
  have hMnz : ((C⁻¹).transpose).det ≠ 0 := by
    rw [Matrix.det_transpose]
    intro hz
    have hd : (C⁻¹).det * C.det = 1 := by
      rw [← Matrix.det_mul]
      rw [Matrix.nonsing_inv_mul C (isUnit_iff_ne_zero.mpr hC)]
      simp
    rw [hz, zero_mul] at hd
    norm_num at hd
  have hz := Commons.Analysis.Fourier.zpow_summable_gauss_matrix n ((C⁻¹).transpose) hMnz
    Real.pi Real.pi_pos
  let decayReal : (Fin n → ℤ) → ℝ := fun m =>
    Real.exp (-Real.pi * (∑ i : Fin n, ((((C⁻¹).transpose) *ᵥ fun j : Fin n => (m j : ℝ)) i) ^ 2))
  have hg : Summable decayReal := by
    simpa [decayReal] using hz
  refine Summable.of_norm_bounded (g := fun m : Fin n → ℤ => ((|C.det| : ℝ)⁻¹) * decayReal m) ?_ ?_
  · exact hg.mul_left ((|C.det| : ℝ)⁻¹)
  · intro m
    rw [Real.norm_of_nonneg (norm_nonneg _)]
    rw [norm_coeff_pgaussTorus n C hC m]
    rw [show sqNormMat (C⁻¹).transpose (intToReal m) =
        (∑ i : Fin n, ((((C⁻¹).transpose) *ᵥ fun j : Fin n => (m j : ℝ)) i) ^ 2) by rfl]

/-- The Fourier series of the periodicised Gaussian converges to it at every point. -/
lemma fourier_series_pgaussTorus (n : ℕ) (C : Matrix (Fin n) (Fin n) ℝ) (hC : C.det ≠ 0)
    (x : Fin n → ℝ) :
    (∑' m : Fin n → ℤ, UnitAddTorus.mFourierCoeff (⇑(pgaussTorus n C hC)) m •
      (UnitAddTorus.mFourier m) (torusMk (Fin n) x)) = pgauss C x := by
  have hsm : Summable (fun m : Fin n → ℤ =>
      UnitAddTorus.mFourierCoeff (⇑(pgaussTorus n C hC)) m) := by
    exact Summable.of_norm (summable_coeff_norm_pgaussTorus n C hC)
  have hfs := UnitAddTorus.hasSum_mFourier_series_apply_of_summable (f := pgaussTorus n C hC) hsm
    (torusMk (Fin n) x)
  rw [← pgaussTorus_descent n C hC x]
  exact hfs.tsum_eq

/-- Each smul term in the Fourier series has norm bounded by the coefficient norm. -/
lemma smul_mFourier_norm_le (n : ℕ) (C : Matrix (Fin n) (Fin n) ℝ) (hC : C.det ≠ 0)
    (x : Fin n → ℝ) (m : Fin n → ℤ) :
    ‖(UnitAddTorus.mFourierCoeff (⇑(pgaussTorus n C hC)) m) •
        (UnitAddTorus.mFourier m) (torusMk (Fin n) x)‖ ≤
      ‖UnitAddTorus.mFourierCoeff (⇑(pgaussTorus n C hC)) m‖ := by
  calc
    ‖(UnitAddTorus.mFourierCoeff (⇑(pgaussTorus n C hC)) m) •
        (UnitAddTorus.mFourier m) (torusMk (Fin n) x)‖ ≤
        ‖UnitAddTorus.mFourierCoeff (⇑(pgaussTorus n C hC)) m‖ *
          ‖(UnitAddTorus.mFourier m) (torusMk (Fin n) x)‖ := norm_smul_le _ _
    _ ≤ ‖UnitAddTorus.mFourierCoeff (⇑(pgaussTorus n C hC)) m‖ * 1 := by
          exact mul_le_mul_of_nonneg_left (by
            calc
              ‖(UnitAddTorus.mFourier m) (torusMk (Fin n) x)‖ ≤ ‖UnitAddTorus.mFourier m‖ :=
                ContinuousMap.norm_coe_le_norm _ _
              _ = 1 := UnitAddTorus.mFourier_norm) (norm_nonneg _)
    _ = ‖UnitAddTorus.mFourierCoeff (⇑(pgaussTorus n C hC)) m‖ := by rw [mul_one]

/-- For every point `x`, the modulus of the periodicised Gaussian is at most its value
at the origin (expressed by the Poisson-summation formula on the right). -/
lemma pgauss_norm_le_origin_value (n : ℕ) (C : Matrix (Fin n) (Fin n) ℝ) (hC : C.det ≠ 0)
    (x : Fin n → ℝ) :
    ‖pgauss C x‖ ≤ (|C.det| : ℝ)⁻¹ *
      (∑' m : Fin n → ℤ,
        Real.exp (-Real.pi * sqNormMat (C⁻¹)ᵀ (intToReal m))) := by
  let F : C(UnitAddTorus (Fin n), ℂ) := pgaussTorus n C hC
  have hcoefsm : Summable (fun m : Fin n → ℤ => ‖UnitAddTorus.mFourierCoeff (⇑F) m‖) := by
    simpa [F] using summable_coeff_norm_pgaussTorus n C hC
  let z : (Fin n → ℤ) → ℂ := fun m =>
    UnitAddTorus.mFourierCoeff (⇑F) m •
      (UnitAddTorus.mFourier m) (torusMk (Fin n) x)
  have hzsm1 : Summable (fun m : Fin n → ℤ => ‖z m‖) := by
    refine Summable.of_norm_bounded (g := fun m : Fin n → ℤ =>
      ‖UnitAddTorus.mFourierCoeff (⇑F) m‖) hcoefsm ?_
    intro m
    rw [Real.norm_of_nonneg (norm_nonneg _)]
    dsimp [z]
    exact smul_mFourier_norm_le n C hC x m
  calc
    ‖pgauss C x‖ = ‖∑' m : Fin n → ℤ, z m‖ := by
          rw [← fourier_series_pgaussTorus n C hC x]
    _ ≤ ∑' m : Fin n → ℤ, ‖z m‖ := norm_tsum_le_tsum_norm hzsm1
    _ ≤ ∑' m : Fin n → ℤ, ‖UnitAddTorus.mFourierCoeff (⇑F) m‖ := by
          exact hzsm1.tsum_le_tsum (fun m => by
            dsimp [z]
            exact smul_mFourier_norm_le n C hC x m) hcoefsm
    _ = ∑' m : Fin n → ℤ, ((|C.det| : ℝ)⁻¹) *
        Real.exp (-Real.pi * sqNormMat (C⁻¹)ᵀ (intToReal m)) := by
          apply tsum_congr
          intro m
          rw [norm_coeff_pgaussTorus n C hC m]
    _ = ((|C.det| : ℝ)⁻¹) *
        (∑' m : Fin n → ℤ, Real.exp (-Real.pi * sqNormMat (C⁻¹)ᵀ (intToReal m))) := by
          rw [tsum_mul_left]

/-- The real `ℤⁿ`-shifted Gaussian sum is at most its value at the unshifted lattice point. -/
lemma gaussian_shift_psf_bound (n : ℕ) (C : Matrix (Fin n) (Fin n) ℝ) (hC : C.det ≠ 0)
    (x : Fin n → ℝ) :
    (∑' k : Fin n → ℤ, rgauss C (x + intToReal k)) ≤
      (∑' k : Fin n → ℤ, rgauss C (intToReal k)) := by
  have hpg : pgauss C x =
      (((∑' k : Fin n → ℤ, rgauss C (x + intToReal k)) : ℝ) : ℂ) := by
    calc
      pgauss C x = ∑' k : Fin n → ℤ, cgauss C (x + intToReal k) := rfl
      _ = ∑' k : Fin n → ℤ, (rgauss C (x + intToReal k) : ℂ) := by
            apply tsum_congr
            intro k
            exact cgauss_eq_ofReal_rgauss C (x + intToReal k)
      _ = (((∑' k : Fin n → ℤ, rgauss C (x + intToReal k)) : ℝ) : ℂ) := by
            exact (Complex.ofReal_tsum (f := fun k : Fin n → ℤ => rgauss C (x + intToReal k))).symm
  have hcoreReal : (∑' k : Fin n → ℤ, rgauss C (intToReal k)) =
      (|C.det| : ℝ)⁻¹ *
        (∑' m : Fin n → ℤ,
          Real.exp (-Real.pi * sqNormMat (C⁻¹)ᵀ (intToReal m))) := by
    calc
      (∑' k : Fin n → ℤ, rgauss C (intToReal k))
          = ∑' k : Fin n → ℤ,
              Real.exp (-Real.pi * (∑ i : Fin n, (((C.mulVec fun j : Fin n => (k j : ℝ))) i) ^ 2)) := by
            apply tsum_congr
            intro k
            rfl
      _ = (|C.det| : ℝ)⁻¹ *
            (∑' m : Fin n → ℤ,
              Real.exp (-Real.pi * sqNormMat (C⁻¹)ᵀ (intToReal m))) := by
            rw [gaussian_psf_core n C hC]
            rfl
  calc
    (∑' k : Fin n → ℤ, rgauss C (x + intToReal k))
        ≤ |(∑' k : Fin n → ℤ, rgauss C (x + intToReal k) : ℝ)| := le_abs_self _
    _ = ‖pgauss C x‖ := by
          rw [hpg]
          simp
    _ ≤ (|C.det| : ℝ)⁻¹ *
          (∑' m : Fin n → ℤ, Real.exp (-Real.pi * sqNormMat (C⁻¹)ᵀ (intToReal m))) :=
          pgauss_norm_le_origin_value n C hC x
    _ = ∑' k : Fin n → ℤ, rgauss C (intToReal k) := by
          exact hcoreReal.symm


/-- The (real-valued) shifted Gaussian sum in coordinate form, written with `rgauss`. -/
lemma rgauss_sub_eq_sqsum (n : ℕ) (C : Matrix (Fin n) (Fin n) ℝ)
    (z : Fin n → ℝ) (v : Fin n → ℝ) (hCz : C.mulVec z = v) (k : Fin n → ℤ) :
    rgauss C (intToReal k - z) =
      Real.exp (-Real.pi *
        (∑ i : Fin n, (((C.mulVec (fun j : Fin n => (k j : ℝ))) i) - v i) ^ 2)) := by
  unfold rgauss
  congr 1
  congr 1
  have hvec : C *ᵥ (intToReal k - z) = C *ᵥ (fun j : Fin n => (k j : ℝ)) - v := by
    rw [Matrix.mulVec_sub]
    rw [show C *ᵥ intToReal k = C *ᵥ (fun j : Fin n => (k j : ℝ)) by rfl]
    rw [hCz]
  calc
    sqNormMat C (intToReal k - z)
        = ∑ i : Fin n, ((C *ᵥ (intToReal k - z)) i) ^ 2 := rfl
    _ = ∑ i : Fin n, (((C *ᵥ (fun j : Fin n => (k j : ℝ))) i) - v i) ^ 2 := by
          rw [hvec]
          rfl

/-- Rescaling the shift by `s` turns the plain Gaussian lattice sums into the `s = 1` ones. -/
theorem gaussian_shift_psf_matrix_le_correct {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.det ≠ 0)
    (s : ℝ) (hs : 0 < s) (u : Fin n → ℝ) :
    (∑' k : Fin n → ℤ,
        Real.exp (-Real.pi * (∑ i : Fin n, (((A.mulVec (fun j : Fin n => (k j : ℝ))) i) - u i) ^ 2) / s ^ 2)) ≤
      (∑' k : Fin n → ℤ,
        Real.exp (-Real.pi * (∑ i : Fin n, ((A.mulVec (fun j : Fin n => (k j : ℝ))) i) ^ 2) / s ^ 2)) := by
  classical
  let C : Matrix (Fin n) (Fin n) ℝ := (s⁻¹) • A
  have hs' : s ≠ 0 := ne_of_gt hs
  have hC : C.det ≠ 0 := by
    dsimp [C]
    rw [Matrix.det_smul]
    rw [show Fintype.card (Fin n) = n by simp]
    exact mul_ne_zero (pow_ne_zero n (inv_ne_zero hs')) hA
  let v : Fin n → ℝ := fun i => u i / s
  let z : Fin n → ℝ := C⁻¹.mulVec v
  have hCz : C.mulVec z = v := by
    dsimp [z]
    exact mulVec_inv_mulVec C hC v
  -- rewrite the left-hand side into the `rgauss` form
  have hL : (∑' k : Fin n → ℤ,
        Real.exp (-Real.pi * (∑ i : Fin n, (((A.mulVec (fun j : Fin n => (k j : ℝ))) i) - u i) ^ 2) / s ^ 2)) =
      (∑' k : Fin n → ℤ, rgauss C (intToReal k - z)) := by
    apply tsum_congr
    intro k
    rw [rgauss_sub_eq_sqsum n C z v hCz k]
    -- now: exp(-π * (∑((Ak)-u)^2) / s^2) = exp(-π * (∑((Ck)-v)^2))
    congr 1
    have hXY : (∑ i : Fin n, (((A.mulVec (fun j : Fin n => (k j : ℝ))) i) - u i) ^ 2) / s ^ 2 =
        (∑ i : Fin n, (((C.mulVec (fun j : Fin n => (k j : ℝ))) i) - v i) ^ 2) := by
      calc
        (∑ i : Fin n, (((A.mulVec (fun j : Fin n => (k j : ℝ))) i) - u i) ^ 2) / s ^ 2
            = ∑ i : Fin n, ((((A.mulVec (fun j : Fin n => (k j : ℝ))) i) - u i) ^ 2 / s ^ 2) := by
              rw [Finset.sum_div]
        _ = ∑ i : Fin n, (((((A.mulVec (fun j : Fin n => (k j : ℝ))) i) - u i) / s) ^ 2) := by
              apply Finset.sum_congr rfl
              intro i hi
              field_simp
        _ = ∑ i : Fin n, ((((C.mulVec (fun j : Fin n => (k j : ℝ))) i) - v i) ^ 2) := by
              apply Finset.sum_congr rfl
              intro i hi
              congr 1
              -- ((Ak)_i - u_i) / s = (Ck)_i - v_i
              have hci : ((C.mulVec (fun j : Fin n => (k j : ℝ))) i) = (s⁻¹) * ((A.mulVec (fun j : Fin n => (k j : ℝ))) i) := by
                dsimp [C]
                rw [GaussianPsfAssembly.smul_mulVec_apply A (s⁻¹) (fun j : Fin n => (k j : ℝ)) i, smul_eq_mul]
              dsimp [v]
              rw [hci]
              field_simp
    calc
      -Real.pi * (∑ i : Fin n, (((A.mulVec (fun j : Fin n => (k j : ℝ))) i) - u i) ^ 2) / s ^ 2
          = -Real.pi * ((∑ i : Fin n, (((A.mulVec (fun j : Fin n => (k j : ℝ))) i) - u i) ^ 2) / s ^ 2) := by ring
      _ = -Real.pi * (∑ i : Fin n, (((C.mulVec (fun j : Fin n => (k j : ℝ))) i) - v i) ^ 2) := by rw [hXY]
  -- rewrite the right-hand side into the `rgauss` form
  have hR : (∑' k : Fin n → ℤ,
        Real.exp (-Real.pi * (∑ i : Fin n, ((A.mulVec (fun j : Fin n => (k j : ℝ))) i) ^ 2) / s ^ 2)) =
      (∑' k : Fin n → ℤ, rgauss C (intToReal k)) := by
    apply tsum_congr
    intro k
    unfold rgauss
    congr 1
    have hXY : (∑ i : Fin n, ((A.mulVec (fun j : Fin n => (k j : ℝ))) i) ^ 2) / s ^ 2 =
        (∑ i : Fin n, ((C.mulVec (fun j : Fin n => (k j : ℝ))) i) ^ 2) := by
      calc
        (∑ i : Fin n, ((A.mulVec (fun j : Fin n => (k j : ℝ))) i) ^ 2) / s ^ 2
            = ∑ i : Fin n, (((A.mulVec (fun j : Fin n => (k j : ℝ))) i) ^ 2 / s ^ 2) := by
              rw [Finset.sum_div]
        _ = ∑ i : Fin n, ((((A.mulVec (fun j : Fin n => (k j : ℝ))) i) / s) ^ 2) := by
              apply Finset.sum_congr rfl
              intro i hi
              field_simp
        _ = ∑ i : Fin n, (((C.mulVec (fun j : Fin n => (k j : ℝ))) i) ^ 2) := by
              apply Finset.sum_congr rfl
              intro i hi
              congr 1
              have hci : ((C.mulVec (fun j : Fin n => (k j : ℝ))) i) = (s⁻¹) * ((A.mulVec (fun j : Fin n => (k j : ℝ))) i) := by
                dsimp [C]
                rw [GaussianPsfAssembly.smul_mulVec_apply A (s⁻¹) (fun j : Fin n => (k j : ℝ)) i, smul_eq_mul]
              rw [hci]
              field_simp
    calc
      -Real.pi * (∑ i : Fin n, ((A.mulVec (fun j : Fin n => (k j : ℝ))) i) ^ 2) / s ^ 2
          = -Real.pi * ((∑ i : Fin n, ((A.mulVec (fun j : Fin n => (k j : ℝ))) i) ^ 2) / s ^ 2) := by ring
      _ = -Real.pi * (∑ i : Fin n, ((C.mulVec (fun j : Fin n => (k j : ℝ))) i) ^ 2) := by rw [hXY]
  -- the shifted sum is at most the unshifted one
  have hshift : (∑' k : Fin n → ℤ, rgauss C (intToReal k - z)) ≤
      (∑' k : Fin n → ℤ, rgauss C (intToReal k)) := by
    have hbound := gaussian_shift_psf_bound n C hC (-z)
    -- ∑ rgauss C ((-z) + k) ≤ ∑ rgauss C (k); rewrite -z + k = k - z
    simpa [add_comm, add_left_comm, add_assoc, sub_eq_add_neg] using hbound
  calc
    (∑' k : Fin n → ℤ,
        Real.exp (-Real.pi * (∑ i : Fin n, (((A.mulVec (fun j : Fin n => (k j : ℝ))) i) - u i) ^ 2) / s ^ 2))
        = ∑' k : Fin n → ℤ, rgauss C (intToReal k - z) := hL
    _ ≤ ∑' k : Fin n → ℤ, rgauss C (intToReal k) := hshift
    _ = (∑' k : Fin n → ℤ,
        Real.exp (-Real.pi * (∑ i : Fin n, ((A.mulVec (fun j : Fin n => (k j : ℝ))) i) ^ 2) / s ^ 2)) := hR.symm

end Commons.Analysis.Fourier
