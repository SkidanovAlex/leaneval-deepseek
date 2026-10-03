import Mathlib

namespace Work.Analysis.Fourier

open MeasureTheory

/-- If `f` has the pointwise Fourier series `∑_j a_j · fourier_j` (absolutely summable
coefficients `a`) and `G ∈ L²` on the circle of circumference `1`, then the Fourier
coefficients of the product `f · G` are given by the convolution of `a` with the
coefficients of `G`. -/
theorem fourierCoeff_mul_summable_series {a : ℤ → ℂ} (ha : Summable fun j => ‖a j‖)
    {f : AddCircle (1 : ℝ) → ℂ}
    (hf : ∀ ξ, HasSum (fun j => a j * fourier (T := 1) j ξ) (f ξ))
    {G : AddCircle (1 : ℝ) → ℂ} (hG : MeasureTheory.MemLp G 2 (AddCircle.haarAddCircle (T := 1)))
    (m : ℤ) :
    fourierCoeff (fun ξ => f ξ * G ξ) m
      = ∑' j : ℤ, a j * fourierCoeff G (m - j) := by
  have hGint : Integrable G (AddCircle.haarAddCircle (T := 1)) := hG.integrable (by norm_num)
  -- The integrands whose series we will integrate term by term.
  set F : ℤ → AddCircle (1 : ℝ) → ℂ :=
    fun j ξ => fourier (T := 1) (-m) ξ • (a j * fourier (T := 1) j ξ * G ξ) with hF
  -- Pointwise normal form of `F j`.
  have hFpt : ∀ j ξ, F j ξ = a j * (fourier (T := 1) (j - m) ξ * G ξ) := by
    intro j ξ
    have hfa : fourier (T := 1) (-m) ξ * fourier (T := 1) j ξ = fourier (T := 1) (j - m) ξ := by
      rw [sub_eq_add_neg, fourier_add]; ring
    simp only [hF, smul_eq_mul]
    rw [← hfa]; ring
  -- Norm of the Fourier monomials is `1`.
  have hfournorm : ∀ (k : ℤ) (ξ : AddCircle (1 : ℝ)), ‖fourier (T := 1) k ξ‖ = 1 := by
    intro k ξ
    rw [fourier_apply, Circle.norm_coe]
  -- Each `F j` is integrable.
  have hFint : ∀ j, Integrable (F j) (AddCircle.haarAddCircle (T := 1)) := by
    intro j
    rw [show F j = fun ξ : AddCircle (1 : ℝ) =>
      a j * (fourier (T := 1) (j - m) ξ * G ξ) from funext (hFpt j)]
    refine Integrable.const_mul ?_ (a j)
    refine hGint.bdd_mul (c := 1) (f := fun ξ => fourier (T := 1) (j - m) ξ) ?_ ?_
    · exact (fourier (T := 1) (j - m)).continuous.aestronglyMeasurable
    · filter_upwards with ξ
      rw [hfournorm (j - m) ξ]
  -- The integrals of the norms are summable.
  have hnormpt : ∀ j ξ, ‖F j ξ‖ = ‖a j‖ * ‖G ξ‖ := by
    intro j ξ
    rw [hFpt j ξ]
    simp only [norm_mul, hfournorm, one_mul]
  have hFsum : Summable (fun j => ∫ ξ, ‖F j ξ‖ ∂AddCircle.haarAddCircle (T := 1)) := by
    rw [show (fun j => ∫ ξ, ‖F j ξ‖ ∂AddCircle.haarAddCircle (T := 1))
        = fun j => ‖a j‖ * (∫ ξ, ‖G ξ‖ ∂AddCircle.haarAddCircle (T := 1)) from
      funext (fun j => by
        rw [show (fun ξ => ‖F j ξ‖) = fun ξ => ‖a j‖ * ‖G ξ‖ from funext (hnormpt j)]
        rw [integral_const_mul])]
    exact ha.mul_right _
  -- Integrate the series term by term.
  have hmain := hasSum_integral_of_summable_integral_norm hFint hFsum
  -- Rewrite the integral of the pointwise sum as the Fourier coefficient we want.
  have hkey : fourierCoeff (fun ξ => f ξ * G ξ) m
      = ∫ ξ, ∑' j : ℤ, F j ξ ∂AddCircle.haarAddCircle (T := 1) := by
    rw [fourierCoeff]
    apply integral_congr_ae
    filter_upwards with ξ
    exact (((hf ξ).mul_right (G ξ)).const_smul (fourier (T := 1) (-m) ξ)).tsum_eq.symm
  rw [hkey, ← hmain.tsum_eq]
  refine tsum_congr (fun j => ?_)
  have hcoeff : fourierCoeff G (m - j)
      = ∫ ξ, fourier (T := 1) (j - m) ξ * G ξ ∂AddCircle.haarAddCircle (T := 1) := by
    rw [fourierCoeff]
    apply integral_congr_ae
    filter_upwards with ξ
    rw [show -(m - j) = j - m from by ring, smul_eq_mul]
  rw [show (fun ξ : AddCircle (1 : ℝ) => F j ξ)
      = fun ξ => a j * (fourier (T := 1) (j - m) ξ * G ξ) from funext (hFpt j),
    integral_const_mul, ← hcoeff]

end Work.Analysis.Fourier
