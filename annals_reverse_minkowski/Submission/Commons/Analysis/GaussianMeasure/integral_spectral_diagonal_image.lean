import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Submission.Commons.Analysis.GaussianMeasure.norm_sq_eq_sum_diagonal_spectral

namespace Commons.Analysis.GaussianMeasure

open MeasureTheory Matrix
open scoped Real BigOperators

set_option linter.unusedVariables false

/-- Change of variables for a linear endomorphism `T` of a finite-dimensional real normed space
whose determinant has absolute value `1`: integrating over the image `T '' K` of a set `K` is the
same as integrating the composed function `g ∘ T` over `K`.

This is the "measure preserving" form of the linear change-of-variables formula; it does not
require `K` to be measurable. -/
theorem integral_image_linearMap_det_abs_one {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
    [FiniteDimensional ℝ E] [T2Space E]
    (μ : Measure E) [μ.IsAddHaarMeasure]
    (T : E →ₗ[ℝ] E) (hT : |LinearMap.det T| = 1) (K : Set E) (g : E → ℝ) :
    ∫ x in T '' K, g x ∂μ = ∫ x in K, g (T x) ∂μ := by
  have hne : LinearMap.det T ≠ 0 := by
    intro h; rw [h, abs_zero] at hT; exact one_ne_zero hT.symm
  have hmap : Measure.map (T : E → E) μ = μ := by
    rw [Measure.map_linearMap_addHaar_eq_smul_addHaar μ hne]
    have : |(LinearMap.det T)⁻¹| = 1 := by rw [abs_inv, hT, inv_one]
    rw [this, ENNReal.ofReal_one, one_smul]
  have hemb : MeasurableEmbedding (T : E → E) := by
    have he : (T.equivOfDetNeZero hne : E → E) = (T : E → E) := by
      ext x; simp only [LinearMap.equivOfDetNeZero]; rfl
    rw [← he]
    exact (T.equivOfDetNeZero hne).toContinuousLinearEquiv.toHomeomorph.measurableEmbedding
  have hpre : (T : E → E) ⁻¹' (T '' K) = K := by
    ext x; constructor
    · intro hx
      rcases hx with ⟨y, hy, hTy⟩
      rw [hemb.injective hTy] at hy; exact hy
    · intro hx; exact ⟨x, hx, rfl⟩
  have h1 : μ.restrict (T '' K) = Measure.map (T : E → E) (μ.restrict K) := by
    have h2 := hemb.restrict_map μ (T '' K)
    rw [hmap, hpre] at h2
    exact h2
  calc ∫ x in T '' K, g x ∂μ
      = ∫ x, g x ∂(μ.restrict (T '' K)) := rfl
    _ = ∫ x, g x ∂(Measure.map (T : E → E) (μ.restrict K)) := by rw [h1]
    _ = ∫ x, g (T x) ∂(μ.restrict K) := hemb.integral_map g
    _ = ∫ x in K, g (T x) ∂μ := rfl

/-- Determinant of the linear map attached to a matrix. -/
theorem abs_det_toLpLin_of_orthogonal {n : ℕ} (V : Matrix (Fin n) (Fin n) ℝ)
    (hV : V.transpose * V = 1) :
    |LinearMap.det (Matrix.toLpLin 2 2 V)| = 1 := by
  have h2 : V.det ^ 2 = 1 := by
    have h := congrArg Matrix.det hV
    rw [Matrix.det_mul, Matrix.det_transpose, Matrix.det_one] at h
    rw [sq]; exact h
  rw [LinearMap.det_toLpLin]
  have h3 : |V.det| ^ 2 = (1 : ℝ) := by rw [sq_abs, h2]
  rcases sq_eq_one_iff.mp h3 with h | h
  · exact h
  · exfalso
    have hnn : (0 : ℝ) ≤ |V.det| := abs_nonneg _
    rw [h] at hnn
    linarith

theorem integral_spectral_diagonal_image {n : ℕ} (A V : Matrix (Fin n) (Fin n) ℝ)
    (d : Fin n → ℝ) (hV : V.transpose * V = 1) (hdet : A.det = 1)
    (hM : A.transpose * A = V.transpose * Matrix.diagonal d * V)
    (s : ℝ) (hs : 0 < s) (K : Set (EuclideanSpace ℝ (Fin n))) :
    ∫ x in (Matrix.toLpLin 2 2 A) '' (Set.image (fun k => s⁻¹ • k) K),
        Real.exp (-Real.pi * ‖x‖ ^ 2)
      = ∫ y in (Matrix.toLpLin 2 2 V) '' (Set.image (fun k => s⁻¹ • k) K),
          Real.exp (-Real.pi * ∑ i, d i * (y i) ^ 2) := by
  have hAdet : |LinearMap.det (Matrix.toLpLin 2 2 A)| = 1 := by
    rw [LinearMap.det_toLpLin, hdet, abs_one]
  have hVdet : |LinearMap.det (Matrix.toLpLin 2 2 V)| = 1 :=
    abs_det_toLpLin_of_orthogonal V hV
  rw [integral_image_linearMap_det_abs_one volume (Matrix.toLpLin 2 2 A) hAdet
        (Set.image (fun k => s⁻¹ • k) K) (fun x => Real.exp (-Real.pi * ‖x‖ ^ 2)),
      integral_image_linearMap_det_abs_one volume (Matrix.toLpLin 2 2 V) hVdet
        (Set.image (fun k => s⁻¹ • k) K)
        (fun y => Real.exp (-Real.pi * ∑ i, d i * (y i) ^ 2))]
  apply integral_congr_ae
  filter_upwards with x
  have hsum : (∑ i, d i * (V.mulVec (WithLp.ofLp x)) i ^ 2)
      = ∑ i, d i * (((Matrix.toLpLin 2 2 V) x) i) ^ 2 := by
    apply Finset.sum_congr rfl
    intro i _
    congr 2
  rw [norm_sq_eq_sum_diagonal_spectral A V d hV hM x, hsum]

end Commons.Analysis.GaussianMeasure