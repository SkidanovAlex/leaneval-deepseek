import Mathlib
import Submission.Commons.GeometryOfNumbers.minkowski_polar_lower

namespace Commons.GeometryOfNumbers

/-- **The polar lower bound in an arbitrary determinant-one position** (the Lemma in
Regev–Stephens-Davidowitz, *A reverse Minkowski theorem*, Ann. of Math. 199 (2024), §4.3,
in the form `A ∈ SL_m`).

For a symmetric convex body `K` of volume one and any determinant-one matrix `A`, the Gaussian
second moment of the support function of `K` in the position `A` is bounded below by
`(vol B₂ᵐ)^{-2/m} · m/(2π)`.  Writing `ℓ_{K°}(B)² := ∫ (sup_{y∈K} ⟨y, B x⟩)² e^{-π‖x‖²} dx`,
this is `ℓ_{K°}((Aᵀ)^{-1})² ≥ (vol B₂ᵐ)^{-2/m} m/(2π)`.

Proof: pointwise, `sup_{y∈K}⟨y, (Aᵀ)^{-1}x⟩ = sup_{z ∈ A^{-1}K}⟨z,x⟩` (substitute `z = A^{-1}y`,
using `⟨A^{-1}y, x⟩ = ⟨y, (Aᵀ)^{-1}x⟩`), and `A^{-1} K` is again a symmetric convex body of
volume one (`|det A^{-1}| = 1`), so this is exactly
`Commons.GeometryOfNumbers.minkowski_polar_lower` applied to `A^{-1} K`. -/
theorem polar_lower_det_one {m : ℕ} (hm : 1 ≤ m) (K : Set (EuclideanSpace ℝ (Fin m)))
    (hKcvx : Convex ℝ K) (hKcpt : IsCompact K)
    (hKsymm : (-K : Set (EuclideanSpace ℝ (Fin m))) = K)
    (hKvol : MeasureTheory.volume.real K = 1)
    (A : Matrix (Fin m) (Fin m) ℝ) (hA : A.det = 1) :
    (MeasureTheory.volume.real (Metric.ball (0 : EuclideanSpace ℝ (Fin m)) 1)) ^
          (-(2 / (m : ℝ))) * (m : ℝ) / (2 * Real.pi) ≤
      ∫ x : EuclideanSpace ℝ (Fin m),
        (sSup ((fun z => inner ℝ z x) ''
            (Set.image (fun v => Matrix.toLpLin 2 2 A⁻¹ v) K))) ^ 2 *
        Real.exp (-Real.pi * ‖x‖ ^ 2) := by
  have hm0 : 0 < m := hm
  have hunit : IsUnit A.det := by rw [hA]; exact isUnit_one
  have hdetinv : (A⁻¹).det = 1 := by
    have h := congrArg Matrix.det (Matrix.mul_nonsing_inv A hunit)
    rw [Matrix.det_mul, hA, one_mul, Matrix.det_one] at h
    exact h
  have hφdet : LinearMap.det (Matrix.toLpLin 2 2 A⁻¹) = 1 := by
    rw [LinearMap.det_toLpLin, hdetinv]
  have hφcont : Continuous (fun v : EuclideanSpace ℝ (Fin m) => Matrix.toLpLin 2 2 A⁻¹ v) :=
    LinearMap.continuous_of_finiteDimensional _
  have hcvx : Convex ℝ ((fun v : EuclideanSpace ℝ (Fin m) => Matrix.toLpLin 2 2 A⁻¹ v) '' K) :=
    hKcvx.linear_image _
  have hcpt : IsCompact ((fun v : EuclideanSpace ℝ (Fin m) => Matrix.toLpLin 2 2 A⁻¹ v) '' K) :=
    hKcpt.image hφcont
  have hsymm : -((fun v : EuclideanSpace ℝ (Fin m) => Matrix.toLpLin 2 2 A⁻¹ v) '' K)
      = (fun v : EuclideanSpace ℝ (Fin m) => Matrix.toLpLin 2 2 A⁻¹ v) '' K := by
    have h1 := Set.image_neg (Matrix.toLpLin 2 2 A⁻¹) K
    rw [hKsymm] at h1
    exact h1.symm
  have hvol : MeasureTheory.volume.real
      ((fun v : EuclideanSpace ℝ (Fin m) => Matrix.toLpLin 2 2 A⁻¹ v) '' K) = 1 := by
    have h1 := MeasureTheory.Measure.addHaar_image_linearMap (μ := MeasureTheory.volume)
      (Matrix.toLpLin 2 2 A⁻¹) K
    rw [hφdet, abs_one, ENNReal.ofReal_one, one_mul] at h1
    rw [MeasureTheory.Measure.real_def, h1]
    simpa [MeasureTheory.Measure.real_def] using hKvol
  exact minkowski_polar_lower hm0 _ hcvx hcpt hsymm hvol

end Commons.GeometryOfNumbers
