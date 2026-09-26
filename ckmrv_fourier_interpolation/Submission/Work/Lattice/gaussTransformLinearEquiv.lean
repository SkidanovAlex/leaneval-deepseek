import Mathlib

namespace Work.Lattice

open scoped FourierTransform RealInnerProductSpace
open MeasureTheory

/-- **The Fourier transform of a Gaussian under a linear change of variables**, in a general
finite-dimensional real inner product space `V`.  For an invertible linear map `T` of `V`, the
Fourier integral of `v ↦ exp (-π t ‖T v‖²)` at `w` is
`|det T|⁻¹ · t^{-dim V/2} · exp (-π ‖T⁻ᵀ w‖² / t)`, where `T⁻ᵀ` is `LinearMap.adjoint T.symm`.

The proof substitutes `y = T v` (`MeasureTheory.integral_map` together with
`MeasureTheory.Measure.map_linearMap_addHaar_eq_smul_addHaar`, which gives
`Measure.map T volume = ofReal |det T|⁻¹ • volume`) and then evaluates the resulting Gaussian
Fourier integral with `fourier_gaussian_innerProductSpace`. -/
theorem gaussTransformLinearEquiv_general {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
    (T : V ≃ₗ[ℝ] V) {t : ℝ} (ht : 0 < t) (w : V) :
    (∫ v : V, Complex.exp (-(↑(Real.pi * t) : ℂ) * (↑(‖T v‖ ^ 2) : ℂ)) *
        Complex.exp (-(↑(2 * Real.pi) : ℂ) * Complex.I * (↑(inner ℝ w v) : ℂ)))
      = (((|((LinearEquiv.det T : ℝˣ) : ℝ)| : ℝ)⁻¹ : ℝ) : ℂ) *
          ((t ^ (-(Module.finrank ℝ V : ℝ) / 2) : ℝ) : ℂ) *
          Complex.exp (-(↑(Real.pi / t) : ℂ) *
            (↑(‖(LinearMap.adjoint (T.symm : V →ₗ[ℝ] V)) w‖ ^ 2) : ℂ)) := by
  have hsymm : Continuous (fun y : V => T.symm y) :=
    LinearMap.continuous_of_finiteDimensional (T.symm : V →ₗ[ℝ] V)
  have hdet : LinearMap.det (T : V →ₗ[ℝ] V) ≠ 0 := by
    rw [← LinearEquiv.coe_det]; exact Units.ne_zero _
  set g : V → ℂ := fun y => Complex.exp (-(↑(Real.pi * t) : ℂ) * (↑(‖y‖ ^ 2) : ℂ)) with hg
  set A : V →ₗ[ℝ] V := LinearMap.adjoint (T.symm : V →ₗ[ℝ] V) with hA
  set F : V → ℂ := fun y =>
    Complex.exp (-(↑(2 * Real.pi) : ℂ) * Complex.I * (↑(inner ℝ w (T.symm y)) : ℂ)) * g y with hF
  have hFcont : Continuous F := by rw [hF]; fun_prop
  have hinner : ∀ y, inner ℝ w (T.symm y) = inner ℝ y (A w) := by
    intro y
    rw [hA]
    conv_rhs => rw [← real_inner_comm]
    exact (LinearMap.adjoint_inner_left (T.symm : V →ₗ[ℝ] V) y w).symm
  -- Step 1: rewrite the integrand in terms of `F ∘ T`.
  have stepA : (∫ v : V, Complex.exp (-(↑(Real.pi * t) : ℂ) * (↑(‖T v‖ ^ 2) : ℂ)) *
        Complex.exp (-(↑(2 * Real.pi) : ℂ) * Complex.I * (↑(inner ℝ w v) : ℂ))) =
      ∫ v, F (T v) := by
    apply integral_congr_ae
    filter_upwards with v
    simp only [hF, hg]
    rw [T.symm_apply_apply]; ring
  -- Step 2: substitute `y = T v`.
  have stepB : ∫ v, F (T v) = ((|(LinearMap.det (T : V →ₗ[ℝ] V))⁻¹| : ℝ) : ℂ) * ∫ y, F y := by
    have hvol := MeasureTheory.Measure.map_linearMap_addHaar_eq_smul_addHaar
      (volume : Measure V) (f := (T : V →ₗ[ℝ] V)) hdet
    have h1 : ∫ v, F (T v) = ∫ y, F y ∂(volume.map (⇑(T : V →ₗ[ℝ] V))) :=
      (MeasureTheory.integral_map (φ := ⇑(T : V →ₗ[ℝ] V))
        ((LinearMap.continuous_of_finiteDimensional (T : V →ₗ[ℝ] V)).measurable.aemeasurable)
        hFcont.measurable.aestronglyMeasurable).symm
    rw [h1, hvol, MeasureTheory.integral_smul_measure]
    rw [ENNReal.toReal_ofReal (abs_nonneg _)]
    rw [Complex.real_smul]
  -- Step 3: identify the remaining integral with a Fourier transform.
  have stepC : ∫ y, F y = 𝓕 g (A w) := by
    rw [Real.fourier_eq']
    apply integral_congr_ae
    filter_upwards with y
    simp only [hF, hg, smul_eq_mul]
    congr 1
    congr 1
    rw [hinner]; push_cast; ring
  -- Step 4: evaluate the Gaussian Fourier transform.
  have stepD : 𝓕 g (A w) = (↑Real.pi / ↑(Real.pi * t)) ^ ((↑(Module.finrank ℝ V) : ℂ)/2) *
      Complex.exp (-(↑Real.pi)^2 * (↑‖A w‖^2 : ℂ) / ↑(Real.pi * t)) := by
    have hfun : g = fun y => Complex.exp (-(↑(Real.pi*t):ℂ) * (↑‖y‖)^2) := by
      funext y; simp only [hg, Complex.ofReal_pow]
    rw [hfun]
    exact fourier_gaussian_innerProductSpace (b := (↑(Real.pi*t):ℂ))
      (by simpa using mul_pos Real.pi_pos ht) (A w)
  rw [stepA, stepB, stepC, stepD]
  -- Final algebra on the constants.
  have hc1 : (|(LinearMap.det (T : V →ₗ[ℝ] V))⁻¹| : ℝ) =
      |((LinearEquiv.det T : ℝˣ) : ℝ)|⁻¹ := by
    rw [← LinearEquiv.coe_det, abs_inv]
  have hc2 : (↑Real.pi / (↑(Real.pi * t) : ℂ)) ^ ((↑(Module.finrank ℝ V) : ℂ)/2)
      = ((t ^ (-(Module.finrank ℝ V : ℝ)/2) : ℝ) : ℂ) := by
    have hbase : (↑Real.pi : ℂ) / (↑(Real.pi * t) : ℂ) = (↑(t⁻¹) : ℂ) := by
      rw [← Complex.ofReal_div]; congr 1; field_simp
    rw [hbase, show ((↑(Module.finrank ℝ V) : ℂ)/2) = (↑((Module.finrank ℝ V : ℝ)/2) : ℂ)
      by push_cast; ring]
    rw [← Complex.ofReal_cpow (_root_.inv_nonneg.mpr ht.le) ((Module.finrank ℝ V : ℝ)/2)]
    congr 1
    rw [Real.inv_rpow ht.le, ← Real.rpow_neg ht.le]
    ring_nf
  have hc3 : Complex.exp (-(↑Real.pi)^2 * (↑‖A w‖^2 : ℂ) / ↑(Real.pi * t))
      = Complex.exp (-(↑(Real.pi/t) : ℂ) * (↑‖A w‖^2 : ℂ)) := by
    congr 1
    rw [Complex.ofReal_div]
    push_cast
    field_simp
  rw [hc1, hc2, hc3]
  simp only [Complex.ofReal_pow]
  ring

/-- **The Fourier transform of a Gaussian under a linear change of variables.**  For an invertible
linear map `T` of `E = ℝⁿ`, the Fourier transform of `v ↦ exp (-π t ‖T v‖²)` at `w` is
`|det T|⁻¹ · t^{-n/2} · exp (-π ‖T⁻ᵀ w‖² / t)`.

Proof route: `MeasureTheory.integral_map` with Mathlib's
`MeasureTheory.map_linearMap_addHaar_eq_smul_addHaar` (which computes
`Measure.map f volume = ofReal |det f|⁻¹ • volume` for `f : E →ₗ[ℝ] E` with `LinearMap.det f ≠ 0`)
substitutes `y = T v`, giving `|det T|⁻¹ ∫ y, exp (-π t ‖y‖²) exp (-2 π i ⟪T⁻ᵀw, y⟫) dy`, and
Mathlib's `fourier_gaussian_innerProductSpace` with `b = π t` evaluates the resulting Gaussian
integral as `(π / (π t))^{n/2} exp (-π² ‖T⁻ᵀw‖² / (π t)) = t^{-n/2} exp (-π ‖T⁻ᵀw‖² / t)`.
(The adjoint `T⁻ᵀ` is `LinearMap.adjoint (T.symm : E →ₗ[ℝ] E)`.) -/
theorem gaussTransformLinearEquiv {n : ℕ}
    (T : EuclideanSpace ℝ (Fin n) ≃ₗ[ℝ] EuclideanSpace ℝ (Fin n)) {t : ℝ} (ht : 0 < t)
    (w : EuclideanSpace ℝ (Fin n)) :
    (∫ v : EuclideanSpace ℝ (Fin n),
        Complex.exp (-(↑(Real.pi * t) : ℂ) * (↑(‖T v‖ ^ 2) : ℂ)) *
          Complex.exp (-(↑(2 * Real.pi) : ℂ) * Complex.I * (↑(inner ℝ w v) : ℂ)))
      = ((((|((LinearEquiv.det T : ℝˣ) : ℝ)| : ℝ))⁻¹ : ℝ) : ℂ) *
          ((t ^ (-(n : ℝ) / 2) : ℝ) : ℂ) *
          Complex.exp (-(↑(Real.pi / t) : ℂ) *
            (↑(‖(LinearMap.adjoint
              (T.symm : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n))) w‖ ^ 2) : ℂ)) := by
  simpa [finrank_euclideanSpace, Fintype.card_fin] using gaussTransformLinearEquiv_general T ht w

end Work.Lattice
