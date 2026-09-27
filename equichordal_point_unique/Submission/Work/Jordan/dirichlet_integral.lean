import Mathlib

/-!
# The Dirichlet integral of a bounded injective holomorphic function is finite

`Work.Jordan.lintegral_ofReal_sq_norm_deriv_lt_top` is the first of the three remaining ingredients of
the length–area estimate `Work.Jordan.length_area_estimate`
(see `Submission/Work/Jordan/NOTES_caratheodory_route.md`): for `f` holomorphic and injective on the
unit disc with `‖f‖ ≤ R`,

`∫⁻ z in ball 0 1, ENNReal.ofReal ‖deriv f z‖ ^ 2 < ⊤`.

Proof: the area formula for injective differentiable maps
(`MeasureTheory.lintegral_abs_det_fderiv_eq_addHaar_image`) gives
`∫⁻_𝔻 ofReal |(fderiv ℝ f z).det| = volume (f '' 𝔻) ≤ volume (closedBall 0 R) < ⊤`, and the Jacobian
determinant of the `ℝ`-linear map `z ↦ c * z` is `‖c‖ ^ 2` (`det_smul_one_complex`, via the basis
`Complex.basisOneI` and `Matrix.planeConformalMatrix`), which identifies the integrand with
`ofReal ‖deriv f z‖ ^ 2` because `fderiv ℝ f x = (deriv f x) • 1` for complex-differentiable `f`
(`HasDerivAt.complexToReal_fderiv`).
-/


open Set MeasureTheory
open scoped Topology ENNReal

namespace Work.Jordan

noncomputable section

/-- The matrix of the `ℝ`-linear map `z ↦ c * z` in the basis `(1, I)` is the conformal matrix. -/
theorem toMatrix_lmul_complex (c : ℂ) (hc : c ≠ 0) :
    LinearMap.toMatrix Complex.basisOneI Complex.basisOneI (Algebra.lmul ℝ ℂ c)
      = Matrix.planeConformalMatrix c.re c.im (by
          have h : Complex.normSq c ≠ 0 := (Complex.normSq_pos.mpr hc).ne'
          simpa only [Complex.normSq_apply, pow_two] using h) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [LinearMap.toMatrix_apply, Complex.coe_basisOneI, Complex.coe_basisOneI_repr,
      Matrix.val_planeConformalMatrix, Algebra.lmul]

/-- The `ℝ`-linear map `z ↦ c * z` has determinant `‖c‖ ^ 2`. -/
theorem det_lmul_complex (c : ℂ) : LinearMap.det (Algebra.lmul ℝ ℂ c) = ‖c‖ ^ 2 := by
  rcases eq_or_ne c 0 with rfl | hc
  · simp
  · rw [← LinearMap.det_toMatrix Complex.basisOneI, toMatrix_lmul_complex c hc, Matrix.det_fin_two]
    simp [← Complex.normSq_apply, Complex.normSq_eq_norm_sq, pow_two]

/-- The `ℝ`-linear endomorphism `z ↦ c * z` of `ℂ`, as a continuous linear map, has determinant
`‖c‖ ^ 2`. -/
theorem det_smul_one_complex (c : ℂ) :
    ((c • (1 : ℂ →L[ℝ] ℂ)) : ℂ →L[ℝ] ℂ).det = ‖c‖ ^ 2 := by
  rw [show ((c • (1 : ℂ →L[ℝ] ℂ)) : ℂ →L[ℝ] ℂ).det
      = LinearMap.det (((c • (1 : ℂ →L[ℝ] ℂ)) : ℂ →L[ℝ] ℂ) : ℂ →ₗ[ℝ] ℂ) from rfl]
  rw [show (((c • (1 : ℂ →L[ℝ] ℂ)) : ℂ →L[ℝ] ℂ) : ℂ →ₗ[ℝ] ℂ) = Algebra.lmul ℝ ℂ c from by
    ext x; simp]
  exact det_lmul_complex c

/-- `fderiv` of a complex-differentiable function, as an `ℝ`-linear map. -/
theorem fderiv_eq_smul_one {f : ℂ → ℂ} {x : ℂ} (hd : DifferentiableAt ℂ f x) :
    fderiv ℝ f x = ((deriv f x) • (1 : ℂ →L[ℝ] ℂ)) :=
  (hd.hasDerivAt.complexToReal_fderiv).fderiv

/-- **The Dirichlet integral of a bounded injective holomorphic function is finite.** -/
theorem lintegral_ofReal_sq_norm_deriv_lt_top {f : ℂ → ℂ} {R : ℝ}
    (hd : ∀ z ∈ Metric.ball (0 : ℂ) 1, DifferentiableAt ℂ f z)
    (hinj : Set.InjOn f (Metric.ball (0 : ℂ) 1))
    (hR : ∀ z ∈ Metric.ball (0 : ℂ) 1, ‖f z‖ ≤ R) :
    ∫⁻ z in Metric.ball (0 : ℂ) 1, ENNReal.ofReal (‖deriv f z‖ ^ 2) < ⊤ := by
  have hs : MeasurableSet (Metric.ball (0 : ℂ) 1) := Metric.isOpen_ball.measurableSet
  have hf' : ∀ x ∈ Metric.ball (0 : ℂ) 1,
      HasFDerivWithinAt f (fderiv ℝ f x) (Metric.ball (0 : ℂ) 1) x := fun x hx =>
    ((hd x hx).restrictScalars ℝ).hasFDerivAt.hasFDerivWithinAt
  have hkey := MeasureTheory.lintegral_abs_det_fderiv_eq_addHaar_image
    (μ := volume) (f := f) (f' := fderiv ℝ f) (s := Metric.ball (0 : ℂ) 1) hs hf' hinj
  have hcongr : ∀ x ∈ Metric.ball (0 : ℂ) 1,
      ENNReal.ofReal (‖deriv f x‖ ^ 2) = ENNReal.ofReal |(fderiv ℝ f x).det| := by
    intro x hx
    rw [fderiv_eq_smul_one (hd x hx), det_smul_one_complex, abs_of_nonneg (sq_nonneg _)]
  have hae : (fun z => ENNReal.ofReal (‖deriv f z‖ ^ 2))
      =ᵐ[volume.restrict (Metric.ball (0 : ℂ) 1)]
        (fun z => ENNReal.ofReal |(fderiv ℝ f z).det|) := by
    rw [Filter.EventuallyEq, MeasureTheory.ae_restrict_iff' hs]
    exact Filter.Eventually.of_forall fun x hx => hcongr x hx
  rw [MeasureTheory.lintegral_congr_ae hae, hkey]
  refine lt_of_le_of_lt (measure_mono ?_) (isCompact_closedBall (0 : ℂ) R).measure_lt_top
  rintro y ⟨x, hx, rfl⟩
  rw [Metric.mem_closedBall, dist_zero_right]
  exact hR x hx

end

end Work.Jordan
