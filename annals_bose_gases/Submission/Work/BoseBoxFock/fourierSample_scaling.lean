import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseBoxFock

/-- Change of variables `y = (ℓ/2π) • p` in a Fourier sample: for `ℓ > 0`, `Φ : ℝ³ → ℂ` and
`w : ℝ³`,
`∫_y Φ((2π/ℓ) • y) e^{-2πi⟪y,w⟫} dy = (ℓ/2π)³ ∫_p Φ p e^{-i⟪ℓ • w, p⟫} dp`.
(No integrability hypothesis is needed: `Measure.integral_comp_smul_of_nonneg` holds for
arbitrary functions, both sides being `0` for a non-integrable `Φ`.  The proof is a short chain of
`Measure.integral_comp_smul_of_nonneg` + `real_inner_smul_left`/`real_inner_comm` + `ring`.) -/
theorem fourierSample_scaling {ℓ : ℝ} (hℓ : 0 < ℓ)
    (Φ : EuclideanSpace ℝ (Fin 3) → ℂ) (w : EuclideanSpace ℝ (Fin 3)) :
    (∫ y : EuclideanSpace ℝ (Fin 3), Φ ((2 * Real.pi / ℓ) • y) *
        Complex.exp (-(2 * Real.pi * Complex.I * (inner ℝ y w))))
      = ((ℓ / (2 * Real.pi)) ^ 3) *
        ∫ p : EuclideanSpace ℝ (Fin 3),
          Φ p * Complex.exp (-(Complex.I * (inner ℝ (ℓ • w) p : ℂ))) := by
  -- The substitution `y = R • p` with `R = ℓ / (2π)`.
  set R : ℝ := ℓ / (2 * Real.pi) with hRdef
  have hRpos : 0 < R := by rw [hRdef]; positivity
  have hRinv : R⁻¹ = 2 * Real.pi / ℓ := by rw [hRdef, inv_div]
  have hRmul : 2 * Real.pi * R = ℓ := by rw [hRdef]; field_simp
  -- The exponent identity, reduced to a real identity on inner products.
  have harg (p : EuclideanSpace ℝ (Fin 3)) :
      (2 * (Real.pi : ℂ)) * (inner ℝ (R • p) w : ℂ) = (inner ℝ (ℓ • w) p : ℂ) := by
    have h : ((2 * Real.pi * inner ℝ (R • p) w : ℝ) : ℂ) = ((inner ℝ (ℓ • w) p : ℝ) : ℂ) := by
      rw [real_inner_smul_left, real_inner_smul_left, ← real_inner_comm p w, ← mul_assoc, hRmul]
    push_cast at h
    exact h
  have hexp (p : EuclideanSpace ℝ (Fin 3)) :
      Complex.exp (-(2 * Real.pi * Complex.I * (inner ℝ (R • p) w : ℂ)))
        = Complex.exp (-(Complex.I * (inner ℝ (ℓ • w) p : ℂ))) := by
    congr 1
    rw [show -(2 * Real.pi * Complex.I * (inner ℝ (R • p) w : ℂ))
        = -(Complex.I * ((2 * (Real.pi : ℂ)) * (inner ℝ (R • p) w : ℂ))) by ring, harg p]
  -- The integrand of the left-hand side is the substituted integrand.
  have hpt (y : EuclideanSpace ℝ (Fin 3)) :
      Φ (R⁻¹ • y) * Complex.exp (-(2 * Real.pi * Complex.I * (inner ℝ (R • (R⁻¹ • y)) w : ℂ)))
        = Φ ((2 * Real.pi / ℓ) • y) *
          Complex.exp (-(2 * Real.pi * Complex.I * (inner ℝ y w : ℂ))) := by
    have h1 : R • (R⁻¹ • y) = y := by rw [smul_smul, mul_inv_cancel₀ (ne_of_gt hRpos), one_smul]
    rw [h1, hRinv]
  have hL : (∫ y : EuclideanSpace ℝ (Fin 3), Φ ((2 * Real.pi / ℓ) • y) *
        Complex.exp (-(2 * Real.pi * Complex.I * (inner ℝ y w))))
      = ∫ y : EuclideanSpace ℝ (Fin 3),
          (fun p : EuclideanSpace ℝ (Fin 3) =>
            Φ p * Complex.exp (-(2 * Real.pi * Complex.I * (inner ℝ (R • p) w : ℂ)))) (R⁻¹ • y) := by
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    exact (hpt y).symm
  have hkey := MeasureTheory.Measure.integral_comp_inv_smul_of_nonneg
      (μ := (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))))
      (fun p : EuclideanSpace ℝ (Fin 3) =>
        Φ p * Complex.exp (-(2 * Real.pi * Complex.I * (inner ℝ (R • p) w : ℂ))))
      (le_of_lt hRpos)
  have hIntEq : (∫ p : EuclideanSpace ℝ (Fin 3),
        Φ p * Complex.exp (-(2 * Real.pi * Complex.I * (inner ℝ (R • p) w : ℂ))))
      = ∫ p : EuclideanSpace ℝ (Fin 3),
          Φ p * Complex.exp (-(Complex.I * (inner ℝ (ℓ • w) p : ℂ))) := by
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
    show Φ p * Complex.exp (-(2 * Real.pi * Complex.I * (inner ℝ (R • p) w : ℂ))) =
      Φ p * Complex.exp (-(Complex.I * (inner ℝ (ℓ • w) p : ℂ)))
    rw [hexp p]
  have hfin : Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 3 := by simp
  have hRC : (R : ℂ) = (ℓ : ℂ) / (2 * (Real.pi : ℂ)) := by
    rw [hRdef]; push_cast; ring
  rw [hL, hkey, hIntEq, hfin, Complex.real_smul, Complex.ofReal_pow, hRC]

end Work.BoseBoxFock
