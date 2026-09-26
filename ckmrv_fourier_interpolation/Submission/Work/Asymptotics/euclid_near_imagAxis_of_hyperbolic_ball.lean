import Mathlib
import Submission.Work.Asymptotics.contourLeftDefs

namespace Work.Asymptotics

/-- **Hyperbolic balls shrink to Euclidean balls around the translate pole.**  For `s₀ > 0` and
any `η > 0` there is `ε₀ > 0` such that any `τ : ℍ` within hyperbolic distance `ε₀` of the centre
`1 + i s₀` has its translate `τ - 1` within Euclidean distance `η` of `i s₀`.

Proof route: `UpperHalfPlane.isometry_real_vadd (-1)` turns `dist τ (onePlusI s₀ hs₀) < ε₀` into
`dist (tauSubOne τ) (imagAxis s₀ hs₀) < ε₀` (because `(-1) +ᵥ (onePlusI s₀ hs₀) = imagAxis s₀ hs₀`),
then `UpperHalfPlane.dist_coe_le` gives
`‖(tauSubOne τ : ℂ) - (s₀ : ℂ) * Complex.I‖ ≤ s₀ * (Real.exp ε₀ - 1)`, and one takes
`ε₀ = Real.log (η / (2 * s₀) + 1)`. -/
theorem euclid_near_imagAxis_of_hyperbolic_ball (s₀ : ℝ) (hs₀ : 0 < s₀) (η : ℝ)
    (hη : 0 < η) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ τ : UpperHalfPlane,
      dist τ (Work.Asymptotics.onePlusI s₀ hs₀) < ε₀ →
        ‖(Work.Asymptotics.tauSubOne τ : ℂ) - (s₀ : ℂ) * Complex.I‖ < η := by
  refine ⟨Real.log (η / (2 * s₀) + 1), ?_, ?_⟩
  · apply Real.log_pos
    have h2 : 0 < η / (2 * s₀) := div_pos hη (by linarith)
    linarith
  · intro τ hτ
    have hpos : 0 < η / (2 * s₀) + 1 := by
      have h2 : 0 < η / (2 * s₀) := div_pos hη (by linarith)
      linarith
    have hexp : Real.exp (Real.log (η / (2 * s₀) + 1)) = η / (2 * s₀) + 1 :=
      Real.exp_log hpos
    -- the translate of the centre: `(-1) +ᵥ (1 + i s₀) = i s₀`
    set w : UpperHalfPlane := (-1 : ℝ) +ᵥ Work.Asymptotics.onePlusI s₀ hs₀ with hw
    have hw_coe : (w : ℂ) = (s₀ : ℂ) * Complex.I := by
      rw [hw, UpperHalfPlane.coe_vadd, Work.Asymptotics.onePlusI_coe]
      push_cast
      ring
    have hw_im : w.im = s₀ := by
      rw [hw, UpperHalfPlane.vadd_im, Work.Asymptotics.onePlusI_im]
    -- the translation is a hyperbolic isometry
    have hdist : dist (Work.Asymptotics.tauSubOne τ) w
        = dist τ (Work.Asymptotics.onePlusI s₀ hs₀) := by
      rw [hw]
      exact (UpperHalfPlane.isometry_real_vadd (-1)).dist_eq τ _
    have hcoe : dist ((Work.Asymptotics.tauSubOne τ : UpperHalfPlane) : ℂ) w
        = ‖((Work.Asymptotics.tauSubOne τ : UpperHalfPlane) : ℂ) - (s₀ : ℂ) * Complex.I‖ := by
      rw [Complex.dist_eq, hw_coe]
    -- the Euclidean distance is controlled by the hyperbolic one
    have hdc := UpperHalfPlane.dist_coe_le (Work.Asymptotics.tauSubOne τ) w
    rw [hcoe, hw_im, hdist] at hdc
    have h1 : Real.exp (dist τ (Work.Asymptotics.onePlusI s₀ hs₀)) < η / (2 * s₀) + 1 := by
      have h := Real.exp_lt_exp.mpr hτ
      rwa [hexp] at h
    have h2 : Real.exp (dist τ (Work.Asymptotics.onePlusI s₀ hs₀)) - 1 < η / (2 * s₀) := by
      linarith
    have heq : s₀ * (η / (2 * s₀)) = η / 2 := by
      field_simp
    have hmul := mul_lt_mul_of_pos_left h2 hs₀
    rw [heq] at hmul
    linarith

end Work.Asymptotics
