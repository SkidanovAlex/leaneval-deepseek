import Mathlib
import Submission.Work.BourgainPlan.IonescuWainger.OpArcDefs

-- The hypothesis `hφ` is not needed: the identity below holds for *every* circle function,
-- because it is a consequence of translation invariance and the character identity alone.
set_option linter.unusedVariables false

namespace Work.BourgainPlan.IonescuWainger

/-- The circle characters are additive in their *argument*: `e_m (x + y) = e_m x * e_m y`.
(This is the counterpart of `fourier_add`, which is additive in the *index* `m`.) -/
theorem fourier_add_arg {T : ℝ} (m : ℤ) (x y : AddCircle T) :
    fourier m (x + y) = fourier m x * fourier m y := by
  rw [fourier_apply, smul_add, AddCircle.toCircle_add, Circle.coe_mul, ← fourier_apply,
    ← fourier_apply]

/-- **The Fourier coefficients of a translate.**  Translating a circle function by `β` multiplies its
`m`-th Fourier coefficient by `star (fourier m β)`. -/
theorem fourierCoeff_arcTranslate (φ : Circle → ℂ)
    (hφ : MeasureTheory.MemLp φ ⊤ (AddCircle.haarAddCircle (T := 1)))
    (β : Circle) (m : ℤ) :
    ∫ ξ, arcTranslate β φ ξ * star (fourier m ξ) ∂(AddCircle.haarAddCircle (T := 1))
      = star (fourier m β) * ∫ ξ, φ ξ * star (fourier m ξ)
          ∂(AddCircle.haarAddCircle (T := 1)) := by
  -- Translation invariance of the Haar measure on the circle:
  -- `∫ x, F (x + β) = ∫ x, F x` for `F ξ = φ (ξ - β) * star (fourier m ξ)`.
  have hshift : ∫ x : Circle, φ x * star (fourier m (x + β))
        ∂(AddCircle.haarAddCircle (T := 1))
      = ∫ x : Circle, φ (x - β) * star (fourier m x)
          ∂(AddCircle.haarAddCircle (T := 1)) := by
    have h := MeasureTheory.integral_add_right_eq_self (μ := AddCircle.haarAddCircle (T := 1))
      (f := fun ξ : Circle => φ (ξ - β) * star (fourier m ξ)) (g := β)
    simpa using h
  -- Rewrite the integrand using `fourier m (x + β) = fourier m x * fourier m β` and pull the
  -- constant `star (fourier m β)` out of the integral.
  have key : ∫ ξ : Circle, arcTranslate β φ ξ * star (fourier m ξ)
        ∂(AddCircle.haarAddCircle (T := 1))
      = ∫ ξ : Circle, star (fourier m β) * (φ ξ * star (fourier m ξ))
          ∂(AddCircle.haarAddCircle (T := 1)) := by
    have e1 : (fun ξ : Circle => arcTranslate β φ ξ * star (fourier m ξ))
        = (fun ξ : Circle => φ (ξ - β) * star (fourier m ξ)) := by
      funext ξ; simp
    rw [e1, ← hshift]
    refine MeasureTheory.integral_congr_ae ?_
    filter_upwards with x
    rw [fourier_add_arg m x β, star_mul]
    ring
  rw [key]
  exact MeasureTheory.integral_smul (star (fourier m β)) (fun ξ => φ ξ * star (fourier m ξ))

end Work.BourgainPlan.IonescuWainger
