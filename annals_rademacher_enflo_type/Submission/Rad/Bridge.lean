import Submission.Rad.S1ENN
set_option autoImplicit false
open Function MeasureTheory ProbabilityTheory Measure
open scoped ENNReal

namespace RadType
open RademacherEnfloType

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]

/-- The `lintegral` of a real power of an `ennorm` equals `ofReal` of the real integral of the
power of the norm. -/
lemma lintegral_enorm_rpow {n : ℕ} (F : Ω n → X) {p : ℝ} (hp : 0 ≤ p) :
    (∫⁻ (ε : Ω n), ‖F ε‖ₑ ^ p ∂rademacherProductDistribution (Fin n))
      = ENNReal.ofReal (∫ ε : Ω n, ‖F ε‖ ^ p ∂rademacherProductDistribution (Fin n)) := by
  let g : Ω n → NNReal := fun ε => ⟨‖F ε‖ ^ p, Real.rpow_nonneg (norm_nonneg (F ε)) p⟩
  have hconv : ∀ ε : Ω n, ENNReal.ofReal (‖F ε‖ ^ p) = (g ε : ℝ≥0∞) := by
    intro ε
    rw [ENNReal.ofReal_eq_coe_nnreal (Real.rpow_nonneg (norm_nonneg (F ε)) p)]
    rfl
  calc
    (∫⁻ (ε : Ω n), ‖F ε‖ₑ ^ p ∂rademacherProductDistribution (Fin n))
        = ∫⁻ (ε : Ω n), ENNReal.ofReal (‖F ε‖ ^ p) ∂rademacherProductDistribution (Fin n) := by
          apply lintegral_congr
          intro ε
          exact (ofReal_norm_rpow (F ε) hp).symm
    _ = ∫⁻ (ε : Ω n), (g ε : ℝ≥0∞) ∂rademacherProductDistribution (Fin n) := by
          apply lintegral_congr
          intro ε
          exact hconv ε
    _ = ENNReal.ofReal (∫ ε : Ω n, (g ε : ℝ) ∂rademacherProductDistribution (Fin n)) := by
          exact lintegral_coe_eq_integral g (integrable_cube (fun ε : Ω n => (g ε : ℝ)))
    _ = ENNReal.ofReal (∫ ε : Ω n, ‖F ε‖ ^ p ∂rademacherProductDistribution (Fin n)) := rfl

end RadType
