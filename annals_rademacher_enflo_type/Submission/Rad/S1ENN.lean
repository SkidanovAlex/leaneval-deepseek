import Submission.Rad.S1
import Submission.Commons.Analysis.ENNReal.mul_le_mul_left_iff
set_option autoImplicit false
open Function MeasureTheory ProbabilityTheory Measure
open scoped ENNReal

namespace RadType
open RademacherEnfloType

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]

lemma ofReal_norm_rpow (v : X) {p : ℝ} (hp : 0 ≤ p) :
    ENNReal.ofReal (‖v‖ ^ p) = ‖v‖ₑ ^ p := by
  rw [← ENNReal.ofReal_rpow_of_nonneg (norm_nonneg v) hp]
  rw [ofReal_norm]

lemma ofReal_two : (2 : ℝ≥0∞) = ENNReal.ofReal (2 : ℝ) := by
  norm_num [ENNReal.ofReal]

/-- Doubled midpoint convexity of the `p`-power of the `ennorm`, `p ≥ 1`. -/
lemma ennorm_midpoint_double (u v : X) {p : ℝ} (hp : 1 ≤ p) :
    (2 : ℝ≥0∞) * ‖(1 / 2 : ℝ) • (u - v)‖ₑ ^ p ≤ ‖u‖ₑ ^ p + ‖v‖ₑ ^ p := by
  have hreal : 2 * ‖(1 / 2 : ℝ) • (u - v)‖ ^ p ≤ ‖u‖ ^ p + ‖v‖ ^ p := by
    have h := norm_midpoint_smul_pow_le u v hp
    nlinarith
  have hp0 : 0 ≤ p := by linarith
  calc
    (2 : ℝ≥0∞) * ‖(1 / 2 : ℝ) • (u - v)‖ₑ ^ p
        = (2 : ℝ≥0∞) * ENNReal.ofReal (‖(1 / 2 : ℝ) • (u - v)‖ ^ p) := by
          rw [← ofReal_norm_rpow ((1 / 2 : ℝ) • (u - v)) hp0]
    _ = ENNReal.ofReal (2 * ‖(1 / 2 : ℝ) • (u - v)‖ ^ p) := by
          rw [ofReal_two, ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
    _ ≤ ENNReal.ofReal (‖u‖ ^ p + ‖v‖ ^ p) := ENNReal.ofReal_le_ofReal hreal
    _ = ENNReal.ofReal (‖u‖ ^ p) + ENNReal.ofReal (‖v‖ ^ p) := by
          rw [ENNReal.ofReal_add (Real.rpow_nonneg (norm_nonneg u) p)
            (Real.rpow_nonneg (norm_nonneg v) p)]
    _ = ‖u‖ₑ ^ p + ‖v‖ₑ ^ p := by
          rw [ofReal_norm_rpow u hp0, ofReal_norm_rpow v hp0]

/--
Symmetrization at the level of `lintegral`s (ENNReal): the expected `p`-power distance between
`f(ε)` and `f(-ε)` is at most that between `f(ε)` and any fixed point `c`.
-/
lemma symm_enorm_lint_le {n : ℕ} (f : Ω n → X) (c : X) {p : ℝ} (hp : 1 ≤ p) :
    (∫⁻ (ε : Ω n), ‖(1 / 2 : ℝ) • (f ε - f (negΩ ε))‖ₑ ^ p
        ∂rademacherProductDistribution (Fin n))
    ≤ ∫⁻ (ε : Ω n), ‖f ε - c‖ₑ ^ p ∂rademacherProductDistribution (Fin n) := by
  let A : Ω n → ℝ≥0∞ := fun ε => ‖(1 / 2 : ℝ) • (f ε - f (negΩ ε))‖ₑ ^ p
  let U : Ω n → ℝ≥0∞ := fun ε => ‖f ε - c‖ₑ ^ p
  let V : Ω n → ℝ≥0∞ := fun ε => ‖f (negΩ ε) - c‖ₑ ^ p
  have hpoint : ∀ ε : Ω n, (2 : ℝ≥0∞) * A ε ≤ U ε + V ε := by
    intro ε
    change (2 : ℝ≥0∞) * ‖(1 / 2 : ℝ) • (f ε - f (negΩ ε))‖ₑ ^ p
      ≤ ‖f ε - c‖ₑ ^ p + ‖f (negΩ ε) - c‖ₑ ^ p
    have hsub : (1 / 2 : ℝ) • (f ε - f (negΩ ε)) = (1 / 2 : ℝ) • ((f ε - c) - (f (negΩ ε) - c)) := by
      congr 1
      abel
    rw [hsub]
    exact ennorm_midpoint_double (f ε - c) (f (negΩ ε) - c) hp
  have h2A : (2 : ℝ≥0∞) * (∫⁻ (ε : Ω n), A ε ∂rademacherProductDistribution (Fin n))
      ≤ (∫⁻ (ε : Ω n), U ε ∂rademacherProductDistribution (Fin n)) +
        (∫⁻ (ε : Ω n), V ε ∂rademacherProductDistribution (Fin n)) := by
    have hmono : (∫⁻ (ε : Ω n), (2 : ℝ≥0∞) * A ε ∂rademacherProductDistribution (Fin n))
        ≤ ∫⁻ (ε : Ω n), (U ε + V ε) ∂rademacherProductDistribution (Fin n) := by
      apply lintegral_mono
      intro ε
      exact hpoint ε
    calc
      (2 : ℝ≥0∞) * (∫⁻ (ε : Ω n), A ε ∂rademacherProductDistribution (Fin n))
          = ∫⁻ (ε : Ω n), (2 : ℝ≥0∞) * A ε ∂rademacherProductDistribution (Fin n) := by
            rw [lintegral_const_mul' (r := (2 : ℝ≥0∞)) (f := A) (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)]
      _ ≤ ∫⁻ (ε : Ω n), (U ε + V ε) ∂rademacherProductDistribution (Fin n) := hmono
      _ = (∫⁻ (ε : Ω n), U ε ∂rademacherProductDistribution (Fin n)) +
          (∫⁻ (ε : Ω n), V ε ∂rademacherProductDistribution (Fin n)) := by
            rw [lintegral_add_right (fun ε : Ω n => U ε) (RadType.measurable_cube_ennreal V)]
  have hsym : (∫⁻ (ε : Ω n), V ε ∂rademacherProductDistribution (Fin n))
      = ∫⁻ (ε : Ω n), U ε ∂rademacherProductDistribution (Fin n) := by
    unfold V U
    exact lintegral_negΩ (fun ε : Ω n => ‖f ε - c‖ₑ ^ p)
  have h2 : (2 : ℝ≥0∞) ≠ 0 := by norm_num
  have h2t : (2 : ℝ≥0∞) ≠ ⊤ := by norm_num
  calc
    (∫⁻ (ε : Ω n), A ε ∂rademacherProductDistribution (Fin n))
        ≤ ∫⁻ (ε : Ω n), U ε ∂rademacherProductDistribution (Fin n) := by
          rw [← (Commons.Analysis.ENNReal.mul_le_mul_left_iff (a :=
            ∫⁻ (ε : Ω n), A ε ∂rademacherProductDistribution (Fin n))
            (b := ∫⁻ (ε : Ω n), U ε ∂rademacherProductDistribution (Fin n)) (c := (2 : ℝ≥0∞)) h2 h2t)]
          calc
            (2 : ℝ≥0∞) * (∫⁻ (ε : Ω n), A ε ∂rademacherProductDistribution (Fin n))
                ≤ (∫⁻ (ε : Ω n), U ε ∂rademacherProductDistribution (Fin n)) +
                  (∫⁻ (ε : Ω n), V ε ∂rademacherProductDistribution (Fin n)) := h2A
            _ = (∫⁻ (ε : Ω n), U ε ∂rademacherProductDistribution (Fin n)) +
                (∫⁻ (ε : Ω n), U ε ∂rademacherProductDistribution (Fin n)) := by rw [hsym]
            _ = (2 : ℝ≥0∞) * (∫⁻ (ε : Ω n), U ε ∂rademacherProductDistribution (Fin n)) := by
                  exact (two_mul _).symm
    _ = ∫⁻ (ε : Ω n), ‖f ε - c‖ₑ ^ p ∂rademacherProductDistribution (Fin n) := rfl

end RadType
