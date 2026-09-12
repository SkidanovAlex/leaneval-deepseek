import Submission.Rad.Mineq
import Submission.Rad.S1
import Submission.Commons.Analysis.SpecialFunctions.pi_sqrt2_rpow_assembly
set_option autoImplicit false
open Function MeasureTheory ProbabilityTheory Measure
open scoped ENNReal BigOperators Interval
noncomputable section
namespace RadType
open RademacherEnfloType

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]

/-- The real Enflo-type inequality with constant `(π/√2)·c`, from Rademacher type `c`
(symmetrization + main inequality + `(π/2)^p 2^(p/2) = (π/√2)^p`). -/
lemma enflo_real_ineq {n : ℕ} (hn : 1 ≤ n) (f : Ω n → X) {pow : ℝ} (hp1 : 1 ≤ pow) (hp2 : pow ≤ 2)
    {c : ℝ} (hc0 : 0 ≤ c)
    (hRad : ∀ (m : ℕ), 1 ≤ m → ∀ x : Fin m → X,
      (∑ ε : Ω m, ((1 / 2 : ℝ) ^ m) * ‖∑ j : Fin m, (((ε j : C) : ℝ) • x j)‖ ^ pow)
        ≤ c ^ pow * (∑ j : Fin m, ‖x j‖ ^ pow)) :
    meanReal (fun ε : Ω n => ‖(1 / 2 : ℝ) • (f ε - f (negΩ ε))‖ ^ pow)
      ≤ ((Real.pi / Real.sqrt 2) * c) ^ pow *
          (∑ j : Fin n, meanReal (fun x : Ω n => ‖D j f x‖ ^ pow)) := by
  let S : ℝ := ∑ j : Fin n, meanReal (fun x : Ω n => ‖D j f x‖ ^ pow)
  calc
    meanReal (fun ε : Ω n => ‖(1 / 2 : ℝ) • (f ε - f (negΩ ε))‖ ^ pow)
        ≤ meanReal (fun x : Ω n => ‖f x - meanX f‖ ^ pow) := symm_pow_mean_le f hp1
    _ ≤ (Real.pi / 2) ^ pow * (2 : ℝ) ^ (pow / 2) * c ^ pow * S := by
          simpa [S] using main_ineq (n := n) hn f hp1 hp2 hc0 hRad
    _ = ((Real.pi / 2) ^ pow * (2 : ℝ) ^ (pow / 2)) * (c ^ pow * S) := by ring
    _ = (Real.pi / Real.sqrt 2) ^ pow * (c ^ pow * S) := by
          rw [Commons.Analysis.SpecialFunctions.pi_sqrt2_rpow_assembly pow]
    _ = (Real.pi / Real.sqrt 2) ^ pow * c ^ pow * S := by ring
    _ = ((Real.pi / Real.sqrt 2) * c) ^ pow * S := by
          have hx : 0 ≤ Real.pi / Real.sqrt 2 := by positivity
          rw [← Real.mul_rpow hx hc0]
    _ = ((Real.pi / Real.sqrt 2) * c) ^ pow *
          (∑ j : Fin n, meanReal (fun x : Ω n => ‖D j f x‖ ^ pow)) := by rfl

end RadType
