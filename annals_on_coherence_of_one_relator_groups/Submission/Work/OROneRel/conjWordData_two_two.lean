import Mathlib
import Submission.Work.OROneRel.Basic
import Submission.Work.OROneRel.relatorNorm_letterPow_mul_letterPow

namespace Work.OROneRel

theorem conjWordData_two_two :
    ∃ (x₀ : Fin 2) (s : FreeGroup (Fin 2)) (sect : Fin 2 → FreeGroup (ULift.{0,0} (Fin 2))),
      (∀ x : Fin 2, FreeGroup.lift (fun i : ULift.{0,0} (Fin 2) =>
          if i = ULift.up (0 : Fin 2) then FreeGroup.of x₀ else s) (sect x) = FreeGroup.of x) ∧
      sect x₀ = FreeGroup.of (ULift.up (0 : Fin 2)) ∧
      FreeGroup.lift sect s = FreeGroup.of (ULift.up (1 : Fin 2)) ∧
      (FreeGroup.of (0 : Fin 2) ^ 2 * FreeGroup.of (1 : Fin 2) ^ 2
        = FreeGroup.of x₀ * s * (FreeGroup.of x₀)⁻¹ * s) ∧
      2 ≤ relatorNorm (FreeGroup.of (0 : Fin 2) ^ 2 * FreeGroup.of (1 : Fin 2) ^ 2) := by
  -- The torus-knot relator `a ^ 2 * b ^ 2` is the conjugate-commutator word
  -- `a * (a * b) * a⁻¹ * (a * b)` (with `a = of 0`, `b = of 1`); equivalently
  -- `a ^ 2 * b ^ 2 = [a, b] * (a * b) ^ 2`, i.e. `a ^ 2 * b ^ 2 = x₀ * s * x₀⁻¹ * s`
  -- for `x₀ = a`, `s = a * b`.
  refine ⟨0, FreeGroup.of 0 * FreeGroup.of 1,
    (fun x : Fin 2 => if x = 0 then FreeGroup.of (ULift.up 0)
      else (FreeGroup.of (ULift.up 0))⁻¹ * FreeGroup.of (ULift.up 1)),
    ?_, ?_, ?_, ?_, ?_⟩
  · -- `sect` is a section of the retraction `up 0 ↦ x₀`, `up 1 ↦ s`
    intro x
    fin_cases x <;> simp
  · simp
  · -- `lift sect s = of (up 1)`
    simp [FreeGroup.lift_apply_of]
  · rw [pow_two, pow_two]
    group
  · have h := relatorNorm_letterPow_mul_letterPow (α := Fin 2) (a := 0) (b := 1) (by decide) 2 2
    rw [h]
    norm_num

end Work.OROneRel
