import Mathlib
import Submission.Work.CKFinal.LineDecay.Tail_integral_eight

namespace Work.CKFinal.LineDecay

open MeasureTheory Filter

/-- The twenty-four dimensional tail integral is an immediate corollary of the general
elementary tail estimate `Tail_integral_eight 0`: the integrand
`e^{-2πy} · e^{-πt}/(1 + e^{2π(y-t)})` is the constant multiple `e^{-2πy}` of the
`A = 0` integrand `e^{-πt}/(1 + e^{2π(y-t)})`, and the hypothesis `1 ≤ y` gives `1 + y ≥ 1`
so that `(1+y)^0 = 1`.  Multiplying the resulting bound `e^{-2πy} · C e^{-πy}` gives
`C e^{-3πy}`. -/
theorem Tail_integral_twentyfour :
    ∃ C : ℝ, 0 < C ∧ ∀ y : ℝ, 1 ≤ y →
      MeasureTheory.IntegrableOn (fun t : ℝ => Real.exp (-(2 * Real.pi * y)) *
          (Real.exp (-(Real.pi * t)) / (1 + Real.exp (2 * Real.pi * (y - t))))) (Set.Ici 1) ∧
      ∫ t in Set.Ici (1 : ℝ), Real.exp (-(2 * Real.pi * y)) *
          (Real.exp (-(Real.pi * t)) / (1 + Real.exp (2 * Real.pi * (y - t))))
        ≤ C * Real.exp (-(3 * Real.pi * y)) := by
  obtain ⟨C, hCpos, hC⟩ := Tail_integral_eight 0
  refine ⟨C, hCpos, fun y hy => ?_⟩
  obtain ⟨hInt, hbnd⟩ := hC y hy
  -- Strip the factor `(1+t)^0 = 1` from the integrability statement.
  have hInt' : IntegrableOn (fun t : ℝ =>
      Real.exp (-(Real.pi * t)) / (1 + Real.exp (2 * Real.pi * (y - t)))) (Set.Ici 1) := by
    have h := hInt
    simp only [Real.rpow_zero, one_mul] at h
    exact h
  -- Strip `(1+t)^0 = 1` and `(1+y)^0 = 1` from the bound.
  have hbnd' : ∫ t in Set.Ici (1 : ℝ),
        (Real.exp (-(Real.pi * t)) / (1 + Real.exp (2 * Real.pi * (y - t))))
      ≤ C * Real.exp (-(Real.pi * y)) := by
    have h := hbnd
    simp only [Real.rpow_zero, one_mul, mul_one] at h
    exact h
  refine ⟨?_, ?_⟩
  · -- Integrability of the constant multiple of the `A = 0` integrand.
    have h := hInt'.const_mul (Real.exp (-(2 * Real.pi * y)))
    exact h
  · -- Factor out the constant and multiply the bounds.
    have hconst : ∫ t in Set.Ici (1 : ℝ), Real.exp (-(2 * Real.pi * y)) *
          (Real.exp (-(Real.pi * t)) / (1 + Real.exp (2 * Real.pi * (y - t))))
        = Real.exp (-(2 * Real.pi * y)) * ∫ t in Set.Ici (1 : ℝ),
            (Real.exp (-(Real.pi * t)) / (1 + Real.exp (2 * Real.pi * (y - t)))) :=
      MeasureTheory.integral_const_mul _ _
    calc ∫ t in Set.Ici (1 : ℝ), Real.exp (-(2 * Real.pi * y)) *
          (Real.exp (-(Real.pi * t)) / (1 + Real.exp (2 * Real.pi * (y - t))))
        = Real.exp (-(2 * Real.pi * y)) * ∫ t in Set.Ici (1 : ℝ),
            (Real.exp (-(Real.pi * t)) / (1 + Real.exp (2 * Real.pi * (y - t)))) := hconst
      _ ≤ Real.exp (-(2 * Real.pi * y)) * (C * Real.exp (-(Real.pi * y))) :=
          mul_le_mul_of_nonneg_left hbnd' (Real.exp_pos _).le
      _ = C * Real.exp (-(3 * Real.pi * y)) := by
          rw [← mul_assoc, mul_comm (Real.exp (-(2 * Real.pi * y))) C, mul_assoc]
          congr 1
          rw [← Real.exp_add]
          ring_nf

end Work.CKFinal.LineDecay
