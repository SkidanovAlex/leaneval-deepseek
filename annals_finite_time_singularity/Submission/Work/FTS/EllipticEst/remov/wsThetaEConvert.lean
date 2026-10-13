import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.remov

theorem wsThetaEConvert {X A B E P M : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hE : 0 ≤ E)
    (hP : 0 ≤ P) (hPM : 1 + P ≤ M)
    (h : X ≤ (2 * A + 4 * Real.pi ^ 2 * (1 + P) * (1 + B + E)) * P) :
    X ≤ (M * (2 * A + 4 * Real.pi ^ 2 * M * (1 + B))) * (1 + E) := by
  -- Write `f P = 2 * A + 4 * π² * (1 + P) * (1 + B + E)` and `g = 2 * A + 4 * π² * M * (1 + B)`.
  -- The chain is: `f P * P ≤ f M * M ≤ g * (1 + E) * M`.
  have hM0 : 0 ≤ M := by linarith
  have hM1 : 1 ≤ M := by linarith
  have hP'M : P ≤ M := by linarith
  have h1BE : 0 ≤ 1 + B + E := by linarith
  have h4 : (0 : ℝ) ≤ 4 * Real.pi ^ 2 := by positivity
  have hf1 : 0 ≤ 2 * A + 4 * Real.pi ^ 2 * (1 + P) * (1 + B + E) := by positivity
  -- `(1 + P) ≤ M` upgrades the coefficient.
  have hmono : 2 * A + 4 * Real.pi ^ 2 * (1 + P) * (1 + B + E)
      ≤ 2 * A + 4 * Real.pi ^ 2 * M * (1 + B + E) := by
    have hprod : (1 + P) * (1 + B + E) ≤ M * (1 + B + E) :=
      mul_le_mul_of_nonneg_right hPM h1BE
    have := mul_le_mul_of_nonneg_left hprod h4
    nlinarith [this]
  have hstep1 : (2 * A + 4 * Real.pi ^ 2 * (1 + P) * (1 + B + E)) * P
      ≤ (2 * A + 4 * Real.pi ^ 2 * M * (1 + B + E)) * M :=
    calc (2 * A + 4 * Real.pi ^ 2 * (1 + P) * (1 + B + E)) * P
        ≤ (2 * A + 4 * Real.pi ^ 2 * (1 + P) * (1 + B + E)) * M :=
          mul_le_mul_of_nonneg_left hP'M hf1
      _ ≤ (2 * A + 4 * Real.pi ^ 2 * M * (1 + B + E)) * M :=
          mul_le_mul_of_nonneg_right hmono hM0
  -- `2A + 4π²M(1 + B + E) ≤ (2A + 4π²M(1 + B))(1 + E)`.
  have ht1 : 2 * A ≤ 2 * A * (1 + E) := by nlinarith [hA, hE]
  have hBE' : 1 + B + E ≤ (1 + B) * (1 + E) := by nlinarith [hB, hE]
  have ht2 : 4 * Real.pi ^ 2 * M * (1 + B + E)
      ≤ 4 * Real.pi ^ 2 * M * ((1 + B) * (1 + E)) := by
    have h4M : (0 : ℝ) ≤ 4 * Real.pi ^ 2 * M := by positivity
    exact mul_le_mul_of_nonneg_left hBE' h4M
  have hstep2 : 2 * A + 4 * Real.pi ^ 2 * M * (1 + B + E)
      ≤ (2 * A + 4 * Real.pi ^ 2 * M * (1 + B)) * (1 + E) := by
    nlinarith [ht1, ht2]
  calc X ≤ (2 * A + 4 * Real.pi ^ 2 * (1 + P) * (1 + B + E)) * P := h
    _ ≤ (2 * A + 4 * Real.pi ^ 2 * M * (1 + B + E)) * M := hstep1
    _ ≤ ((2 * A + 4 * Real.pi ^ 2 * M * (1 + B)) * (1 + E)) * M :=
        mul_le_mul_of_nonneg_right hstep2 hM0
    _ = (M * (2 * A + 4 * Real.pi ^ 2 * M * (1 + B))) * (1 + E) := by ring

end Work.FTS.EllipticEst.remov
