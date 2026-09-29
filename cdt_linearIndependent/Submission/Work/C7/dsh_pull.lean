import Mathlib
import Submission.Work.C7.seven_setup

namespace Work.C7

/-- Pullback of the derivation `∂ = x(x-1)²·d/dx` (`Work.C7.dsh`) to the three series
`g 5`, `g 6`, `Jps`.

The two "integral" functions are pinned down by `y·(g 5)' = (g 2)·y'` and
`y·(g 6)' = (g 3)·y'`; multiplying by `(x-1)²` and clearing the factor `x` via
`y·(x-1) = x²`, `(x-1)²·y' = x(x-2)` turns these into `x(x-1)·(g i)' = (x-2)·g i`, whence
`∂(g i) = (x-1)·(x(x-1)·(g i)') = (x-1)(x-2)·g i`.  For `g 6` the rational prefactor
`x - φ = x(x-2)/(x-1)` of `g 3` is absorbed by `(x-1)(x-φ) = x(x-2)`.  The `Jps` identity is the
first-order ODE `2x(x-1)·J' - x·J = 2(1-x)·L` solved for `J'` and multiplied by `(x-1)`. -/
theorem dsh_pull
    (h2 : Work.C7.g 2 = -(PowerSeries.C (1 / 2 : ℚ)) * Work.C7.Lps ^ 2)
    (h3 : Work.C7.g 3 = (PowerSeries.X - Submission.CDT.sympPhi) *
      (2 * Work.C7.Li2ps + PowerSeries.C (1 / 2 : ℚ) * Work.C7.Lps ^ 2))
    (h6 : Work.C7.yps * PowerSeries.derivative (R := ℚ) (Work.C7.g 5)
      = (Work.C7.g 2) * PowerSeries.derivative (R := ℚ) Work.C7.yps)
    (h7 : Work.C7.yps * PowerSeries.derivative (R := ℚ) (Work.C7.g 6)
      = (Work.C7.g 3) * PowerSeries.derivative (R := ℚ) Work.C7.yps)
    (hJ : 2 * PowerSeries.X * (PowerSeries.X - 1) * PowerSeries.derivative (R := ℚ) Work.C7.Jps
      - PowerSeries.X * Work.C7.Jps = 2 * (1 - PowerSeries.X) * Work.C7.Lps) :
    Work.C7.dsh (Work.C7.g 5)
        = PowerSeries.C (-(1 / 2) : ℚ) * (PowerSeries.X - 1) * (PowerSeries.X - 2)
          * Work.C7.Lps ^ 2 ∧
      Work.C7.dsh (Work.C7.g 6)
        = PowerSeries.X * (PowerSeries.X - 2) ^ 2 *
          (2 * Work.C7.Li2ps + PowerSeries.C (1 / 2 : ℚ) * Work.C7.Lps ^ 2) ∧
      Work.C7.dsh Work.C7.Jps
        = PowerSeries.C (1 / 2 : ℚ) * (PowerSeries.X * (PowerSeries.X - 1)) * Work.C7.Jps
          - (PowerSeries.X - 1) ^ 2 * Work.C7.Lps := by
  -- From `y·D = G·y'` (with `y = x²/(x-1)`, `y' = x(x-2)/(x-1)²`) deduce
  -- `x(x-1)·D = (x-2)·G`, after clearing the denominators `(x-1)²` and the factor `x`.
  have key_gen : ∀ (D G : PowerSeries ℚ), yps * D = G * PowerSeries.derivative (R := ℚ) yps →
      PowerSeries.X * (PowerSeries.X - 1) * D = (PowerSeries.X - 2) * G := by
    intro D G h
    have hh := congrArg (fun z : PowerSeries ℚ => ((PowerSeries.X : PowerSeries ℚ) - 1)^2 * z) h
    rw [show ((PowerSeries.X:PowerSeries ℚ)-1)^2 * (yps * D)
          = (((PowerSeries.X:PowerSeries ℚ)-1)^2 * yps) * D by ring,
        sq_sub_one_mul_yps,
        show ((PowerSeries.X:PowerSeries ℚ)-1)^2 * (G * PowerSeries.derivative (R := ℚ) yps)
          = (((PowerSeries.X:PowerSeries ℚ)-1)^2 * PowerSeries.derivative (R := ℚ) yps) * G by ring,
        sq_sub_one_mul_deriv_yps] at hh
    exact mul_left_cancel₀ X_ne_zero (by linear_combination hh)
  -- `(x-1)(x-2)(x-φ) = x(x-2)²`, i.e. `(x-1)(x-φ) = x(x-2)` where `x-φ = x(x-2)/(x-1)`.
  have hcfun : ((PowerSeries.X : PowerSeries ℚ) - 1) * (PowerSeries.X - 2)
      * (PowerSeries.X - Submission.CDT.sympPhi) = PowerSeries.X * (PowerSeries.X - 2)^2 := by
    rw [cfun_sub_phi, show cfun = (PowerSeries.X : PowerSeries ℚ) * (PowerSeries.X - 2)
        * ((PowerSeries.X : PowerSeries ℚ) - 1)⁻¹ from rfl]
    linear_combination (PowerSeries.X * (PowerSeries.X - 2) * (PowerSeries.X - 2)) * mul_gU
  refine ⟨?_, ?_, ?_⟩
  · rw [dsh]
    rw [show (PowerSeries.X * (PowerSeries.X - 1)^2) * PowerSeries.derivative (R := ℚ) (g 5)
          = (PowerSeries.X - 1) * (PowerSeries.X * (PowerSeries.X - 1)
              * PowerSeries.derivative (R := ℚ) (g 5)) by ring,
        key_gen _ _ h6, h2]
    have hc : PowerSeries.C (-(1/2) : ℚ) = -(PowerSeries.C (1/2 : ℚ)) := by simp
    rw [hc]; ring
  · rw [dsh]
    rw [show (PowerSeries.X * (PowerSeries.X - 1)^2) * PowerSeries.derivative (R := ℚ) (g 6)
          = (PowerSeries.X - 1) * (PowerSeries.X * (PowerSeries.X - 1)
              * PowerSeries.derivative (R := ℚ) (g 6)) by ring,
        key_gen _ _ h7, h3]
    linear_combination (2 * Li2ps + PowerSeries.C (1/2 : ℚ) * Lps^2) * hcfun
  · rw [dsh]
    have hC2 : PowerSeries.C (1/2 : ℚ) * (2 : PowerSeries ℚ) = 1 := by
      rw [show (2 : PowerSeries ℚ) = PowerSeries.C (2 : ℚ) from rfl, ← map_mul]; norm_num
    have hmid : PowerSeries.X * (PowerSeries.X - 1) * PowerSeries.derivative (R := ℚ) Jps
        = PowerSeries.C (1/2 : ℚ) * PowerSeries.X * Jps - (PowerSeries.X - 1) * Lps := by
      linear_combination (PowerSeries.C (1/2 : ℚ)) * hJ
        - (PowerSeries.X * (PowerSeries.X - 1) * PowerSeries.derivative (R := ℚ) Jps
            + (PowerSeries.X - 1) * Lps) * hC2
    linear_combination (PowerSeries.X - 1) * hmid

end Work.C7
