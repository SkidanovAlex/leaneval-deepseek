import Mathlib
import Submission.Work.Pure.b4_defs
import Submission.Work.Pure.b4_B2_ode
import Submission.Work.Pure.b4_theta_defs
import Submission.Work.Pure.b4_psi_rel
import Submission.Work.Pure.b4_B2_subst_sympY

namespace Work.Pure

/-- Route. (1) `((1-x)·b4L' = -1)` and `(x·b4Li2' = -b4L)` are one-step coefficient identities;
`b4L.subst sympPhi = -b4L` follows by differentiating `b4L.subst sympPhi + b4L` (chain rule
`PowerSeries.derivative_subst` with `sympPhi_hasSubst`, `derivative sympPhi = -(X-1)⁻²`
— see `Submission.CDT.SympExplicitodeBridge`, where `W = (X-1)⁻¹`, `derivative_W = -W²`,
`(sympPhi - 1) * (X-1) = 1`): substituting `(1-x)·b4L' = -1` along `sympPhi` gives
`(1-φ)·(b4L'∘φ) = -1`, so `b4L'∘φ = -(X-1)`, and `(b4L∘φ)' = (b4L'∘φ)·φ' = -(X-1)W² = -W = b4L'`,
so the sum is the constant `0` (`PowerSeries.derivative.ext`).
(2) `B2.subst sympY = 2·sympY - (X-φ)·b4L`: show the right side `g` is `φ`-invariant
(`sympY` is, and `(X-φ)·b4L` is because `b4L.subst sympPhi = -b4L` and `sympPhi - X = -(X - sympPhi)`),
so `g = δ.subst sympY` for `δ = sympDesc g`; show `g` satisfies the pullback
`Y(4-Y)g' = Y'[(2-Y)g + Y²]` of `B2`'s ODE (pure algebra with `L' = -(1-X)⁻¹`,
`1-ρ' = (2-Y)/(1-X)`, `Y(4-Y) = -(X-ρ)²`, `Y' = (X-ρ)/(X-1)`), deduce `Y(4-Y)δ' = (2-Y)δ + Y²`,
and identify `δ = B2` by the coefficient recurrence (`δ₀ = 0`, `2(2n-1)δₙ = (n-2)δₙ₋₁ + [n=2]`).
(3) `b4Theta = (X-φ)(b4Li2 - b4Li2.subst sympPhi)`; put `Ψ = b4Li2 - b4Li2.subst sympPhi`, so
`b4Theta = (X-φ)Ψ` and `X(X-1)Ψ' = b4L(2-X)` (from (1) and
`(b4Li2.subst sympPhi)' = (b4Li2'∘φ)·φ'`).  Substituting `b4Theta = (X-φ)Ψ`,
`b4Theta' = (1-φ')Ψ + (X-φ)Ψ'`, `B2.subst sympY = 2Y - (X-φ)L` from (2),
`Y(4-Y) = -(X-φ)²`, `Y' = (X-φ)/(X-1)`, `1-φ' = (2-Y)/(1-X)` and `(X-φ)(2-X) = X(4-Y)`,
the identity reduces to a rational-function identity, which closes by `ring`
(divide by the non-zero factors `X-φ` and `b4L` using that `ℚ⟦X⟧` is a domain). -/
theorem b4_theta_bridge :
    (((1 : PowerSeries ℚ) - PowerSeries.X) * PowerSeries.derivative (R := ℚ) Work.Pure.b4L = -1) ∧
    (PowerSeries.X * PowerSeries.derivative (R := ℚ) Work.Pure.b4Li2 = -Work.Pure.b4L) ∧
    (Work.Pure.b4L.subst Submission.CDT.sympPhi = -Work.Pure.b4L) ∧
    (Submission.CDTPlan.B2.subst Submission.CDT.sympY
        = 2 * Submission.CDT.sympY - (PowerSeries.X - Submission.CDT.sympPhi) * Work.Pure.b4L) ∧
    (Submission.CDT.sympY * (4 - Submission.CDT.sympY) * PowerSeries.derivative (R := ℚ) Work.Pure.b4Theta
        = (PowerSeries.derivative (R := ℚ) Submission.CDT.sympY)
          * ((2 - Submission.CDT.sympY) * Work.Pure.b4Theta
              + (4 - Submission.CDT.sympY) * (Submission.CDTPlan.B2.subst Submission.CDT.sympY)
              - 2 * Submission.CDT.sympY * (4 - Submission.CDT.sympY))) := by
  refine ⟨b4L_deriv, b4Li2_deriv, b4L_subst_sympPhi, b4_B2_subst_sympY, ?_⟩
  have hY4 : Submission.CDT.sympY * (4 - Submission.CDT.sympY)
      = -((PowerSeries.X - Submission.CDT.sympPhi) ^ 2) := by
    simpa [Submission.CDT.sympW] using sympY_mul_four_sub
  have hP1 : ((PowerSeries.X : PowerSeries ℚ) - 1)
      * (1 - (PowerSeries.derivative (R := ℚ)) Submission.CDT.sympPhi)
      = -(2 - Submission.CDT.sympY) := derivative_one_sub_sympPhi
  have hU : ((PowerSeries.X : PowerSeries ℚ) - 1) * b4Unit = 1 := mul_b4Unit
  have hP2 : ((PowerSeries.X : PowerSeries ℚ) - 1) * (PowerSeries.X - Submission.CDT.sympPhi)
      * (PowerSeries.derivative (R := ℚ)) b4Psi = (4 - Submission.CDT.sympY) * b4L := by
    simpa [Submission.CDT.sympW] using b4Psi_rel_two
  have hY' : (PowerSeries.derivative (R := ℚ)) Submission.CDT.sympY
      = (PowerSeries.X - Submission.CDT.sympPhi) * b4Unit := by
    simpa [Submission.CDT.sympW] using derivative_sympY
  have hΘ : (PowerSeries.derivative (R := ℚ)) b4Theta
      = (1 - (PowerSeries.derivative (R := ℚ)) Submission.CDT.sympPhi) * b4Psi
        + (PowerSeries.X - Submission.CDT.sympPhi) * (PowerSeries.derivative (R := ℚ)) b4Psi := by
    rw [b4Theta_eq, b4_deriv_mul, derivative_sympW,
        show Submission.CDT.sympW = (PowerSeries.X - Submission.CDT.sympPhi) from rfl]
    ring
  have hΘdef : b4Theta = (PowerSeries.X - Submission.CDT.sympPhi) * b4Psi := by
    rw [b4Theta_eq, show Submission.CDT.sympW = (PowerSeries.X - Submission.CDT.sympPhi) from rfl]
  refine mul_left_cancel₀ sub_one_ne_zero ?_
  rw [hΘ, hΘdef, b4_B2_subst_sympY, hY']
  linear_combination
    (-(((PowerSeries.X : PowerSeries ℚ) - 1)
        * (PowerSeries.X - Submission.CDT.sympPhi) ^ 2 * b4Unit * b4Psi)) * hP1
    + ((((PowerSeries.X : PowerSeries ℚ) - 1) * (PowerSeries.X - Submission.CDT.sympPhi) ^ 2
          * (1 - (PowerSeries.derivative (R := ℚ)) Submission.CDT.sympPhi) * b4Psi)
        + (PowerSeries.X - Submission.CDT.sympPhi) ^ 2 * (4 - Submission.CDT.sympY) * b4L)
      * hU
    + ((((PowerSeries.X : PowerSeries ℚ) - 1)
          * (1 - (PowerSeries.derivative (R := ℚ)) Submission.CDT.sympPhi) * b4Psi)
        + (4 - Submission.CDT.sympY) * b4L) * hY4
    + (Submission.CDT.sympY * (4 - Submission.CDT.sympY)) * hP2

end Work.Pure
