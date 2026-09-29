import Mathlib
import Submission.Work.Pure.b4_defs
import Submission.Work.Pure.b4_B2_ode
import Submission.Work.Pure.b4_theta_defs
import Submission.Work.Pure.b4_rel

/-!
# The pullback of the pure function `B₂` along the symmetrization coordinate

Calegari--Dimitrov--Tang, arXiv:2408.15403, §`sec:lindep`, eq. `(diffformulas)`:

  `B₂(y(x)) = 2y - (x - φ)·log(1-x)`,   `y = x²/(x-1)`, `φ = x/(x-1)`.

Route.  Put `g := 2·sympY - sympW·b4L` with `sympW = x - φ`.

1. `g` is `φ`-invariant, so `g = δ.subst sympY` for `δ := sympDesc g`.
2. `g` satisfies the pullback of the ODE of `B₂`, `Y(4-Y)g' = Y'[(2-Y)g + Y²]`; the residual
   difference is `sympW²·b4L·[(1-φ') + b4Unit·(2-Y)]`, which vanishes because
   `(X-1)(1-φ') = -(2-Y)` and `(X-1)·b4Unit = 1`.
3. Differentiating `δ.subst sympY = g` gives `g' = (δ'.subst sympY)·Y'`, and `Y' ≠ 0`, so
   `Y(4-Y)·(δ'.subst sympY) = (2-Y)·g + Y²`.
4. Hence `E := X(4-X)δ' - (2-X)δ - X²` satisfies `E.subst sympY = 0`, so `E = 0` by injectivity of
   substitution by `sympY`.
5. `B₂` satisfies `X(4-X)B₂' = (2-X)B₂ + X²` (`b4_B2_ode`), and solutions of that ODE are unique
   (`req_of_same_ode`), so `δ = B₂`.
6. Therefore `B₂.subst sympY = δ.subst sympY = g`.
-/

namespace Work.Pure

open PowerSeries

noncomputable section

/-- the derivative of `sympW = x - φ` -/
lemma derivative_sympW :
    (PowerSeries.derivative (R := ℚ)) Submission.CDT.sympW
      = 1 - (PowerSeries.derivative (R := ℚ)) Submission.CDT.sympPhi := by
  rw [show Submission.CDT.sympW = (X : PowerSeries ℚ) - Submission.CDT.sympPhi from rfl,
      map_sub, PowerSeries.derivative_X]

/-- `w = x - φ` is anti-invariant under `φ` -/
lemma sympW_subst_sympPhi :
    PowerSeries.subst Submission.CDT.sympPhi Submission.CDT.sympW = -Submission.CDT.sympW := by
  have hφ := Submission.CDT.sympPhi_hasSubst
  rw [show Submission.CDT.sympW = (X : PowerSeries ℚ) - Submission.CDT.sympPhi from rfl,
      PowerSeries.subst_sub hφ, PowerSeries.subst_X hφ, Submission.CDT.symp_phi_involutive]
  ring

/-- `y' = sympW·b4Unit` is nonzero -/
lemma derivative_sympY_ne_zero : (PowerSeries.derivative (R := ℚ)) Submission.CDT.sympY ≠ 0 := by
  rw [derivative_sympY]
  exact mul_ne_zero sympW_ne_zero b4Unit_ne_zero

lemma subst_sympY_two : PowerSeries.subst Submission.CDT.sympY (2 : PowerSeries ℚ) = 2 := by
  rw [show (2 : PowerSeries ℚ) = PowerSeries.C 2 from rfl,
      Submission.CDT.C_subst_eq ℚ 2 Submission.CDT.sympY Submission.CDT.sympY_hasSubst]

lemma subst_sympY_four : PowerSeries.subst Submission.CDT.sympY (4 : PowerSeries ℚ) = 4 := by
  rw [show (4 : PowerSeries ℚ) = PowerSeries.C 4 from rfl,
      Submission.CDT.C_subst_eq ℚ 4 Submission.CDT.sympY Submission.CDT.sympY_hasSubst]

theorem b4_B2_subst_sympY :
    Submission.CDTPlan.B2.subst Submission.CDT.sympY
      = 2 * Submission.CDT.sympY - (PowerSeries.X - Submission.CDT.sympPhi) * Work.Pure.b4L := by
  show Submission.CDTPlan.B2.subst Submission.CDT.sympY
      = 2 * Submission.CDT.sympY - Submission.CDT.sympW * b4L
  have hφ := Submission.CDT.sympPhi_hasSubst
  have hY := Submission.CDT.sympY_hasSubst
  set g : PowerSeries ℚ := 2 * Submission.CDT.sympY - Submission.CDT.sympW * b4L with hgdef
  -- (1) `g` is `φ`-invariant
  have hgφ : PowerSeries.subst Submission.CDT.sympPhi g = g := by
    have h2 : PowerSeries.subst Submission.CDT.sympPhi (2 : PowerSeries ℚ) = 2 := by
      rw [show (2 : PowerSeries ℚ) = PowerSeries.C 2 from rfl,
          Submission.CDT.C_subst_eq ℚ 2 Submission.CDT.sympPhi hφ]
    rw [hgdef, PowerSeries.subst_sub hφ, PowerSeries.subst_mul hφ, PowerSeries.subst_mul hφ,
        h2, Submission.CDT.symp_y_invariant, sympW_subst_sympPhi, b4L_subst_sympPhi]
    ring
  -- (2) the pullback of `B₂`'s ODE, for `g`
  have hg' : (PowerSeries.derivative (R := ℚ)) g
      = 2 * (PowerSeries.derivative (R := ℚ)) Submission.CDT.sympY
        - ((1 - (PowerSeries.derivative (R := ℚ)) Submission.CDT.sympPhi) * b4L
            + Submission.CDT.sympW * b4Unit) := by
    have hD2 : (PowerSeries.derivative (R := ℚ)) (2 * Submission.CDT.sympY)
        = 2 * (PowerSeries.derivative (R := ℚ)) Submission.CDT.sympY := by
      rw [show (2 : PowerSeries ℚ) = PowerSeries.C 2 from rfl, Derivation.leibniz]
      simp
    have hDW : (PowerSeries.derivative (R := ℚ)) (Submission.CDT.sympW * b4L)
        = (1 - (PowerSeries.derivative (R := ℚ)) Submission.CDT.sympPhi) * b4L
          + Submission.CDT.sympW * b4Unit := by
      rw [b4_deriv_mul, derivative_sympW, deriv_b4L]
      ring
    rw [hgdef, map_sub, hD2, hDW]
  have hODE : Submission.CDT.sympY * (4 - Submission.CDT.sympY) * (PowerSeries.derivative (R := ℚ)) g
      = (PowerSeries.derivative (R := ℚ)) Submission.CDT.sympY
        * ((2 - Submission.CDT.sympY) * g + Submission.CDT.sympY ^ 2) := by
    rw [hg', hgdef, derivative_sympY]
    linear_combination
      (-(1 - (PowerSeries.derivative (R := ℚ)) Submission.CDT.sympPhi) * b4L) * sympY_mul_four_sub
      + (Submission.CDT.sympW ^ 2 * b4Unit * b4L) * derivative_one_sub_sympPhi
      - (Submission.CDT.sympW ^ 2 * b4L
          * (1 - (PowerSeries.derivative (R := ℚ)) Submission.CDT.sympPhi)) * mul_b4Unit
  -- (3) the analogous equation for `δ = sympDesc g`
  set δ : PowerSeries ℚ := Submission.CDT.sympDesc g with hδdef
  have hδsub : PowerSeries.subst Submission.CDT.sympY δ = g := by
    rw [hδdef]
    exact Submission.CDT.sympDesc_y_subst g hgφ
  have hchain : (PowerSeries.derivative (R := ℚ)) g
      = PowerSeries.subst Submission.CDT.sympY ((PowerSeries.derivative (R := ℚ)) δ)
          * (PowerSeries.derivative (R := ℚ)) Submission.CDT.sympY := by
    rw [← hδsub, PowerSeries.derivative_subst hY]
  have hODEδ : Submission.CDT.sympY * (4 - Submission.CDT.sympY)
      * PowerSeries.subst Submission.CDT.sympY ((PowerSeries.derivative (R := ℚ)) δ)
      = (2 - Submission.CDT.sympY) * g + Submission.CDT.sympY ^ 2 := by
    refine mul_right_cancel₀ derivative_sympY_ne_zero ?_
    rw [show (Submission.CDT.sympY * (4 - Submission.CDT.sympY)
            * PowerSeries.subst Submission.CDT.sympY ((PowerSeries.derivative (R := ℚ)) δ))
            * (PowerSeries.derivative (R := ℚ)) Submission.CDT.sympY
          = (Submission.CDT.sympY * (4 - Submission.CDT.sympY))
            * (PowerSeries.subst Submission.CDT.sympY ((PowerSeries.derivative (R := ℚ)) δ)
              * (PowerSeries.derivative (R := ℚ)) Submission.CDT.sympY) by ring]
    rw [← hchain, hODE]
    ring
  -- (4) the series `E` vanishes after substitution by `y`
  have hE : PowerSeries.subst Submission.CDT.sympY
      (PowerSeries.X * (4 - PowerSeries.X) * (PowerSeries.derivative (R := ℚ)) δ
        - (2 - PowerSeries.X) * δ - PowerSeries.X ^ 2) = 0 := by
    have h1 : PowerSeries.subst Submission.CDT.sympY
        (PowerSeries.X * (4 - PowerSeries.X) * (PowerSeries.derivative (R := ℚ)) δ)
        = Submission.CDT.sympY * (4 - Submission.CDT.sympY)
          * PowerSeries.subst Submission.CDT.sympY ((PowerSeries.derivative (R := ℚ)) δ) := by
      rw [PowerSeries.subst_mul hY, PowerSeries.subst_mul hY, PowerSeries.subst_sub hY,
          PowerSeries.subst_X hY, subst_sympY_four]
    have h2 : PowerSeries.subst Submission.CDT.sympY ((2 - PowerSeries.X) * δ)
        = (2 - Submission.CDT.sympY) * g := by
      rw [PowerSeries.subst_mul hY, PowerSeries.subst_sub hY, PowerSeries.subst_X hY,
          subst_sympY_two, hδsub]
    have h3 : PowerSeries.subst Submission.CDT.sympY ((PowerSeries.X : PowerSeries ℚ) ^ 2)
        = Submission.CDT.sympY ^ 2 := by
      rw [PowerSeries.subst_pow hY, PowerSeries.subst_X hY]
    rw [PowerSeries.subst_sub hY, PowerSeries.subst_sub hY, h1, h2, h3]
    linear_combination hODEδ
  -- (5) `δ` satisfies the ODE of `B₂`
  have hδODE : PowerSeries.X * (4 - PowerSeries.X) * (PowerSeries.derivative (R := ℚ)) δ
      = (2 - PowerSeries.X) * δ + PowerSeries.X ^ 2 := by
    have h := Submission.CDT.symp_subst_y_injective _ hE
    linear_combination h
  have hδB2 : δ = Submission.CDTPlan.B2 := req_of_same_ode hδODE b4_B2_ode
  -- (6) conclude
  rw [← hδB2, hδsub, hgdef]

end

end Work.Pure
