import Mathlib
import Submission.Work.C7.gsetup
import Submission.Work.Pure.b4_rel
import Submission.Work.Pure.pure_facts

namespace Work.C7

/-! The pullback of the `B₄`-ODE to the `x`-variable: substituting `y = Work.C7.yps = x²/(x−1)`
in `X(4−X)·B₄' = (2−X)·B₄ + (4−X)·B₂ − 2X(4−X)` (proved as `Work.Pure.b4_rel`, and in scaled
form as `Work.Pure.relation_B4`) gives
`x(2−x)·(B₄∘y)' = (2−y)·(B₄∘y) + (4−y)·(B₂∘y) − 2y(4−y)`.

Route: apply `PowerSeries.substAlgHom Work.C7.yps` (or `PowerSeries.subst`) to the proved ODE
(`map_mul`, `map_sub`, `map_add`, numeral lemmas, `PowerSeries.substAlgHom_X` /
`PowerSeries.coe_substAlgHom`), rewrite `(B₄∘y)'` by
`PowerSeries.derivative_subst Submission.CDT.sympY_hasSubst` as `(B₄' ∘ y)·y'`, and use
`Work.C7.X_mul_two_sub_mul_deriv_yps : x(2−x)·y' = y(4−y)` from `Submission.Work.C7.gsetup`. -/
theorem B4sub_ode :
    PowerSeries.X * (2 - PowerSeries.X)
      * PowerSeries.derivative (R := ℚ) (Submission.CDTPlan.B4.subst Work.C7.yps)
      = (2 - Work.C7.yps) * (Submission.CDTPlan.B4.subst Work.C7.yps)
        + (4 - Work.C7.yps) * (Submission.CDTPlan.B2.subst Work.C7.yps)
        - 2 * Work.C7.yps * (4 - Work.C7.yps) := by
  have hy : PowerSeries.HasSubst Work.C7.yps := Work.C7.subst_yps_hasSubst
  -- Substitute `X ↦ yps` in the `y`-side ODE `Work.Pure.b4_rel`.
  have key : Work.C7.yps * (4 - Work.C7.yps)
        * PowerSeries.subst Work.C7.yps ((PowerSeries.derivative (R := ℚ)) Submission.CDTPlan.B4)
      = (2 - Work.C7.yps) * PowerSeries.subst Work.C7.yps Submission.CDTPlan.B4
        + (4 - Work.C7.yps) * PowerSeries.subst Work.C7.yps Submission.CDTPlan.B2
        - 2 * Work.C7.yps * (4 - Work.C7.yps) := by
    have h := congrArg (PowerSeries.substAlgHom (R := ℚ) (τ := Unit) (S := ℚ) hy)
      Work.Pure.b4_rel
    simp only [map_mul, map_sub, map_add, map_ofNat, PowerSeries.substAlgHom_X] at h
    simpa only [PowerSeries.coe_substAlgHom] using h
  -- Chain rule: `(B₄ ∘ y)' = (B₄' ∘ y) * y'`.
  have hd : PowerSeries.derivative (R := ℚ) (PowerSeries.subst Work.C7.yps Submission.CDTPlan.B4)
      = PowerSeries.subst Work.C7.yps ((PowerSeries.derivative (R := ℚ)) Submission.CDTPlan.B4)
        * PowerSeries.derivative (R := ℚ) Work.C7.yps := PowerSeries.derivative_subst hy
  rw [hd]
  -- `x(2−x)·y' = y(4−y)` converts the chain-rule factor into the substituted ODE.
  linear_combination
    PowerSeries.subst Work.C7.yps ((PowerSeries.derivative (R := ℚ)) Submission.CDTPlan.B4)
      * Work.C7.X_mul_two_sub_mul_deriv_yps + key

end Work.C7
