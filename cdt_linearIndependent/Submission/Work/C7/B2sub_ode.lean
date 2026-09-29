import Mathlib
import Submission.Work.C7.gsetup
import Submission.Work.Pure.b4_B2_ode
import Submission.Work.Pure.pure_facts

namespace Work.C7

/-! The pullback of the `B₂`-ODE to the `x`-variable: substituting `y = Work.C7.yps = x²/(x−1)`
in `X(4−X)·B₂' = (2−X)·B₂ + X²` (proved twice: `Work.Pure.b4_B2_ode`, and in scaled form
`Work.Pure.relation_B2 : 2X(4−X)B₂' = 2X² + (4−2X)B₂`, both axiom-clean) gives this identity.

Route: apply `PowerSeries.substAlgHom Work.C7.yps` (or `PowerSeries.subst`) to the proved ODE
(`map_mul`, `map_sub`, `map_add`, `map_ofNat`, `PowerSeries.substAlgHom_X` /
`PowerSeries.coe_substAlgHom`) to get `y(4−y)·(B₂' ∘ y) = (2−y)·(B₂∘y) + y²`, rewrite
`(B₂∘y)'` by `PowerSeries.derivative_subst Submission.CDT.sympY_hasSubst` as
`(B₂' ∘ y)·y'`, and use `Work.C7.X_mul_two_sub_mul_deriv_yps : x(2−x)·y' = y(4−y)` from
`Submission.Work.C7.gsetup` (the rearrangement uses commutativity). -/

/-- The pullback of the `B₂`-ODE along `y`: `y(4−y)·(B₂'∘y) = (2−y)·(B₂∘y) + y²`. -/
lemma B2sub_pullback :
    Work.C7.yps * (4 - Work.C7.yps)
      * (PowerSeries.derivative (R := ℚ) Submission.CDTPlan.B2).subst Work.C7.yps
      = (2 - Work.C7.yps) * (Submission.CDTPlan.B2.subst Work.C7.yps) + Work.C7.yps ^ 2 := by
  have hy : PowerSeries.HasSubst (Work.C7.yps) := Submission.CDT.sympY_hasSubst
  have h := congrArg (fun f : PowerSeries ℚ => f.subst Work.C7.yps) Work.Pure.b4_B2_ode
  simp only [show (2 : PowerSeries ℚ) = PowerSeries.C (2 : ℚ) from rfl,
    show (4 : PowerSeries ℚ) = PowerSeries.C (4 : ℚ) from rfl,
    PowerSeries.subst_mul hy, PowerSeries.subst_sub hy, PowerSeries.subst_add hy,
    PowerSeries.subst_pow hy, PowerSeries.subst_X hy, PowerSeries.subst_C] at h
  exact h

theorem B2sub_ode :
    PowerSeries.X * (2 - PowerSeries.X)
      * PowerSeries.derivative (R := ℚ) (Submission.CDTPlan.B2.subst Work.C7.yps)
      = (2 - Work.C7.yps) * (Submission.CDTPlan.B2.subst Work.C7.yps) + Work.C7.yps ^ 2 := by
  have hy : PowerSeries.HasSubst (Work.C7.yps) := Submission.CDT.sympY_hasSubst
  rw [PowerSeries.derivative_subst hy]
  rw [show PowerSeries.X * (2 - PowerSeries.X)
        * ((PowerSeries.derivative (R := ℚ) Submission.CDTPlan.B2).subst Work.C7.yps
            * PowerSeries.derivative (R := ℚ) Work.C7.yps)
      = PowerSeries.X * (2 - PowerSeries.X) * PowerSeries.derivative (R := ℚ) Work.C7.yps
        * (PowerSeries.derivative (R := ℚ) Submission.CDTPlan.B2).subst Work.C7.yps by ring]
  rw [Work.C7.X_mul_two_sub_mul_deriv_yps]
  exact B2sub_pullback

end Work.C7
