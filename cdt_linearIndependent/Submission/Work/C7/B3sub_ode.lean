import Mathlib
import Submission.Work.C7.gsetup
import Submission.Work.Pure.pure_facts

namespace Work.C7

/-! The pullback of the `B₃`-ODE to the `x`-variable (hypothesis-free version of the earlier
request: the `y`-ODE is now imported rather than assumed). With
`Work.Pure.relation_B3 : 2X(4−X)·B₃' = 4X − 2B₂` (proved, axiom-clean, in
`Submission.Work.Pure.pure_facts`), substituting `y = Work.C7.yps = x²/(x−1)` gives
`x(2−x)·(B₃∘y)' = 2y − B₂∘y`.

Route: apply `PowerSeries.substAlgHom Work.C7.yps` (or `PowerSeries.subst`) to
`Work.Pure.relation_B3` (`map_mul`, `map_sub`, `map_add`, `map_ofNat`,
`PowerSeries.substAlgHom_X` / `PowerSeries.coe_substAlgHom`), rewrite `(B₃∘y)'` by
`PowerSeries.derivative_subst Submission.CDT.sympY_hasSubst` as `(B₃' ∘ y)·y'`, and use
`Work.C7.X_mul_two_sub_mul_deriv_yps : x(2−x)·y' = y(4−y)` from `Submission.Work.C7.gsetup`
(the factor `2` is carried along throughout). -/
theorem B3sub_ode :
    PowerSeries.X * (2 - PowerSeries.X)
      * PowerSeries.derivative (R := ℚ) (Submission.CDTPlan.B3.subst Work.C7.yps)
      = 2 * Work.C7.yps - Submission.CDTPlan.B2.subst Work.C7.yps := by
  -- `y = sympY` may be substituted into power series (zero constant term).
  have hY : PowerSeries.HasSubst Work.C7.yps := Submission.CDT.sympY_hasSubst
  -- push the `y`-ODE `2X(4−X)·B₃' = 4X − 2B₂` through the substitution `X ↦ y`.
  have hsub := congrArg (PowerSeries.substAlgHom (R := ℚ) hY) Work.Pure.relation_B3
  simp only [map_mul, map_sub, map_ofNat, PowerSeries.substAlgHom_X,
    PowerSeries.coe_substAlgHom] at hsub
  -- chain rule for formal substitution: `(B₃∘y)' = (B₃'∘y)·y'`.
  have hchain := PowerSeries.derivative_subst (f := Submission.CDTPlan.B3) (g := Work.C7.yps) hY
  rw [hchain]
  set S := PowerSeries.subst Work.C7.yps ((PowerSeries.derivative (R := ℚ)) Submission.CDTPlan.B3)
    with hSdef
  -- the pulled-back ODE, in terms of the newly introduced `S = B₃'∘y`.
  have hmain : Work.C7.yps * (4 - Work.C7.yps) * S
      = 2 * Work.C7.yps - Submission.CDTPlan.B2.subst Work.C7.yps := by
    apply mul_left_cancel₀ (show (2 : PowerSeries ℚ) ≠ 0 by
      intro h
      have hc := congrArg (PowerSeries.coeff 0) h
      rw [show (2 : PowerSeries ℚ) = PowerSeries.C 2 from rfl, PowerSeries.coeff_C] at hc
      simp at hc)
    linear_combination hsub
  -- `x(2−x)·y' = y(4−y)` converts the `y`-form into the `x`-form.
  have hX := Work.C7.X_mul_two_sub_mul_deriv_yps
  linear_combination S * hX + hmain

end Work.C7
