import Mathlib
import Submission.Work.Smooth.JordanSeparation.Separation

/-!
# The Jordan separation theorem for a simple immersed closed plane curve: packaged statements

This is the entry point of the chapter.  Everything is stated for a `C¹` `2π`-periodic curve
`c : ℝ → ℂ` which is an **immersion** (`∀ t, deriv c.γ t ≠ 0`) and **simple**
(`c.toPlaneCurve.IsSimple`, i.e. injective on one period `[0, 2π)`).

## Main results

* `jordanSeparation` — `Nonempty (PlaneSeparation c.toPlaneCurve)`: the complement of the trace is
  the disjoint union of two non-empty preconnected open sets, the bounded side `V` and the
  unbounded side `U`.  This is `Work.Smooth.Jordan.JordanInput c.toPlaneCurve`.
* `PlaneJordanSeparation c` — the same together with the values of the index on the two sides:
  `ind c x = 0` for `x ∈ U` and `|ind c x| = 1` for `x ∈ V`;
* `jordanInputSmooth` — the two above combined, in the form of the hypothesis `JordanInput` of the
  sibling chapter `Submission/Work/Smooth/Jordan`;
* `planeJordanSchoenflies_of_schoenflies` — the full classical input `PlaneJordanSchoenflies c` of
  the sibling chapter, obtained from the present chapter together with the *only* remaining
  classical input, the spanning disc of `PlaneSchoenflies` (the Schoenflies theorem).
-/

open Set
open Work.Smooth.Jordan

namespace Work.Smooth.JordanSeparation

noncomputable section

/-- **The plane input of the Jordan theory, with the values of the index on the two sides.**

This is `Work.Smooth.Jordan.PlaneJordanSchoenflies` without the Schoenflies part: a Jordan
separation of `c`, the index vanishing on the unbounded side and having modulus `1` on the bounded
side.  Everything except the spanning disc of the Schoenflies theorem. -/
structure PlaneJordanSeparation (c : SmoothPlaneCurve) where
  /-- Jordan separation of the curve -/
  sep : PlaneSeparation c.toPlaneCurve
  /-- the index vanishes on the unbounded side -/
  ind_eq_zero_U : ∀ x : ℂ, x ∈ sep.U → ind c x = 0
  /-- the index has modulus `1` on the bounded side -/
  ind_abs_eq_one_V : ∀ x : ℂ, x ∈ sep.V → |ind c x| = 1

/-- **Jordan separation with the index values.**  For a `C¹` immersed simple closed plane curve,
the plane separates into two sides and the index of the curve is `0` on the unbounded side and
`±1` on the bounded side. -/
theorem nonempty_planeJordanSeparation (c : SmoothPlaneCurve) (himm : c.IsImmersion)
    (hs : c.toPlaneCurve.IsSimple) : Nonempty (PlaneJordanSeparation c) := by
  obtain ⟨S⟩ := jordanSeparation c himm hs
  exact ⟨{ sep := S
           ind_eq_zero_U := fun x hx => ind_eq_zero_of_mem_U c himm hs hx
           ind_abs_eq_one_V := fun x hx => ind_abs_eq_one_of_mem_V c himm hs hx }⟩

/-- **The full classical plane input of the sibling chapter `Work.Smooth.Jordan`.**

`Work.Smooth.Jordan.PlaneJordanSchoenflies c` is a `PlaneSeparation` with the index values *and* an
embedded disc spanning the curve whose image is the closure of the bounded side.  The first three
clauses are proved in this chapter for every `C¹` immersed simple closed curve; only the spanning
disc (the Schoenflies theorem) is taken as an input. -/
def planeJordanSchoenflies_of_schoenflies (c : SmoothPlaneCurve) (himm : c.IsImmersion)
    (hs : c.toPlaneCurve.IsSimple) (hS : PlaneSchoenflies c.toPlaneCurve) :
    PlaneJordanSchoenflies c :=
  { sep := hS.toPlaneSeparation
    ind_eq_zero_U := fun x hx => ind_eq_zero_of_mem_U c himm hs hx
    ind_abs_eq_one_V := fun x hx => ind_abs_eq_one_of_mem_V c himm hs hx
    e := hS.e
    inj := hS.inj
    boundary := hS.boundary
    range_e := hS.range_e }

/-- **Jordan separation in the exact shape of `Work.Smooth.Jordan.JordanInput`.**

For a `C¹` `2π`-periodic plane curve `c : ℝ → ℂ` which is an immersion and is injective on one
period, the complement of its trace is the disjoint union of two non-empty preconnected open sets,
the unbounded side `U` and the bounded side `V`.  This is `PlaneSeparation c` itself, without going
through the `SmoothPlaneCurve` wrapper. -/
theorem planeSeparation_of_contDiff (c : PlaneCurve) (hc : ContDiff ℝ 1 c.γ)
    (himm : ∀ t : ℝ, deriv c.γ t ≠ 0) (hs : c.IsSimple) : Nonempty (PlaneSeparation c) := by
  let c' : SmoothPlaneCurve := { c with contDiff := hc }
  have himm' : c'.IsImmersion := himm
  have hs' : c'.toPlaneCurve.IsSimple := hs
  simpa using jordanSeparation c' himm' hs'

/-- **`JordanInput` for a `C¹` immersed simple closed plane curve.** -/
theorem jordanInput_of_smooth (c : SmoothPlaneCurve) (himm : c.IsImmersion)
    (hs : c.toPlaneCurve.IsSimple) : JordanInput c.toPlaneCurve :=
  fun _ => jordanSeparation c himm hs

/-- **The class of curves covered by this chapter**: `C¹` `2π`-periodic curves which are
immersions and are injective on one period. -/
def SmoothImmersionInput : Prop :=
  ∀ c : SmoothPlaneCurve, c.IsImmersion → c.toPlaneCurve.IsSimple →
    Nonempty (PlaneSeparation c.toPlaneCurve)

/-- **`SmoothImmersionInput` holds.**  This is the Jordan curve theorem for `C¹` immersed simple
closed plane curves. -/
theorem smoothImmersionInput : SmoothImmersionInput :=
  fun c himm hs => jordanSeparation c himm hs

end

end Work.Smooth.JordanSeparation
