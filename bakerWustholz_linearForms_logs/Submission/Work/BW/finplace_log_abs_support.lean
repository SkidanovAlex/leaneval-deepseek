import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

/-- For a non-zero `x` in a number field `L`, the function sending a finite place `w` to
`log (w x)` has finite support: `w x = 1` for all but finitely many `w`, and `log 1 = 0`.
The absolute value has the same support since `|a| = 0 ↔ a = 0`. -/
theorem finplace_log_abs_support {L : Type*} [Field L] [NumberField L] {x : L} (hx : x ≠ 0) :
    Function.HasFiniteSupport (fun w : NumberField.FinitePlace L => Real.log (w x)) ∧
    Function.HasFiniteSupport (fun w : NumberField.FinitePlace L => |Real.log (w x)|) := by
  have hmul : (Function.mulSupport fun w : NumberField.FinitePlace L => w x).Finite :=
    NumberField.FinitePlace.hasFiniteMulSupport hx
  have hlog : (Function.support fun w : NumberField.FinitePlace L => Real.log (w x)).Finite :=
    hmul.subset (by
      intro w hw
      simp only [Function.mem_support, Function.mem_mulSupport] at hw ⊢
      intro h1
      exact hw (by rw [h1, Real.log_one]))
  refine ⟨hlog, ?_⟩
  have habs : (Function.support fun w : NumberField.FinitePlace L => |Real.log (w x)|)
      = (Function.support fun w : NumberField.FinitePlace L => Real.log (w x)) := by
    ext w
    simp only [Function.mem_support, ne_eq, abs_eq_zero]
  rw [Function.HasFiniteSupport, habs]
  exact hlog

end Work.BW
