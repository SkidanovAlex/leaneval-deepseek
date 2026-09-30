import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW.LiouvilleAux

/-- For `x ≠ 0` the function `v ↦ log⁺ |x|_v` on the finite places of a number field has
finite support: `log⁺ ‖x‖_v = 0` whenever `‖x‖_v = 1`, and this happens for all but
finitely many finite places by the finiteness of the multiplicative support. -/
theorem posLog_hasFiniteSupport {K : Type*} [Field K] [NumberField K] (x : K) (hx : x ≠ 0) :
    Function.HasFiniteSupport (fun v : NumberField.FinitePlace K => Real.posLog (v x)) := by
  refine (NumberField.FinitePlace.hasFiniteMulSupport hx).subset ?_
  intro v hv
  rw [Function.mulSupport, Set.mem_ofPred_eq]
  intro h
  rw [Function.support, Set.mem_ofPred_eq] at hv
  exact hv (by rw [h, Real.posLog, Real.log_one, max_self])

end Work.BW.LiouvilleAux
