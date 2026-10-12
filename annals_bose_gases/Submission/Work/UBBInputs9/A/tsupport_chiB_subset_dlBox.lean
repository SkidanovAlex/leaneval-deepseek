import Mathlib.Analysis.InnerProductSpace.PiL2
import Submission.Work.UBBInputs9.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.UBBInputs9.A

/-- **The topological support of the sliding cutoff lies in the small box `B(u)`.**

`χ_B = chiB ℓ d u` is the product `χ(x/ℓ)·χ(x/(ℓd) − u)`; if it is nonzero then
both factors are nonzero, so `x ∈ dlBox ℓ d u` (`chiB_support_mem`). Hence the
support of `chiB ℓ d u` is contained in `dlBox ℓ d u`, and so is its closure
because `dlBox ℓ d u` is closed (an intersection of the closed cube `acube ℓ`
with the preimage of the closed cube `acube (ℓd)` under the continuous
translation `x ↦ x − (ℓd)•u`). -/
theorem tsupport_chiB_subset_dlBox {ℓ d : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d)
    (u : EuclideanSpace ℝ (Fin 3)) :
    tsupport (Submission.BoseGases.chiB ℓ d u) ⊆ Submission.BoseGases.dlBox ℓ d u := by
  refine closure_minimal (fun x hx => ?_) ?_
  · rw [Function.mem_support] at hx
    exact Submission.BoseGases.chiB_support_mem hℓ hd u x hx
  · unfold Submission.BoseGases.dlBox
    exact (Submission.BoseGases.acube_isClosed ℓ).inter
      ((Submission.BoseGases.acube_isClosed (ℓ * d)).preimage (by fun_prop))

end Work.UBBInputs9.A
