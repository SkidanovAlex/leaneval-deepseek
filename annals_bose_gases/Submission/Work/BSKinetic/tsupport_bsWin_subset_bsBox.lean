import Mathlib.Analysis.InnerProductSpace.PiL2
import Submission.Work.BSKinetic.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BSKinetic

open Submission.BoseGases

/-- **The topological support of the moving window lies in the moving box.**

`bsWin ℓ u x = chiScale ℓ (x − ℓ•u)`, so if it is nonzero then `x − ℓ•u` lies in the
support of the scaled bump `chiScale ℓ`, whence `‖x − ℓ•u‖ ≤ ℓ/2` and therefore
`x − ℓ•u ∈ acube ℓ`, i.e. `x ∈ bsBox ℓ u`.  The support of `bsWin ℓ u` is thus contained
in `bsBox ℓ u`, and so is its closure because `bsBox ℓ u` is closed (the preimage of the
closed cube `acube ℓ` under the continuous translation `x ↦ x − ℓ•u`). -/
theorem tsupport_bsWin_subset_bsBox {ℓ : ℝ} (hℓ : 0 < ℓ)
    (u : EuclideanSpace ℝ (Fin 3)) :
    tsupport (Work.BSKinetic.bsWin ℓ u) ⊆ Work.BSKinetic.bsBox ℓ u := by
  refine closure_minimal (fun x hx => ?_) ?_
  · rw [Function.mem_support] at hx
    show x - ℓ • u ∈ acube ℓ
    exact mem_acube_of_norm_le (le_of_lt hℓ) (chiScale_support_le hℓ hx)
  · show IsClosed (bsBox ℓ u)
    rw [bsBox]
    exact (acube_isClosed ℓ).preimage (by fun_prop)

end Work.BSKinetic
