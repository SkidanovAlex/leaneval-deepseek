import Mathlib
import Submission.Work.Whitney.TCMDefs
import Submission.Work.Whitney.tcmModelMul
import Submission.Work.Whitney.tcmSuccOneAux

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false

/-!
# The inverse coordinate identification: general pair conditions

`Submission/Work/Whitney/tcmSuccOneAux.lean` proves the pair conditions of the inverse coordinate
identification `Work.Whitney.Fib.tcmF_inv` only in the case `q = 1` (the case needed for the
`succ-one` form of the model product formula).  This module records the *general* `q` versions,
which are needed by the general induction: the sphere bundle of rank `p + q` is carried into
`A ∪ C`, and so is the punctured set.

The proofs are the `q = 1` arguments verbatim (both use `tcmA_union_tcmC` and the fact that the
fibre coordinates of a point of `Sph` are non-zero).
-/

namespace Work.Whitney

open Work.Thom

noncomputable section

variable {Y : Type} [TopologicalSpace Y]

/-- **The pair condition of the inverse identification, general `q`**: every point of the sphere
bundle of rank `p + q` lies in `A ∪ C` after applying `Work.Whitney.Fib.tcmF_inv`. -/
theorem tcmF_inv_mem' (p q : ℕ) :
    ∀ x ∈ Sph Y (p + q), Fib.tcmF_inv Y p q x ∈ tcmA Y p q ∪ tcmC Y p q := by
  intro x hx
  rw [tcmA_union_tcmC]
  simp only [Set.mem_ofPred_eq, Fib.tcmF_inv_apply]
  intro h0
  have h1 : x.2 = 0 := by
    have h2 := congrArg (tcmSumLin p q) h0
    simpa only [ContinuousLinearEquiv.apply_symm_apply, map_zero] using h2
  have h3 : ‖x.2‖ = 1 := hx
  rw [h1, norm_zero] at h3
  exact one_ne_zero h3.symm

/-- **The pair condition of the inverse identification on the punctured part, general `q`**:
`Punct` is carried into `A ∪ C` by `Work.Whitney.Fib.tcmF_inv`. -/
theorem tcmF_inv_mem_punct' (p q : ℕ) :
    ∀ x ∈ Punct Y (p + q), Fib.tcmF_inv Y p q x ∈ tcmA Y p q ∪ tcmC Y p q := by
  intro x hx
  rw [tcmA_union_tcmC]
  simp only [Set.mem_ofPred_eq, Fib.tcmF_inv_apply]
  intro h0
  exact hx (by
    have h2 := congrArg (tcmSumLin p q) h0
    simpa only [ContinuousLinearEquiv.apply_symm_apply, map_zero] using h2)

end

end Work.Whitney
