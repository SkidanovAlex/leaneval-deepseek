import Mathlib
import Submission.Work.Landing.Core
import Submission.Work.ELRig.deriv_iterate_ne_zero_of_notMem_orbit

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.TripodCert

/-- The chain rule for the third iterate of `Tsq c`: the derivative of `(Tsq c)^[3]` is the
product of the derivatives of `Tsq c` at the three points of the orbit. -/
theorem deriv_tsq_three (c z : ℂ) :
    deriv ((Work.Landing.Tsq c)^[3]) z
      = deriv (Work.Landing.Tsq c) ((Work.Landing.Tsq c)^[2] z)
        * deriv (Work.Landing.Tsq c) ((Work.Landing.Tsq c) z)
        * deriv (Work.Landing.Tsq c) z := by
  have hf : Differentiable ℂ (Work.Landing.Tsq c) := by
    show Differentiable ℂ (fun z : ℂ => (z ^ 2 + star c) ^ 2 + c)
    fun_prop
  have h1 : ((Work.Landing.Tsq c)^[3]) = (Work.Landing.Tsq c) ∘ ((Work.Landing.Tsq c)^[2]) := by
    rw [show (3 : ℕ) = 2 + 1 from rfl, Function.iterate_succ']
  have h2 : ((Work.Landing.Tsq c)^[2]) = (Work.Landing.Tsq c) ∘ (Work.Landing.Tsq c) := by
    rw [show (2 : ℕ) = 1 + 1 from rfl, Function.iterate_succ', Function.iterate_one]
  rw [h1, deriv_comp z hf.differentiableAt ((hf.iterate 2).differentiableAt), h2,
    deriv_comp z hf.differentiableAt hf.differentiableAt]
  ring

end Work.TripodCert
