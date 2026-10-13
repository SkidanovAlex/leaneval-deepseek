import Mathlib.Basic.Real.Basic
import Mathlib.Order.Filter.Defs
import Submission.Work.Spaces.Defs
import Submission.Work.Elliptic.Defs
import Submission.Work.Spaces.HkSq_terms
import Submission.Work.FTS.EllipticEst.H2W.Norms
import Submission.Work.FTS.EllipticEst.TT.WeakDefs
import Submission.Work.FTS.EllipticEst.TT.bslOp_DzIter_eq
import Submission.Work.FTS.EllipticEst.TT.SliceDatum
import Submission.Work.FTS.EllipticEst.OpenQDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.H2W

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false

/-! ## Monotonicity of the level-`0` quantity in the level

The two ingredients of the final assembly that need no analysis:

* the level-`0` `ℋ`-square of the radially differentiated source `D_z^jF` (`j ≤ 2`) is one of
  the summands of the level-`2` `ℋ`-square of `F`, so it is bounded by it as soon as that
  integral is honest (`HkMem α 2 F`, which the weak class `EllWeakPos α 2` provides);
* the level-`0` `ℋ`-square of `g` is the `L²`-square of `g · w / sin(2θ)^{η/2}`
  (`NSq_eq_HkSq` of `H2W/Norms`). -/

/-- `HkSq α 0 (DzIter j F) ≤ HkSq α 2 F` for `j ≤ 2`, given the honesty of the level-`2`
integral of `F`: the level-`0` integrand of `D_z^j F` is one summand of the level-`2` integrand
of `F`, and the outer integral of the latter is honest. -/
theorem HkSq_zero_DzIter_le_HkSq (α : ℝ) (F : ℝ → ℝ → ℝ) (hF : Work.Spaces.HkMem α 2 F)
    (j : ℕ) (hj : j ≤ 2) :
    Work.Spaces.HkSq α 0 (Work.Spaces.DzIter j F) ≤ Work.Spaces.HkSq α 2 F := by
  rw [NSq_eq_HkSq]
  exact Work.Spaces.L2Sq_DzIter_le_HkSq α 2 F hF j hj

end Work.FTS.EllipticEst.H2W
