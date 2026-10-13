import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.NormNum.Ineq
import Submission.Work.FTS.ClassC.A1
import Submission.Work.FTS.OpenPkg.Basic
import Submission.Work.FTS.StrongEps.EComparison.Reduction

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS_RegExport.RXR1

/-- The pointwise/Pi identification of the difference of two profiles. -/
theorem sub_apply' (f g : Work.FTS.Galerkin.Fn) :
    (f - g) = fun z θ => f z θ - g z θ := by
  funext z θ; rfl

/-- `ClassC α` is closed under subtraction, in the ambient (Pi-)difference form. -/
theorem classC_sub' {α : ℝ} {f g : Work.FTS.Galerkin.Fn}
    (hf : Work.FTS.ClassC.ClassC α f) (hg : Work.FTS.ClassC.ClassC α g) :
    Work.FTS.ClassC.ClassC α (f - g) := by
  rw [sub_apply' f g]
  exact Work.FTS.StrongEps.EComparison.classC_sub hf hg

/-- **The regularity hypotheses of the class descend to the difference.**  If `f` and `g` are both
in `ClassC α` (which is a subspace: `ClassC.classC_add` / `ClassC.classC_smul` / `EComparison.classC_sub`),
then `f - g` is `C^∞` on the open quadrant, honestly in `ℋ⁴`, and it satisfies the
integration-by-parts boundary traces up to order `4`.  The order is lowered from the class's
`ℋ⁷`/`ℋ⁸` and `BdryTraces … 6`/`… 7` because that is all the `ℋ⁴` estimates consume. -/
theorem classC_sub_hyp {α : ℝ} {f g : Work.FTS.Galerkin.Fn}
    (hf : Work.FTS.ClassC.ClassC α f) (hg : Work.FTS.ClassC.ClassC α g) :
    Work.FTS.EllipticEst.SmoothOpen (f - g) ∧ Work.Spaces.HkMem α 4 (f - g) ∧
      Work.FTS.Nonlin.BdryTraces α 4 (f - g) :=
  let hsub := classC_sub' hf hg
  ⟨hsub.reg, Work.FTS.ClassC.classC_hkMem_four hsub, hsub.bdry_le_six (by norm_num)⟩

end Work.FTS_RegExport.RXR1
