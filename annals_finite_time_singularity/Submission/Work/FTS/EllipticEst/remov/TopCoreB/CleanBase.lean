import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS.H2.T2Qaux.SupAux
import Submission.Work.Spaces.dthU_Gam
import Submission.Work.Spaces.sq_mul_div_rpow

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `TopCoreB/CleanBase`: the reverse expansions, on a poison-free import cone

The declarations `reverse_expansion_2d` / `reverse_expansion_top` of
`Submission.Work.FTS.EllipticEst.remov.PsiSlotBounds` are the pointwise input of the slot
recursions, but their module (and hence everything importing it) sits downstream of
`remov/DthIter_expansion`, whose import cone reaches the `EllHyp`-certificate cluster
(`Cert/*`, `ellHyp_L2Mem_*`, `RPFresh/excess_finite`), which currently does not compile.

The coefficient machinery is available *cleanly* in the fresh namespace `...remov.selfdth` of
`remov/high_chain_sum_self.lean` (`selfdth.DthIter_expansion_local`,
`selfdth.DthCoef_sin_pow_bound`, `selfdth.dthCoef_self`), so the two reverse expansions are
re-produced here verbatim in terms of it.

Also re-exported here: `HkMem_Dz_shift`, which the `A`-half copy
(`TopCoreB/ATopClean.lean`) consumes, taken from the clean provider
`Work.FTS.EllipticEst.AeMom.Repair.HkMem_Dz_shift`.
-/

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.remov.TopCoreB

set_option autoImplicit false
set_option linter.unusedSimpArgs false


/-- `∂_θ^{m+n} f = ∂_θ^m (∂_θ^n f)`. -/
theorem pthIter_addT (m n : ℕ) (f : ℝ → ℝ → ℝ) :
    Work.Spaces.pthIter (m + n) f = Work.Spaces.pthIter m (Work.Spaces.pthIter n f) := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [Nat.succ_add, Work.Spaces.pthIter_succ, ih, Work.Spaces.pthIter_succ]





end Work.FTS.EllipticEst.remov.TopCoreB

namespace Work.FTS.EllipticEst.remov

set_option autoImplicit false

/-- **Membership form of the `D_z`-shift** (clean provider): if `f` is `C^∞` on the open
quadrant and in `ℋ^k` (`k ≥ 1`), then `D_z f ∈ ℋ^{k-1}`. -/
theorem HkMem_Dz_shift {α : ℝ} {k : ℕ} (hk : 1 ≤ k) {f : ℝ → ℝ → ℝ}
    (hf : Work.FTS.EllipticEst.SmoothOpen f) (hmem : Work.Spaces.HkMem α k f) :
    Work.Spaces.HkMem α (k - 1) (Work.Spaces.Dz f) :=
  Work.FTS.EllipticEst.AeMom.Repair.HkMem_Dz_shift hk hf hmem

end Work.FTS.EllipticEst.remov
