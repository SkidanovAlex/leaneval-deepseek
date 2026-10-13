import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Ring.RingNF
import Submission.Work.FTS.EllipticEst.EllHyp_certificates
import Submission.Work.FTS.EllipticEst.OpenQDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst

set_option autoImplicit false
set_option maxHeartbeats 800000

/-- **`ℋ^k` is closed under differences** for data which are `C^∞` on the open quadrant.

The point is that `f - g = f + (-1)·g` pointwise, and the right-hand side is `ℋ^k` because
scalar multiples of `SmoothOpen` functions are `SmoothOpen` (`SmoothOpen.const_mul'`), `ℋ^k`
is closed under scalar multiples (`Work.FTS.LocData.HkMem_const_mul`) and under sums
(`HkMem_add_open`). -/
theorem HkMem_sub_open {α : ℝ} {k : ℕ} {f g : ℝ → ℝ → ℝ}
    (hf : Work.FTS.EllipticEst.SmoothOpen f) (hg : Work.FTS.EllipticEst.SmoothOpen g)
    (hmf : Work.Spaces.HkMem α k f) (hmg : Work.Spaces.HkMem α k g) :
    Work.Spaces.HkMem α k (fun z θ => f z θ - g z θ) := by
  have hneg : Work.FTS.EllipticEst.SmoothOpen (fun z θ => (-1 : ℝ) * g z θ) :=
    SmoothOpen.const_mul' (-1) hg
  have hmneg : Work.Spaces.HkMem α k (fun z θ => (-1 : ℝ) * g z θ) :=
    Work.FTS.LocData.HkMem_const_mul α k (-1) hmg
  have hadd : Work.Spaces.HkMem α k (fun z θ => f z θ + (-1 : ℝ) * g z θ) :=
    HkMem_add_open hf hneg hmf hmneg
  have hfun : (fun z θ => f z θ + (-1 : ℝ) * g z θ) = fun z θ => f z θ - g z θ := by
    funext z θ
    ring
  rwa [hfun] at hadd

end Work.FTS.EllipticEst
