import Mathlib.Basic.Real.Basic
import Mathlib.Order.Filter.Defs
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.StrongEps.Basic
import Submission.Work.FTS.StrongEps.HkMem_Jeps_ten_of_eight

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `StrongEps/Mem10Obligations` — the `ℋ¹⁰` obligation of the mollifier part of `ClassC`

Lead install, 2026-10-11 (`cbc/fts_phistar_REVIEW.md` §3, `cbc/fts_mem10_install.md`).

`ClassC` gained the field `mem10 : HkMem α 10 g` (the repaired elliptic node
`PhiStar.bslOp_sol_exists_pp 8` needs two orders of slack).  Every `ClassC` element that the
tree produces is a log-mollified profile `J_ε f` (possibly corrected by `Pz`), and `SoftClass`
(the mollifier part of `ClassC`, `MolClassC.lean`) gained the matching field `mem10`, supplied
in `softClass_Jeps` by

  `Work.FTS.StrongEps.HkMem_Jeps_ten_of_eight` — `J_ε : ℋ⁸ → ℋ¹⁰`, for **every** `ε > 0`.

**Status: DISCHARGED.**  The declaration now lives in
`Submission/Work/FTS/StrongEps/HkMem_Jeps_ten_of_eight.lean` (module
`Submission.Work.FTS.StrongEps.HkMem_Jeps_ten_of_eight`), which this file imports; the proof goes
through the scale-free two-order gain `TenOfEight.HkMem_Jeps_gain_pos`
(`Submission/Work/FTS/StrongEps/TenOfEight/GainAll.lean`), which removes the `ε ≤ 1` restriction of
`EpsE4Thr.HkMem_Jeps_gain` by replacing the routed density `LamFull ρ ε c M` with a scale-free one
(the kernel factor `max 1 (ε⁻¹^M)`).  The boundary-vanishing hypothesis of the `EpsE4Thr` form is
*unused* there (`J_ε f` reads `f` only on the open quadrant), so it does not appear in the
delivered statement.

The statement, byte-for-byte as installed:

```lean
theorem HkMem_Jeps_ten_of_eight {ρ : ℝ × ℝ → ℝ} (hρ : IsSmoothKernel ρ) {α : ℝ}
    (hα : α ∈ Set.Ioc 0 1) {ε : ℝ} (hε : 0 < ε) {f : ℝ → ℝ → ℝ}
    (hsm : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry f) Quad)
    (hmem : Work.Spaces.HkMem α 8 f) :
    Work.Spaces.HkMem α 10 (Jeps ρ ε f)
```
-/

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps

set_option autoImplicit false

end Work.FTS.StrongEps
