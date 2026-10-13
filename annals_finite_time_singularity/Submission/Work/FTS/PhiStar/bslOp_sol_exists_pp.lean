import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Submission.Work.FTS.PhiStar.Defs
import Submission.Work.FTS.PhiStar.Basic
import Submission.Work.FTS.EllipticEst.TT.WeakDefs
import Submission.Work.Elliptic.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `PhiStar.bslOp_sol_exists_pp` — the repaired elliptic existence node (two orders of slack)

Lead install, 2026-10-11 (`cbc/fts_phistar_REVIEW.md`, `cbc/fts_mem10_install.md`).

The original node `PhiStar.bslOp_sol_exists k` (`HkMem α k F ⇒ EllWeakPos α k`) is **false** at
every `k`, in particular at `k = 8`: `EllWeakPos α k` contains the order-`k+3` slot
`HkMem α k (z∂_z∂_θ²Ψ)`, while `bslOp` is uniformly elliptic with `s = log z`-invariant
coefficients in interior windows, so `F ∈ ℋᵏ` only gives order `k+2` for `Ψ` (review §1–§2,
explicit counterexample with disjoint bumps at `s_n = 10n`).  One extra order is not enough
either: the every-`z` slice conjunct of `HkMem` fails at top order (review §3).

The repaired node assumes `HkMem α (k+2) F`.  It is used at `k = 8` (ClassC field `mem10`), via
`EllExist.ellClassOk_exists_of_inputs_pp 8` in `ClassC.A2`.  The old file is left untouched
(it is no longer on the `theorem_1_v2` path).
-/

namespace Work.FTS.PhiStar

/-- **The repaired elliptic existence node** (`HkMem α (k+2) F ⇒ EllWeakPos α k F Ψ`). -/
theorem bslOp_sol_exists_pp (k : ℕ) :
    ∀ (α : ℝ) (F : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 / 4 →
      Work.FTS.EllipticEst.SmoothOpen F → Work.Spaces.HkMem α (k + 2) F →
      (∀ z, 0 < z → Work.Elliptic.Fstar F z = 0) →
      (∀ θ ∈ Work.Spaces.Iθ, Filter.Tendsto (fun z => F z θ) Filter.atTop (nhds 0)) →
      ∃ Ψ : ℝ → ℝ → ℝ,
        Work.FTS.EllipticEst.TT.EllWeakPos α k F Ψ ∧ Work.Elliptic.IsBslSol α F Ψ := by
  sorry

end Work.FTS.PhiStar
