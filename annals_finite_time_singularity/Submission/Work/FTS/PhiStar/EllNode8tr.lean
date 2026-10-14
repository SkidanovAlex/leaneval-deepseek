import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Submission.Work.FTS.EllipticEst.OpenFTC.absFtcLeIntegralAbsDeriv
import Submission.Work.FTS.PhiStar.RouteB.EllNode8trBody
import Submission.Work.GalerkinFix.RegQ.HkMem_mono_Q
import Submission.Work.Spaces.mixed_mul_le
import Submission.Work.Spaces.sin_two_rpow
import Submission.Work.Spaces.sq_mul_div_rpow

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `PhiStar.EllNode8tr` — the trace-strengthened elliptic node (R5, lead install R6, 2026-10-11)

`cbc/fts_ellnode_ruling.md` §4.3 (R5), §4.4; review `cbc/fts_ellnode_ruling_REVIEW.md`.

Replaces `PhiStar.bslOp_sol_exists_pp 8` on the `theorem_1_v2` path (via
`EllExist.ellClassOk_exists_of_inputs_tr` in `ClassC.A2`).  It is the old leaf at `k = 8` plus the
hypothesis `ThetaTraces α 10 F`, so it is *weaker* than `bslOp_sol_exists_pp 8`.  The old leaf
cannot be proved with the in-tree machinery because compact-source density
(`Honesty.exists_cptQ_approx`) needs vanishing θ-traces, which do not follow from its hypotheses
(`Refute/not_exists_cptQ_approx`).

Route B′ (R5 assembly, type-checked by the reviewer as `C46Rev.R5_check`):
R1 `exists_cptQ_approx_th 10` → `ellWeakPos_psiSeries_of_cptQ 10` → R2
`bslSolExists_psiSeries_of_node_hyp 10` → R3 `psiSeries_L2_of_approx` → R4
`hkMem_slots_of_approx_pp 8` → the ten clauses of `EllWeakPos α 8`.
-/

noncomputable section
open scoped Real Topology
open Filter

namespace Work.FTS.PhiStar

/-- **R5 / the new node** (replaces `bslOp_sol_exists_pp 8` / `ClassC.EllNode8pp` on the path). -/
def EllNode8tr : Prop :=
  ∀ (α : ℝ) (F : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 / 4 →
    Work.FTS.EllipticEst.SmoothOpen F → Work.Spaces.HkMem α 10 F → ThetaTraces α 10 F →
    (∀ z, 0 < z → Work.Elliptic.Fstar F z = 0) →
    (∀ θ ∈ Work.Spaces.Iθ, Tendsto (fun z => F z θ) atTop (𝓝 0)) →
    ∃ Ψ : ℝ → ℝ → ℝ,
      Work.FTS.EllipticEst.TT.EllWeakPos α 8 F Ψ ∧ Work.Elliptic.IsBslSol α F Ψ

/-- **R5.**  Proved: see `Submission.Work.FTS.PhiStar.RouteB.EllNode8trBody`. -/
theorem EllNode8tr_holds : EllNode8tr := RouteB.ellNode8tr_body

end Work.FTS.PhiStar
