import Mathlib
import Submission.Work.KT.Defs
import Submission.Work.KT.Fund.hopf_trace_det
import Submission.Work.KT.Fund.Basic
import Submission.Work.KT.Fund.twoByTwo_idem_of_trace_det
import Submission.Work.KT.Rank.mvN_one_rank_v2
import Submission.Work.KT.bott_aux
import Submission.Work.KT.EG.mvn_twoByTwo_trace_one

namespace Work.KT.EG

open Matrix

/-- The Hopf idempotent is pointwise a rank-one projection, so its class at any point of `S²` is
the class of the trivial line bundle.  (Used by the assembly of `Work.KT.fund_product`: with the
base point of `S²` it gives `r γ = cls 1`.)

Route: `Fund.hopf_trace_det` (trace `1`, vanishing determinant for the matrix of functions) with
`Fund.twoByTwo_idem_of_trace_det` gives `Mat.IsIdem hopfIdem`; `Fund.K0.map_cls` turns the claim
into one about the matrix `P := hopfIdem.2.map (evalC t0).toRingHom`, a `2 × 2` complex idempotent
of trace one; `cls P = cls (Mat.one ℂ 1)` then follows from an explicit Murray–von Neumann
equivalence (`Fund.cls_eq_of_mvn`), or from `Rank.mvN_one_rank_v2` together with `Matrix.rank P = 1`
(the trace of an idempotent).  Both entries-cases (`P 0 0 ≠ 0` / `P 0 0 = 0`) have an explicit
one-line witness, e.g. `v = !![P 0 1, 1]`, `u = !![P 1 0, 1]` in the degenerate case, using
`P 0 1 * P 1 0 = P 0 0 * P 1 1` (vanishing determinant) and `P 0 0 + P 1 1 = 1`. -/
theorem hopf_eval_one (t0 : S2) :
    K0.mapA (A := C(S2, ℂ)) (B := ℂ) (evalC t0) (cls hopfIdem) = cls (Mat.one ℂ 1) := by
  -- `hopfIdem` is an idempotent, from trace `1` and vanishing determinant.
  have hIdem : hopfIdem.IsIdem :=
    Work.KT.Fund.twoByTwo_idem_of_trace_det hopfIdem.2
      Work.KT.Fund.hopf_trace_det.1 Work.KT.Fund.hopf_trace_det.2
  -- `K0.map` on the class of an idempotent is the class of the entrywise image.
  rw [K0.map_cls (evalC t0).toRingHom hIdem]
  -- Evaluate the two relations of `hopf_trace_det` at `t0`: `P := hopfIdem.2.map (evalC t0)`
  -- has trace `1` and vanishing determinant, so its class is that of the trivial line bundle.
  refine Work.KT.cls_eq_of_mvn (Mat.IsIdem.map (evalC t0).toRingHom hIdem)
    (Mat.one_isIdem (R := ℂ) 1) ?_
  exact mvn_twoByTwo_trace_one (hopfIdem.2.map (evalC t0).toRingHom)
    (congrArg (evalC t0) Work.KT.Fund.hopf_trace_det.1)
    (congrArg (evalC t0) Work.KT.Fund.hopf_trace_det.2)

end Work.KT.EG
