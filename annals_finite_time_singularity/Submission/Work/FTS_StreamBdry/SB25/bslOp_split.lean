import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Submission.Work.FTS_StreamBdry.Basic
import Submission.Work.FTS_StreamBdry.SB25.Defs
import Submission.Work.FTS_StreamBdry.SB25.bslOp_eq_s2_Lgs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS_StreamBdry.SB25

/-- The ground-state identity of the singular stream-boundary problem, in direct (non-`Prop`)
form: for `(z,θ)` in the open quadrant and `Q` of class `C²` there,

`bslOp α Q z θ = sin(2θ) · Lgs α (Q / sin 2θ) z θ`.

This is the pointwise instance of `Work.FTS_StreamBdry.SB25.BslOpEqS2Lgs`
(proved in `SB25/bslOp_eq_s2_Lgs.lean`). -/
theorem bslOp_split (α : ℝ) (Q : ℝ → ℝ → ℝ) {z θ : ℝ}
    (hQd : (z, θ) ∈ Work.Construction.Qd)
    (hQ : ContDiffAt ℝ 2 (Function.uncurry Q) (z, θ)) :
    Work.Elliptic.bslOp α Q z θ
      = Work.Construction.s2 θ *
        Work.FTS_StreamBdry.SB25.Lgs α
          (fun z' θ' => Q z' θ' / Work.Construction.s2 θ') z θ :=
  Work.FTS_StreamBdry.SB25.bslOp_eq_s2_Lgs α Q z θ hQd hQ

end Work.FTS_StreamBdry.SB25
