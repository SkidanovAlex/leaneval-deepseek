import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS.StrongGlobal.Defs
import Submission.Work.FTS_EllLimOK.IsBslSolPos_add

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongGlobal

open scoped Real Topology
open MeasureTheory Set Filter
open Work.FTS.Galerkin (Fam)

set_option linter.unusedVariables false

noncomputable section

/-! ## The tool-kit of the junction

The junction lemma `contDiffOn_concat_1` is proved by localising at the junction hyperplane
`{τ = τ₀}`: the box `concatBox x y τ₀ ε` straddles it, the concatenation is differentiable at every
point of the box with the (explicit) derivative `concatStep`, and `concatStep` is continuous on the
box because its two branches `fderiv ℝ (uncurry3 G)` and `fderiv ℝ (uncurry3 H)` are continuous
there and agree at the hyperplane.  That agreement is the one genuinely two-sided ingredient,
`junction_fderiv_eq`: on the hyperplane the two families agree as *functions of `(z,θ)`*, hence so
do their `z`- and `θ`-partials, while their `τ`-partials agree by hypothesis. -/











end

end Work.FTS.StrongGlobal
