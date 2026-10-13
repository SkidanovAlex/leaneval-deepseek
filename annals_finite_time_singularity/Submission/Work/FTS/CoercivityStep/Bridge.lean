/-
# Reconciliation with the delivered vocabulary

The redesigned specification `IsHkIP_fts` *implies* the delivered
`Work.Coercivity.IsHkIP`: the delivered linearity clauses carry exactly the two
hypotheses `SmoothNbhd f` and `HkMem α k f`, i.e. the class `HkReg α k`, and the
remaining clauses (nonnegativity, comparability, coercivity) are verbatim.  So nothing
proved against the old specification is lost.

The converse fails, and this is the content of finding 2 in `Defs.lean`: the delivered
`IsHkIP` has no Cauchy–Schwarz clause and no second-argument linearity, so it cannot
support the induction step.

`Work.Construction.IsH4IP` is the interface of the a-priori estimate of §Modulation.  It
demands its additivity, homogeneity and Cauchy–Schwarz clauses for *arbitrary* functions,
which `Work.Coercivity.not_IsHkIP_H1IP` shows to be false for the concrete inner product;
`IsH4IP_fts` is the honest replacement (same role, clauses restricted to `HkReg α 4`).
-/
import Mathlib.Basic.Real.Basic
import Mathlib.Order.Filter.Defs
import Submission.Work.Coercivity.Defs
import Submission.Work.FTS.CoercivityStep.Defs
import Submission.Work.FTS.CoercivityStep.Norm.HkReg_closure

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.CoercivityStep

set_option autoImplicit false

/-- The redesigned specification implies the delivered one. -/
theorem IsHkIP_fts.to_old {α : ℝ} {k : ℕ} {IP : (ℝ → ℝ → ℝ) → (ℝ → ℝ → ℝ) → ℝ}
    (h : IsHkIP_fts α k IP) : Work.Coercivity.IsHkIP α k IP :=
  ⟨fun f₁ f₂ g hs₁ hs₂ hsg hm₁ hm₂ hmg =>
      h.core.add_fst f₁ f₂ g ⟨hs₁, hm₁⟩ ⟨hs₂, hm₂⟩ ⟨hsg, hmg⟩
        (Work.FTS.CoercivityStep.Norm.HkReg_closure α k (0:ℝ)
          ⟨hs₁, hm₁⟩ ⟨hs₂, hm₂⟩).1,
    fun c f g hsf hsg hmf hmg =>
      h.core.smul_fst c f g ⟨hsf, hmf⟩ ⟨hsg, hmg⟩,
    h.core.nonneg, h.core.le_self, h.core.upper, h.coercive⟩

/-- The `ℋ⁴` instance of the implication. -/
theorem IsH4IP_fts.to_old {α : ℝ} {IP : (ℝ → ℝ → ℝ) → (ℝ → ℝ → ℝ) → ℝ}
    (h : IsH4IP_fts α IP) : Work.Coercivity.IsHkIP α 4 IP :=
  h.hIP.to_old

end Work.FTS.CoercivityStep
