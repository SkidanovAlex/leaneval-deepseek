/-
Copyright: work module for the Elgindi finite-time singularity project.

# `FTS_EllLimOK.BoxDataH.BoxRegOfBoxUniform2` — closed-box regularity from the box-uniform data

`Crux.contDiffOn_two_of_boxUniform2` gives the `C²`-regularity of the pointwise limit on a
*non-degenerate* box (`a < b`).  The predicate `BoxReg` quantifies over all boxes with `0 < a ≤ b`,
including the degenerate ones (`a = b`); a degenerate box is contained in the non-degenerate box
`[a, a+1]`, so the missing case is a restriction.  This module packages the aggregated form used by
the cluster-limit extraction: the family has its box-uniform data on *every* box and converges to
`G` on every box, hence `G` is `BoxReg`.

Everything here is `sorry`-free.
-/
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS_EllLimOK.BoxDataH.BoxUniform
import Submission.Work.FTS_EllLimOK.BoxDataH.Crux

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS_EllLimOK.BoxDataH

set_option autoImplicit false

/-- **Closed-box regularity of a pointwise limit from the box-uniform data on every box.** -/
theorem boxReg_of_boxUniform2 {H : ℕ → ℝ → ℝ → ℝ} {G : ℝ → ℝ → ℝ}
    (hU : ∀ a b : ℝ, 0 < a → a < b → BoxUniform2 a b H)
    (hconv : ∀ a b : ℝ, 0 < a → a < b → ∀ z ∈ Set.Icc a b, ∀ θ ∈ Set.Icc 0 (Real.pi / 2),
      Filter.Tendsto (fun n => H n z θ) Filter.atTop (nhds (G z θ))) :
    Work.FTS_EllLimOK.BoxReg G := by
  intro a b ha hab
  rcases lt_or_eq_of_le hab with h | h
  · exact contDiffOn_two_of_boxUniform2 h (hU a b ha h) (hconv a b ha h)
  · subst h
    have hsub : Work.FTS_EllLimOK.cbox a a ⊆ Work.FTS_EllLimOK.cbox a (a + 1) := by
      intro p hp
      obtain ⟨hp1, hp2⟩ := Work.FTS_EllLimOK.mem_cbox.mp hp
      exact Work.FTS_EllLimOK.mem_cbox.mpr ⟨⟨hp1.1, by linarith [hp1.2]⟩, hp2⟩
    exact (contDiffOn_two_of_boxUniform2 (by linarith) (hU a (a + 1) ha (by linarith))
      (hconv a (a + 1) ha (by linarith))).mono hsub

end Work.FTS_EllLimOK.BoxDataH
