/-
# `Transfer/CSQ_one_unif.lean` — Cauchy–Schwarz at level `1`, uniform in `α`

The base case of the transfer induction needs the level-`1` Cauchy–Schwarz statement
`Transfer.CSQ α 1 (Work.Coercivity.H1IP α) CC` with a constant `CC` that is *independent of
`α`*: the transfer recursion `Transfer.main` produces a single `UnifIP` package for all small
`α`, so the constants it consumes may not depend on `α`.

This file records that the delivered membership-based bound `Transfer/H1IP_cs_of_mem.lean`
already has such a constant: its proof constructs the witness `10 ^ 22` explicitly (the four
pairings of `H1IP` contribute `10, 10¹⁰, 10¹⁷, 10²¹` and only the elementary arithmetic
`10 + 10¹⁰ + 10¹⁷ + 10²¹ ≤ 10²²` is used), and nothing in it depends on `α`.  We therefore
extract from it the honest statement with the constant *pinned*,
`H1IP_cs_fixed`, and then discharge the uniform existential by taking `CC = 10 ^ 22`.

Everything here rests on `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Order.Filter.Defs
import Submission.Work.FTS.CoercivityFix.Transfer.CoreDefs
import Submission.Work.FTS.CoercivityFix.Transfer.H1IP_cs_of_mem

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.CoercivityFix.Transfer

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false

/-- **Cauchy–Schwarz for `H1IP` with the constant `10 ^ 22` pinned, for every `α > 0`.**

The witness chosen in the proof of `H1IP_cs_of_mem` is literally `(10 : ℝ) ^ 22`, so the
existential can be re-read with the constant instantiated; `α` occurs only in the
hypotheses, never in the constant. -/
theorem H1IP_cs_fixed (α : ℝ) (hα : 0 < α) (f g : ℝ → ℝ → ℝ)
    (hf : Work.Spaces.HkMem α 1 f) (hg : Work.Spaces.HkMem α 1 g) :
    |Work.Coercivity.H1IP α f g|
      ≤ (10 : ℝ) ^ 22 * Work.Spaces.HkNorm α 1 f * Work.Spaces.HkNorm α 1 g :=
  H1IP_cs_of_mem α hα f g hf hg

/-- **Cauchy–Schwarz at level `1` with an `α`-free constant.**  Unlike
`Transfer.CSQ_one` — which produces a (possibly `α`-dependent) constant for each `α > 0` —
this exhibits a single `CC = 10 ^ 22` that works for every `α > 0`.  The `Q0Sm`-smoothness
hypotheses of `CSQ` are simply unused at level `1`. -/
theorem CSQ_one_unif :
    ∃ CC : ℝ, 0 < CC ∧ ∀ (α : ℝ), 0 < α →
      Work.FTS.CoercivityFix.Transfer.CSQ α 1 (Work.Coercivity.H1IP α) CC := by
  refine ⟨(10 : ℝ) ^ 22, by norm_num, fun α hα X Y _ _ hX hY => ?_⟩
  exact H1IP_cs_fixed α hα X Y hX hY

end Work.FTS.CoercivityFix.Transfer
