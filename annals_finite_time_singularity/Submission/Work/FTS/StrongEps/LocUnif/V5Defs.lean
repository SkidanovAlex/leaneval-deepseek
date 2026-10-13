/-
Copyright: work module for the Elgindi finite-time singularity project.

# The measurable majorant for the slots of order `≤ 5`

Companion of `V6Defs.lean`.  The part of `HkIntegrand α 6 f` coming from slots of order
`≤ 5` is handled by a majorant built from the *sequence*: the `liminf`, as `n → ∞`, of
`ofReal (HkIntegrand α 5 (fn n))`.  Two facts make this the right object:

* it is almost everywhere measurable as soon as the sequence members are (they are
  continuous for our application), so the Tonelli step in the final assembly applies to it;
* it agrees a.e. with `ofReal (HkIntegrand α 5 f)` along a.e.-convergent slots, and its
  `∫⁻` is bounded by the `liminf` of the sequence's `∫⁻` by Fatou — with no measurability
  assumption on the limit function `f` itself.

Both facts are supplied by separate lemmas; this file only fixes the definition.
-/
import Mathlib.Basic.ENNReal.Basic
import Mathlib.Order.LiminfLimsup
import Submission.Work.Spaces.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology ENNReal
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.LocUnif

set_option autoImplicit false

/-- The measurable majorant of the slots of order `≤ 5` along a sequence `fn`:
`liminf_n ofReal (HkIntegrand α 5 (fn n) p)`. -/
def V5 (α : ℝ) (fn : ℕ → ℝ → ℝ → ℝ) (p : ℝ × ℝ) : ℝ≥0∞ :=
  Filter.liminf (fun n : ℕ => ENNReal.ofReal (Work.Spaces.HkIntegrand α 5 (fn n) p.1 p.2))
    Filter.atTop

end Work.FTS.StrongEps.LocUnif
