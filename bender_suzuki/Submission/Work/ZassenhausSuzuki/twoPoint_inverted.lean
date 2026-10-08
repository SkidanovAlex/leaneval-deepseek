import Submission.Work.ZassenhausSuzuki.Defs
import Submission.Work.ZassenhausPSL2.ZData.t_conj_eq_inv

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# The Weyl element inverts the two-point stabiliser (Suzuki 1962, Prop. 3)

L1 of the lead's design note `NOTES_LEAD_probe1630.md`: in a Zassenhaus split rank-one
configuration, `t` inverts `D = H ∩ H^t`.

The statement is the same as the already delivered `Work.ZassenhausPSL2.t_conj_eq_inv`
(which carries two extra hypotheses, shown spurious there); it is stated here for the
`t⁻¹` form used in this area.

**Note (deviation from the reviewed statement).**  The reviewed form had no hypotheses on `Q`;
the version here keeps `Q ≠ ⊥` and `IsPGroup 2 Q` because the delivered proof of
`Work.ZassenhausPSL2.ZData.t_conj_eq_inv` is stated with them.  In the intended application
(`suzukiDataProp0`) both are available: `IsPGroup 2 Q` is a hypothesis there and
`¬ IsAbelianSubgroup Q` gives `Q ≠ ⊥`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

open LeanEval.GroupTheory.Defs
open Submission.Blueprint

namespace Work.ZassenhausSuzuki

theorem twoPoint_inverted {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t : G}
    (h : IsSplitRankOne H Q t) (hZ : IsZassenhaus H) (hQ : Q ≠ ⊥) (h2 : IsPGroup 2 Q) :
    ∀ d ∈ twoPoint H t, t * d * t⁻¹ = d⁻¹ := by
  have ht : t⁻¹ = t := Work.ZassenhausPSL2.t_inv h
  intro d hd
  rw [ht]
  exact Work.ZassenhausPSL2.ZData.t_conj_eq_inv H Q t h hZ hQ h2 d hd

end Work.ZassenhausSuzuki
