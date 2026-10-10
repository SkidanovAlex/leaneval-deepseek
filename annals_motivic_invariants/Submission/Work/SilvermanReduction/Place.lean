/-
Copyright (c) 2026 The annals_motivic_invariants team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Work.SilvermanReduction
-/
import Submission.Work.SilvermanReduction.Conditional
import Submission.Work.SilvermanReduction.Add

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The class-(a) local obstruction: the reduction datum at a place of the twist

`Work.PointlessTwist.ReductionPlace D` is the form in which the pointless-twist chain consumes a
*place*: an additive, `σ`-invariant map `E(L) →+ G` that does not kill the marker `P`
(`Work.PointlessTwist.pointlessOf_of_hasReductionPlace`).  This file produces that datum from the
Silverman VII.2.1 theory of the reduction map:

* `redPoint_add` (in `Add.lean`) — the reduction `E(L) →+ Ẽ(k)` is additive,
* `map_redPoint` — it is `σ`-invariant when `σ` preserves the valuation and acts trivially on the
  residue field (the place being totally ramified, this holds for every `σ ∈ Gal(L/𝕜)`),
* `LocalModelData.red_PL_ne_zero` — the marker reduces non-trivially.

## Main results

* `hasReductionPlace_of_localModelData` — **the class-(a) named input**: the local model data at a
  place gives `Work.PointlessTwist.HasReductionPlace D`.
* `pointlessOf_of_localModelData`, `not_exists_galMap_sub_eq_PL_of_localModelData` — consequently
  `Work.PointlessTwist.PointlessOf C₅ L`, in the element-level form `¬ ∃ Q, σ Q - Q = P`.
-/

set_option autoImplicit false
set_option linter.style.haveILetI false

open WeierstrassCurve WeierstrassCurve.Affine
open IsLocalRing (ResidueField residue)
open scoped WithZero

namespace Work.SilvermanReduction

noncomputable section

/-- **The class-(a) named input.**  The local-model data of `LocalModelData D` at a place of the
top field of `D` gives the place datum `Work.PointlessTwist.HasReductionPlace D`: the reduction map
`E(L) →+ Ẽ(k)` (additive by Silverman VII.2.1, proved in `Add.lean`) is `σ`-invariant and does not
kill the marker. -/
theorem hasReductionPlace_of_localModelData {𝕜 : Type} [Field 𝕜] [DecidableEq 𝕜]
    (D : Work.PointlessTwist.QuinticTwist 𝕜) (h : LocalModelData D) :
    Work.PointlessTwist.HasReductionPlace D :=
  hasReductionPlace_of_localModelData_of_add D h (fun P Q => redPoint_add h.R P Q)

/-- **The class-(a) local obstruction in the form the PointlessTwist chain consumes.** -/
theorem pointlessOf_of_localModelData {𝕜 : Type} [Field 𝕜] [DecidableEq 𝕜]
    (C₅ : Work.PointlessTwist.FiveTorsionCurve 𝕜) (L : Work.PointlessTwist.CyclicExtension 𝕜 5)
    (h : LocalModelData (Work.PointlessTwist.twistOf C₅ L)) :
    Work.PointlessTwist.PointlessOf C₅ L :=
  Work.PointlessTwist.pointlessOf_of_hasReductionPlace C₅ L
    (hasReductionPlace_of_localModelData _ h)

/-- **The class-(a) statement at the element level**: there is no point `Q` of `E(L)` with
`σ Q - Q = P`.  This is the form in which the residual is stated in `Work.PointlessTwist`
(`pointlessOf_iff_not_exists_shift`). -/
theorem not_exists_galMap_sub_eq_PL_of_localModelData {𝕜 : Type} [Field 𝕜] [DecidableEq 𝕜]
    (C₅ : Work.PointlessTwist.FiveTorsionCurve 𝕜) (L : Work.PointlessTwist.CyclicExtension 𝕜 5)
    (h : LocalModelData (Work.PointlessTwist.twistOf C₅ L)) :
    ¬ ∃ Q : (Work.PointlessTwist.twistOf C₅ L).LPoints,
      (Work.PointlessTwist.twistOf C₅ L).galMap Q - Q = (Work.PointlessTwist.twistOf C₅ L).PL :=
  (Work.PointlessTwist.pointlessOf_iff_not_exists_shift C₅ L).mp
    (pointlessOf_of_localModelData C₅ L h)

end

end Work.SilvermanReduction
