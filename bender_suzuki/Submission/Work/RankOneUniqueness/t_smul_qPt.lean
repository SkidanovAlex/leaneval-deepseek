import Mathlib
import Submission.Work.RankOneUniqueness.Basic

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.RankOneUniqueness.t_smul_qPt` — the action of `t` on the `Q`-labelling

The content of Peterfalvi II Ch. VII §1 needed for the uniqueness lemma: if `t x⁻¹ t = m t y`
is the canonical form of `t x⁻¹ t` (`m ∈ H`, `y ∈ Q`), then
`t • qPt H t x = qPt H t y⁻¹`.
(With `x = f(y)`-notation: the `Q`-part of the canonical form of `t x t` is `y⁻¹`, which by
the book's H1 is exactly `g(x)⁻¹`; this is the compatibility of the `t`-action with the map
`f` transported by `ψ`.)
-/

set_option autoImplicit false
set_option linter.unusedVariables false

open Submission.Blueprint

namespace Work.RankOneUniqueness

theorem t_smul_qPt {G : Type} [Group G] {H Q : Subgroup G} {t : G}
    (h : Submission.Blueprint.IsSplitRankOne H Q t) {x m y : G} (hx : x ∈ Q) (hx1 : x ≠ 1)
    (hm : m ∈ H) (hy : y ∈ Q) (hcanon : t * x⁻¹ * t = m * t * y) :
    t • Work.RankOneUniqueness.qPt H t x = Work.RankOneUniqueness.qPt H t y⁻¹ := by
  have h1 : t * x * t = y⁻¹ * t * m⁻¹ := by
    have := congrArg Inv.inv hcanon
    simpa only [mul_inv_rev, inv_inv, inv_eq_self h, mul_assoc] using this
  have key : (y⁻¹ * t * m⁻¹)⁻¹ * (y⁻¹ * t) = m := by group
  rw [qPt, smul_mk, ← mul_assoc, qPt, QuotientGroup.eq, h1, key]
  exact hm

end Work.RankOneUniqueness
