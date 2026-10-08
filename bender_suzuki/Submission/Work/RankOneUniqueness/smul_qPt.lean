import Mathlib
import Submission.Work.RankOneUniqueness.Basic

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.RankOneUniqueness.smul_qPt` — the `H`-action on the `Q`-labelling

If `a ∈ H` and `a·x = z·d` with `x, z ∈ Q`, `d ∈ D = H ∩ H^t` (the `Q·D`-factorisation of
`a·x`), then `a • qPt H t x = qPt H t z`: the point labelled `x` is `x • (t • ∞)`, and the
`D`-part is absorbed across `t` because `t·d·t ∈ H`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

open Submission.Blueprint

namespace Work.RankOneUniqueness

theorem smul_qPt {G : Type} [Group G] {H Q : Subgroup G} {t : G}
    (h : Submission.Blueprint.IsSplitRankOne H Q t) {a x z d : G} (ha : a ∈ H) (hx : x ∈ Q)
    (hz : z ∈ Q) (hd : d ∈ Submission.Blueprint.twoPoint H t)
    (hfac : a * x = z * d) :
    a • Work.RankOneUniqueness.qPt H t x = Work.RankOneUniqueness.qPt H t z := by
  have h2 : t * t = 1 := mul_self_eq_one h
  have hdt : t * d * t ∈ H := t_mul_mul_t_mem_of_mem_twoPoint h2 hd
  rw [qPt_def, smul_mk, ← mul_assoc, hfac]
  have hsplit : (z * t) * (t * d * t) = z * d * t := by
    rw [mul_assoc z t (t * d * t), mul_assoc t d t, mul_self_mul h, mul_assoc]
  rw [← hsplit, QuotientGroup.mk_mul_of_mem (z * t) hdt]
  rfl

end Work.RankOneUniqueness
