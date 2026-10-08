import Mathlib
import Submission.Work.RankOneUniqueness.Basic
import Submission.Work.RankOneUniqueness.exists_smul_t_eq

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.RankOneUniqueness.qPt_surjective` — `Q` is transitive on `Ω ∖ {∞}`

Every point `ω ≠ ∞` of `Ω = G ⧸ H` is of the form `qPt H t x = x·t·H` with `x ∈ Q`.
Indeed `H` is transitive on `Ω ∖ {∞}` (`exists_smul_t_eq`), say `a • (t • ∞) = ω`, and
`a = q·d` with `q ∈ Q`, `d ∈ D = H ∩ H^t` (Basic.fact_exists); since `d` fixes `t • ∞`
(its `t`-conjugate lies in `H`), `ω = q • (t • ∞) = qPt H t q`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

open Submission.Blueprint

namespace Work.RankOneUniqueness

theorem qPt_surjective {G : Type} [Group G] {H Q : Subgroup G} {t : G}
    (h : Submission.Blueprint.IsSplitRankOne H Q t) {ω : G ⧸ H}
    (hω : ω ≠ Work.RankOneUniqueness.pt H) :
    ∃ x ∈ Q, Work.RankOneUniqueness.qPt H t x = ω := by
  obtain ⟨a, ha, haω⟩ := exists_smul_t_eq h hω
  obtain ⟨q, hq, d, hd, hqd⟩ := fact_exists h ha
  refine ⟨q, hq, ?_⟩
  have hdt : d • (t • pt H) = t • pt H := by
    have hdtH : t * d * t ∈ H := t_mul_mul_t_mem_of_mem_twoPoint (mul_self_eq_one h) hd
    have hsplit : t * (t * d * t) = d * t := by
      rw [mul_assoc t d t, mul_self_mul h]
    rw [smul_pt, smul_mk, ← hsplit, QuotientGroup.mk_mul_of_mem t hdtH]
  rw [← haω, hqd, qPt_eq_smul, mul_smul, hdt]

end Work.RankOneUniqueness
