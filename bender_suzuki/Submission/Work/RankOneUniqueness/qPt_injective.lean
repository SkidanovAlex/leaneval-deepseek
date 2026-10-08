import Mathlib
import Submission.Work.RankOneUniqueness.Basic

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.RankOneUniqueness.qPt_injective` — the `Q`-labelling is injective

The map `x ↦ qPt H t x = x·t·H` is injective on `Q`: if `x·t·H = y·t·H` then
`(x·t)⁻¹(y·t) = t·(x⁻¹y)·t ∈ H`, so `x⁻¹y ∈ H ∩ H^t = D`; as `x⁻¹y ∈ Q` and
`Q ∩ D = 1`, we get `x = y`.  Consequently the `|Q|` points `qPt H t x` are all distinct.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

open Submission.Blueprint

namespace Work.RankOneUniqueness

theorem qPt_injective {G : Type} [Group G] {H Q : Subgroup G} {t : G}
    (h : Submission.Blueprint.IsSplitRankOne H Q t) {x y : G} (hx : x ∈ Q) (hy : y ∈ Q)
    (heq : Work.RankOneUniqueness.qPt H t x = Work.RankOneUniqueness.qPt H t y) : x = y := by
  have h2 : t * t = 1 := mul_self_eq_one h
  have h1 : (x * t)⁻¹ * (y * t) ∈ H := QuotientGroup.eq.mp heq
  have h3 : t * (x⁻¹ * y) * t ∈ H := by
    have key : (x * t)⁻¹ * (y * t) = t * (x⁻¹ * y) * t := by
      rw [mul_inv_rev, inv_eq_self h]
      group
    rwa [key] at h1
  have hxym : x⁻¹ * y ∈ conj t H := by
    rw [mem_conj_iff]
    refine ⟨t * (x⁻¹ * y) * t, h3, ?_⟩
    rw [inv_eq_self h]
    simpa only [inv_eq_self h] using (involution_conj (e := x⁻¹ * y) h2)
  have hxyH : x⁻¹ * y ∈ Q ⊓ twoPoint H t :=
    ⟨Q.mul_mem (Q.inv_mem hx) hy,
      mem_twoPoint_iff.mpr ⟨h.le (Q.mul_mem (Q.inv_mem hx) hy), hxym⟩⟩
  rw [h.inf_eq] at hxyH
  exact inv_mul_eq_one.mp (Subgroup.mem_bot.mp hxyH)

end Work.RankOneUniqueness
