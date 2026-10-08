import Mathlib
import Submission.Work.RankOneUniqueness.Basic

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.RankOneUniqueness.canon_unique` — uniqueness of the canonical form `H·t·Q`

If `a·t·q = a'·t·q'` with `a, a' ∈ H` and `q, q' ∈ Q`, then `a = a'` and `q = q'`.
Indeed `a'⁻¹a = t·(q·q'⁻¹)·t`; the left-hand side is in `H`, so `q q'⁻¹ ∈ conj t H`, and
`q q'⁻¹ ∈ Q`, whence `q q'⁻¹ ∈ Q ∩ D = 1`.  Together with `canon_exists` this makes the
decomposition `G ∖ H = H·t·Q` a bijection, the basis of the `f`-map.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

open Submission.Blueprint

namespace Work.RankOneUniqueness

theorem canon_unique {G : Type} [Group G] {H Q : Subgroup G} {t : G}
    (h : Submission.Blueprint.IsSplitRankOne H Q t) {a a' q q' : G} (ha : a ∈ H) (ha' : a' ∈ H)
    (hq : q ∈ Q) (hq' : q' ∈ Q) (heq : a * t * q = a' * t * q') : a = a' ∧ q = q' := by
  have h2 : t * t = 1 := mul_self_eq_one h
  have h1 : a'⁻¹ * a * t * q = t * q' := by
    calc a'⁻¹ * a * t * q = a'⁻¹ * (a * t * q) := by group
      _ = a'⁻¹ * (a' * t * q') := by rw [heq]
      _ = t * q' := by group
  have hc : a'⁻¹ * a * t * (q * q'⁻¹) = t := by
    calc a'⁻¹ * a * t * (q * q'⁻¹) = (a'⁻¹ * a * t * q) * q'⁻¹ := by group
      _ = (t * q') * q'⁻¹ := by rw [h1]
      _ = t := by group
  have hmemH : t * (q * q'⁻¹) * t⁻¹ ∈ H := by
    have key : t * (q * q'⁻¹) * t⁻¹ = (a'⁻¹ * a)⁻¹ := by
      have h4 : t * (q * q'⁻¹) = (a'⁻¹ * a)⁻¹ * t := by
        calc t * (q * q'⁻¹) = (a'⁻¹ * a)⁻¹ * (a'⁻¹ * a * t * (q * q'⁻¹)) := by group
          _ = (a'⁻¹ * a)⁻¹ * t := by rw [hc]
      calc t * (q * q'⁻¹) * t⁻¹ = ((a'⁻¹ * a)⁻¹ * t) * t⁻¹ := by rw [h4]
        _ = (a'⁻¹ * a)⁻¹ := by group
    rw [key]
    exact H.inv_mem (H.mul_mem (H.inv_mem ha') ha)
  have hqqm : q * q'⁻¹ ∈ conj t H := by
    rw [mem_conj_iff]
    refine ⟨t * (q * q'⁻¹) * t⁻¹, hmemH, ?_⟩
    simpa only [inv_eq_self h] using (involution_conj (e := q * q'⁻¹) h2)
  have hmem : q * q'⁻¹ ∈ Q ⊓ twoPoint H t :=
    ⟨Q.mul_mem hq (Q.inv_mem hq'), mem_twoPoint_iff.mpr ⟨h.le (Q.mul_mem hq (Q.inv_mem hq')), hqqm⟩⟩
  rw [h.inf_eq] at hmem
  have hqq : q = q' := mul_inv_eq_one.mp (Subgroup.mem_bot.mp hmem)
  subst hqq
  have h2' : a * (t * q) = a' * (t * q) := by
    calc a * (t * q) = a * t * q := by rw [mul_assoc]
      _ = a' * t * q := heq
      _ = a' * (t * q) := by rw [mul_assoc]
  exact ⟨mul_right_cancel h2', rfl⟩

end Work.RankOneUniqueness
