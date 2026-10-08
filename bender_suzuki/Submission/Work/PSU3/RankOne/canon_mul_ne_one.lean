import Mathlib
import Submission.Work.PSU3.Defs
import Submission.Work.RankOneUniqueness.Basic
import Submission.Work.PSU3.RankOne.H16

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.PSU3.RankOne.canon_mul_ne_one` — the H6 side condition `f(x) g(y) ≠ 1`

Peterfalvi II Ch. VII §1, H6: for `x, y ∈ Q#` with `x y ≠ 1`, the product `f(x) g(y)` is again
a nontrivial element of `Q`, so that it has a canonical form and `canon_mul` can be applied.

The argument is short.  If `f(x) g(y) = 1`, then `f(x) = g(y)⁻¹`; by `canon_inv` (H1/H4b)
applied to the data of `y`, `g(y)⁻¹ = f(y⁻¹)`, so `f(x) = f(y⁻¹)`.  The relation `FRel` is
injective on `Q` (helper `fRel_injective` below: `t x t = m t z = t x' t` forces
`x x'⁻¹ ∈ Q ∩ D = 1`), hence `x = y⁻¹` and `x y = 1`, a contradiction.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

open LeanEval.GroupTheory.Defs
open Submission.Blueprint
open Work.RankOneUniqueness

namespace Work.PSU3.RankOne

/-- The relation `FRel H t · z` is injective on `Q`: if `t a t = m t z` and `t b t = m' t z`
with `a, b ∈ Q`, then `a = b`.  Indeed `t (a b⁻¹) t = (t a t)(t b t)⁻¹ = m m'⁻¹ ∈ H`, so
`a b⁻¹ ∈ H ∩ H^t = D`, while `a b⁻¹ ∈ Q`; and `Q ∩ D = 1`. -/
lemma fRel_injective {G : Type} [Group G] {H Q : Subgroup G} {t : G}
    (h : IsSplitRankOne H Q t) {a b z : G} (ha : a ∈ Q) (hb : b ∈ Q)
    (h1 : FRel H t a z) (h2 : FRel H t b z) : a = b := by
  obtain ⟨m, hm, hm1⟩ := h1
  obtain ⟨m', hm', hm2⟩ := h2
  have ht : t * t = 1 := mul_self_eq_one h
  have hkey : t * (a * b⁻¹) * t⁻¹ = m * m'⁻¹ := by
    calc t * (a * b⁻¹) * t⁻¹ = (t * a * t) * (t * b * t)⁻¹ := by group
      _ = (m * t * z) * (m' * t * z)⁻¹ := by rw [hm1, hm2]
      _ = m * m'⁻¹ := by group
  have hmem : a * b⁻¹ ∈ twoPoint H t := by
    refine mem_twoPoint_iff.mpr ⟨H.mul_mem (h.le ha) (H.inv_mem (h.le hb)), ?_⟩
    rw [mem_conj_iff]
    refine ⟨m * m'⁻¹, H.mul_mem hm (H.inv_mem hm'), ?_⟩
    rw [← hkey, inv_eq_self h]
    calc t * (t * (a * b⁻¹) * t) * t = (t * t) * (a * b⁻¹) * (t * t) := by group
      _ = a * b⁻¹ := by rw [ht, one_mul, mul_one]
  have hmemQ : a * b⁻¹ ∈ Q := Q.mul_mem ha (Q.inv_mem hb)
  have hbot : a * b⁻¹ ∈ (⊥ : Subgroup G) := by
    rw [← h.inf_eq]
    exact ⟨hmemQ, hmem⟩
  exact mul_inv_eq_one.mp (Subgroup.mem_bot.mp hbot)

theorem canon_mul_ne_one {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t : G}
    (h : Submission.Blueprint.IsSplitRankOne H Q t) {x y gx dx fx gy dy fy : G}
    (hx : x ∈ Q) (hx1 : x ≠ 1) (hy : y ∈ Q) (hy1 : y ≠ 1)
    (hcx : Work.PSU3.Canon3 H Q t x gx dx fx) (hcy : Work.PSU3.Canon3 H Q t y gy dy fy)
    (hxy : x * y ≠ 1) : fx * gy ≠ 1 := by
  intro hcon
  obtain ⟨hgx, hdx, hfx, heqx⟩ := hcx
  have h1 : FRel H t x fx :=
    ⟨gx * dx, H.mul_mem (h.le hgx) (twoPoint_le_left H t hdx), heqx⟩
  have hinv := canon_inv h hcy
  obtain ⟨hfy', hdy', hgy', heqy'⟩ := hinv
  have h2raw : FRel H t y⁻¹ gy⁻¹ :=
    ⟨fy⁻¹ * (t * dy⁻¹ * t), H.mul_mem (h.le hfy') (twoPoint_le_left H t hdy'), heqy'⟩
  have hfx_eq : fx = gy⁻¹ := eq_inv_of_mul_eq_one_left hcon
  have h2 : FRel H t y⁻¹ fx := by rw [hfx_eq]; exact h2raw
  have hxy_eq : x = y⁻¹ := fRel_injective h hx (Q.inv_mem hy) h1 h2
  exact hxy (by rw [hxy_eq, inv_mul_cancel])

end Work.PSU3.RankOne
