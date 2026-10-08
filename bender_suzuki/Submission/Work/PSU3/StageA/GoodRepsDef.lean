import Mathlib
import Submission.Work.PSU3.Defs
import Submission.Work.ThmF.Setup

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# Shared definitions for the case-b (Ch. VI §2) computation

`GoodReps H t s r` — the representatives of the `K`-orbits on `Q#` used in Peterfalvi II,
Ch. VI §2 (p. 262) — together with the two consequences of the structure identity
`t s t = r⁻¹ t r` used by the orbit computation (`t r⁻¹ t = s t r⁻¹`, `t r t = r t s`).

These live in their own module so that both `caseB_tQt_subset_of_Ksub` (which consumes the orbit
lemma) and `KOrbitsOfQ_full` (which proves it) can import them.
-/

namespace Work.PSU3.StageA

open LeanEval.GroupTheory.Defs
open Submission.Blueprint

variable {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t s r : G}

/-- The representatives of the `K`-orbits on `Q#` used in Peterfalvi II, Ch. VI §2 (p. 262):
`s`, `r`, `r⁻¹`, and `r · k⁻¹ r⁻¹ k = r r^{-k}` for `1 ≠ k ∈ Kset H t` (Peterfalvi's right
action `y^k = k⁻¹ y k`). -/
def GoodReps (H : Subgroup G) (t s r : G) : Set G :=
  ({s, r, r⁻¹} : Set G) ∪
    {x : G | ∃ k : G, k ∈ Work.ThmF.Kset H t ∧ k ≠ 1 ∧ x = r * (k⁻¹ * r⁻¹ * k)}

/-- **Peterfalvi II Ch. V §2 Lemma 1 (3):** `t r⁻¹ t = s t r⁻¹` follows from the structure
identity `t s t = r⁻¹ t r`. -/
theorem caseB_t_conj_r_inv (ht2 : t * t = 1) (hsr : t * s * t = r⁻¹ * t * r) :
    t * r⁻¹ * t = s * t * r⁻¹ := by
  have h1 : t * (r⁻¹ * t * r) = s * t := by
    have h := congrArg (fun x : G => t * x) hsr
    have e : t * (t * s * t) = (t * t) * (s * t) := by group
    rw [e, ht2, one_mul] at h
    exact h.symm
  calc t * r⁻¹ * t = t * (r⁻¹ * t * r) * r⁻¹ := by group
    _ = s * t * r⁻¹ := by rw [h1]

/-- **Peterfalvi II Ch. V §2 Lemma 1 (3):** `t r t = r t s` follows from the structure identity. -/
theorem caseB_t_conj_r (ht2 : t * t = 1) (hs2 : orderOf s = 2)
    (hsr : t * s * t = r⁻¹ * t * r) : t * r * t = r * t * s := by
  have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
  have hs_inv : s⁻¹ = s := by
    have h := pow_orderOf_eq_one s
    rw [hs2] at h
    exact inv_eq_of_mul_eq_one_right (by simpa [pow_two] using h)
  have h3 := caseB_t_conj_r_inv ht2 hsr
  have h4 : (t * r⁻¹ * t)⁻¹ = t * r * t := by
    rw [mul_inv_rev, mul_inv_rev, hti]
    group
  rw [← h4, h3, mul_inv_rev, mul_inv_rev, inv_inv, hti, hs_inv]
  group


end Work.PSU3.StageA
