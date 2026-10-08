import Mathlib
import Submission.Work.CORE3.Defs
import Submission.Work.CORE2A.Basic
import Submission.Work.CORE3.Case1bEightNineDefs

/-!
# Elementary API for the coset-involution count (Bender 1981 §3)

This file collects the *elementary* (Bender 1.4 style) facts about the inverted set
`invSetIn Hh y = {x ∈ Hh | y * x * y = x⁻¹}` of an involution `y` that are used by
`Work.CORE3.CosetInvCountLeFour`.

* `mul_inv_mem_invSet_of_mem_invSetIn` — Bender 1.4 (second part): if the involution `y`
  inverts `f` and `g`, then `g * y` inverts `f * g⁻¹`.
* `invSetIn_eq_of_mul_inv_mem` — if moreover no involution outside `Hh` inverts a nontrivial
  element of a fixed normal subgroup `W ≤ Hh`, then two elements of `invSetIn Hh y` whose
  quotient lies in `W` coincide.  This is the injectivity of the "coset modulo `W`" map.
* `ncard_invSetIn_le_relIndex` — consequently `|invSetIn Hh y| ≤ W.relIndex Hh`.
-/

namespace Work.CORE3

open Work.GW2
open Subgroup

variable {G : Type} [Group G]

/-- Bender 1981, 1.4 (second part).  If the involution `y` inverts `f` and `g`
(`y * f * y = f⁻¹`, `y * g * y = g⁻¹`) then `g * y` inverts `f * g⁻¹`. -/
theorem mul_inv_mem_invSet_of_mem_invSetIn (y f g : G) (hy : y * y = 1)
    (hf : y * f * y = f⁻¹) (hg : y * g * y = g⁻¹) :
    (g * y) * (f * g⁻¹) * (g * y)⁻¹ = (f * g⁻¹)⁻¹ := by
  have hyinv : y⁻¹ = y := inv_eq_of_mul_eq_one_right hy
  have h1 : y * f * y⁻¹ = f⁻¹ := by rw [hyinv]; exact hf
  have h2 : y * g⁻¹ * y⁻¹ = g := by
    have hkey : y * g⁻¹ * y⁻¹ = (y * g * y)⁻¹ := by
      rw [mul_inv_rev, mul_inv_rev, hyinv]; group
    rw [hkey, hg, inv_inv]
  rw [mul_inv_rev]
  rw [show g * y * (f * g⁻¹) * (y⁻¹ * g⁻¹)
        = g * (y * f * y⁻¹) * (y * g⁻¹ * y⁻¹) * g⁻¹ from by group]
  rw [h1, h2]
  group

/-- **Injectivity modulo `W`.**  Let `W ≤ Hh` be a subgroup such that no involution outside
`Hh` inverts a nontrivial element of `W` (Bender (5) for `W = O₂(Ĥ)U`).  Then for an involution
`y ∉ Hh`, two elements `f, g ∈ invSetIn Hh y` with `f * g⁻¹ ∈ W` are equal. -/
theorem invSetIn_eq_of_mul_inv_mem {Hh W : Subgroup G} (hWle : W ≤ Hh)
    (h5 : ∀ z : G, z * z = 1 → z ∉ Hh → invSet W z = {1})
    {y f g : G} (hy : y * y = 1) (hyH : y ∉ Hh) (hf : f ∈ invSetIn Hh y)
    (hg : g ∈ invSetIn Hh y) (hfg : f * g⁻¹ ∈ W) : f = g := by
  -- `g * y` is an involution outside `Hh`
  have hgy2 : (g * y) * (g * y) = 1 := by
    rw [show (g * y) * (g * y) = g * (y * g * y) from by group, hg.2, mul_inv_cancel]
  have hgyH : g * y ∉ Hh := by
    intro hmem
    have h := Hh.mul_mem (Hh.inv_mem hg.1) hmem
    rw [inv_mul_cancel_left] at h
    exact hyH h
  have hinv : (g * y) * (f * g⁻¹) * (g * y)⁻¹ = (f * g⁻¹)⁻¹ :=
    mul_inv_mem_invSet_of_mem_invSetIn y f g hy hf.2 hg.2
  have hmem : f * g⁻¹ ∈ invSet W (g * y) := ⟨hfg, hinv⟩
  rw [h5 (g * y) hgy2 hgyH] at hmem
  exact mul_inv_eq_one.mp (Set.mem_singleton_iff.mp hmem)

/-- **The coset bound.**  Under the same hypothesis (Bender (5) for `W`, which is assumed normal
in `Hh`), the inverted set of an involution `y ∉ Hh` meets each coset of `W` in `Hh` in at most
one point, hence `|invSetIn Hh y| ≤ W.relIndex Hh`. -/
theorem ncard_invSetIn_le_relIndex (Hh W : Subgroup G) [Finite G] (hWle : W ≤ Hh)
    (hWn : (W.subgroupOf Hh).Normal)
    (h5 : ∀ z : G, z * z = 1 → z ∉ Hh → invSet W z = {1})
    {y : G} (hy : y * y = 1) (hyH : y ∉ Hh) :
    (invSetIn Hh y).ncard ≤ W.relIndex Hh := by
  classical
  have hnorm : ∀ (h k : G), h ∈ W → k ∈ Hh → k * h * k⁻¹ ∈ W :=
    (Subgroup.normal_subgroupOf_iff hWle).mp hWn
  set S : Set ↥Hh := {x : ↥Hh | (x : G) ∈ invSetIn Hh y} with hS
  have hcard : (invSetIn Hh y).ncard = S.ncard := by
    refine Set.ncard_congr (fun x hx => (⟨x, hx.1⟩ : ↥Hh)) ?_ ?_ ?_
    · intro x hx; rw [hS]; simpa using hx.2
    · intro a b ha hb hab; exact congrArg Subtype.val hab
    · intro b hb; exact ⟨(b : G), hb, rfl⟩
  rw [hcard]
  have hbound : S.ncard ≤ Nat.card (↥Hh ⧸ (W.subgroupOf Hh)) := by
    have hmain := Set.ncard_le_ncard_of_injOn
      (s := S) (t := (Set.univ : Set (↥Hh ⧸ (W.subgroupOf Hh))))
      (f := fun x : ↥Hh => QuotientGroup.mk x)
      (fun x _ => Set.mem_univ _)
      (fun x hx x' hx' heq => ?_)
    · simpa using hmain
    · rw [QuotientGroup.eq] at heq
      have hmem : (x : G)⁻¹ * (x' : G) ∈ W := by
        have := Subgroup.mem_subgroupOf.mp heq
        simpa using this
      have hconj : (x' : G) * (x : G)⁻¹ ∈ W := by
        have h := hnorm ((x : G)⁻¹ * (x' : G)) (x : G) hmem x.2
        simpa [mul_assoc] using h
      exact Subtype.ext (invSetIn_eq_of_mul_inv_mem hWle h5 hy hyH hx' hx hconj).symm
  refine hbound.trans (le_of_eq ?_)
  rw [← Subgroup.index_eq_card (W.subgroupOf Hh)]
  rfl

end Work.CORE3
