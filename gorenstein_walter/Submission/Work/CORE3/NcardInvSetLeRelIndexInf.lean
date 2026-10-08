import Mathlib
import Submission.Work.CORE3.CosetInvCountBasic

namespace Work.CORE3

theorem NcardInvSetLeRelIndexInf {G : Type} [Group G] [Finite G]
    (Hh W D : Subgroup G) (hWle : W ≤ Hh) (hDle : D ≤ Hh) (hWn : (W.subgroupOf Hh).Normal)
    (h5 : ∀ z : G, z * z = 1 → z ∉ Hh → Work.GW2.invSet W z = {1})
    {y : G} (hy : y * y = 1) (hyH : y ∉ Hh) (hsub : Work.CORE3.invSetIn Hh y ⊆ D) :
    (Work.CORE3.invSetIn Hh y).ncard ≤ (W ⊓ D).relIndex D := by
  classical
  -- `W` is normal in `Hh`: conjugation by an element of `Hh` preserves `W`.
  have hnorm : ∀ (h k : G), h ∈ W → k ∈ Hh → k * h * k⁻¹ ∈ W :=
    (Subgroup.normal_subgroupOf_iff hWle).mp hWn
  -- `W ⊓ D` is normal in `D` (intersect the normal `W` with `D ≤ Hh`).
  have hW'le : W ⊓ D ≤ D := inf_le_right
  have hW'n : ((W ⊓ D).subgroupOf D).Normal :=
    (Subgroup.normal_subgroupOf_iff hW'le).mpr (fun h k hh hk => by
      have hhW : h ∈ W := hh.1
      have hhD : h ∈ D := hh.2
      exact ⟨hnorm h k hhW (hDle hk), D.mul_mem (D.mul_mem hk hhD) (D.inv_mem hk)⟩)
  -- Transport `invSetIn Hh y` (which is contained in `D`) to a set of the subtype `↥D`.
  set S : Set ↥D := {x : ↥D | (x : G) ∈ invSetIn Hh y} with hS
  have hcard : (invSetIn Hh y).ncard = S.ncard := by
    refine Set.ncard_congr (fun x hx => (⟨x, hsub hx⟩ : ↥D)) ?_ ?_ ?_
    · intro x hx; exact hx
    · intro a b ha hb hab; exact congrArg Subtype.val hab
    · intro b hb; exact ⟨(b : G), hb, Subtype.ext rfl⟩
  rw [hcard]
  -- Count cosets of `W ⊓ D` in `D`: the reduction map is injective on `S`.
  have hbound : S.ncard ≤ Nat.card (↥D ⧸ ((W ⊓ D).subgroupOf D)) := by
    have hinj : Set.InjOn (fun x : ↥D => (QuotientGroup.mk x : ↥D ⧸ ((W ⊓ D).subgroupOf D))) S := by
      intro x hx x' hx' heq
      rw [QuotientGroup.eq] at heq
      have hmem : (x : G)⁻¹ * (x' : G) ∈ W := by
        have h := (Subgroup.mem_subgroupOf.mp heq).1
        simpa using h
      -- Conjugating by `x ∈ D ⊆ Hh` puts the quotient in `W`.
      have hconj : (x' : G) * (x : G)⁻¹ ∈ W := by
        have h := hnorm ((x : G)⁻¹ * (x' : G)) (x : G) hmem (hDle x.2)
        rwa [show (x : G) * ((x : G)⁻¹ * (x' : G)) * (x : G)⁻¹
              = (x' : G) * (x : G)⁻¹ from by group] at h
      -- Bender 1.4 injectivity modulo `W` forces `x = x'`.
      exact Subtype.ext (invSetIn_eq_of_mul_inv_mem hWle h5 hy hyH hx' hx hconj).symm
    have hmain := Set.ncard_le_ncard_of_injOn
      (s := S) (t := (Set.univ : Set (↥D ⧸ ((W ⊓ D).subgroupOf D))))
      (fun x : ↥D => (QuotientGroup.mk x : ↥D ⧸ ((W ⊓ D).subgroupOf D)))
      (fun x _ => Set.mem_univ _) hinj
    simpa using hmain
  refine hbound.trans (le_of_eq ?_)
  rw [← Subgroup.index_eq_card ((W ⊓ D).subgroupOf D)]
  rfl

end Work.CORE3
