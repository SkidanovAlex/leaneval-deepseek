import Mathlib
import Submission.Work.CORE2A.Defs
import Submission.Work.ASM.oddCore_odd

/-!
# `O(M) ≤ O(K)` for `M ◁ K`

Let `M, K` be subgroups of a finite group `G` with `M ≤ K` and `M` normal in `K`.  Then the odd
core `O(M) = O_{2'}(M)` of `M`, transported into `G` as `oddCoreIn M`, is contained in
`oddCoreIn K`.

The mathematical content is the standard one:

* `O(M)` is **characteristic** in `M` (it is "the largest normal subgroup of odd order", a
  property respected by every automorphism of `M`), so every automorphism of `M` — in
  particular conjugation by an element `k ∈ K`, which restricts to an automorphism of `M`
  because `M ◁ K` — preserves `O(M)`.  Hence `oddCoreIn M` is normalised by `K`, i.e.
  `(oddCoreIn M).subgroupOf K` is normal in `↥K`.
* `|O(M)|` is odd (`Work.ASM.oddCore_odd`), so `(oddCoreIn M).subgroupOf K` is a normal
  subgroup of `↥K` of odd order.
* By maximality of `O(K)` (the largest normal subgroup of `↥K` of odd order) it is contained
  in `O(K)`, and pulling back along `K.subtype` gives `oddCoreIn M ≤ oddCoreIn K`.
-/

namespace Work.CORE2A

open Subgroup

/-- **Maximality of `O(H)`.** Every normal subgroup of `H` of odd order lies in `O(H)`.

This is the universal property of `O(H) = (sSup {N | N.Normal ∧ Odd (Nat.card N)}).normalCore`
coming straight from the definition: a normal odd-order subgroup already belongs to the family
whose supremum is taken, so it lies in the supremum and (being normal) in its `normalCore`. -/
private theorem oddCoreIn_le_aux_max {H : Type*} [Group H] {N : Subgroup H} (hnorm : N.Normal)
    (hodd : Odd (Nat.card N)) : N ≤ Work.GW2.oddCore H := by
  have := hnorm
  exact Subgroup.normal_le_normalCore.mpr (le_sSup ⟨hnorm, hodd⟩)

/-- `O(H)` is stable under the image along an automorphism of `H`, one inclusion: the image of
`O(H)` is normal (the automorphism is surjective) of odd order (it is injective), so maximality
puts it inside `O(H)`. -/
private theorem oddCoreIn_le_aux_map_aut_le {H : Type*} [Group H] [Finite H] (e : H ≃* H) :
    (Work.GW2.oddCore H).map e.toMonoidHom ≤ Work.GW2.oddCore H :=
  oddCoreIn_le_aux_max ((Work.GW2.oddCore_normal H).map e.toMonoidHom e.surjective)
    (by rw [Subgroup.card_map_of_injective e.injective]; exact Work.ASM.oddCore_odd H)

/-- `O(H)` is invariant under automorphisms of `H`. -/
private theorem oddCoreIn_le_aux_map_aut {H : Type*} [Group H] [Finite H] (e : H ≃* H) :
    (Work.GW2.oddCore H).map e.toMonoidHom = Work.GW2.oddCore H := by
  refine le_antisymm (oddCoreIn_le_aux_map_aut_le e) ?_
  calc (Work.GW2.oddCore H)
      = (Work.GW2.oddCore H).map (MonoidHom.id H) := (Subgroup.map_id _).symm
    _ = (Work.GW2.oddCore H).map (e.toMonoidHom.comp e.symm.toMonoidHom) := by
          congr 1
          ext x
          simp
    _ = ((Work.GW2.oddCore H).map e.symm.toMonoidHom).map e.toMonoidHom :=
          (Subgroup.map_map _ _ _).symm
    _ ≤ (Work.GW2.oddCore H).map e.toMonoidHom :=
          Subgroup.map_mono (oddCoreIn_le_aux_map_aut_le e.symm)

theorem oddCoreIn_le_oddCoreIn_of_normal {G : Type} [Group G] [Finite G] {M K : Subgroup G}
    (hMK : M ≤ K) (hn : (M.subgroupOf K).Normal) :
    Work.GW2.oddCoreIn M ≤ Work.GW2.oddCoreIn K := by
  -- Conjugation by elements of `K` preserves `M`.
  have hniff : ∀ h k : G, h ∈ M → k ∈ K → k * h * k⁻¹ ∈ M :=
    (Subgroup.normal_subgroupOf_iff hMK).mp hn
  have hAK : Work.GW2.oddCoreIn M ≤ K := by
    rw [Work.GW2.oddCoreIn]
    exact (Subgroup.map_subtype_le (Work.GW2.oddCore ↥M)).trans hMK
  -- `oddCoreIn M` is invariant under conjugation by elements of `K`.
  have hInv : ∀ h ∈ Work.GW2.oddCoreIn M, ∀ k ∈ K, k * h * k⁻¹ ∈ Work.GW2.oddCoreIn M := by
    intro h hh k hk
    rw [Work.GW2.oddCoreIn] at hh ⊢
    have hhM : h ∈ M := Subgroup.map_subtype_le (Work.GW2.oddCore ↥M) hh
    have hhO : (⟨h, hhM⟩ : ↥M) ∈ Work.GW2.oddCore ↥M := by
      obtain ⟨m, hm, hmh⟩ := Subgroup.mem_map.mp hh
      have hme : m = ⟨h, hhM⟩ := Subtype.ext hmh
      exact hme ▸ hm
    -- The automorphism of `↥M` given by conjugation with `k`.
    have hconj : ∀ m : ↥M, k * (m : G) * k⁻¹ ∈ M := fun m => hniff m.1 k m.2 hk
    have hconj' : ∀ m : ↥M, k⁻¹ * (m : G) * (k⁻¹)⁻¹ ∈ M :=
      fun m => hniff m.1 k⁻¹ m.2 (K.inv_mem hk)
    let φ : ↥M ≃* ↥M :=
      { toFun := fun m => ⟨k * (m : G) * k⁻¹, hconj m⟩
        invFun := fun m => ⟨k⁻¹ * (m : G) * (k⁻¹)⁻¹, hconj' m⟩
        left_inv := fun m => Subtype.ext (by group)
        right_inv := fun m => Subtype.ext (by group)
        map_mul' := fun a b => Subtype.ext (by simp only [Subgroup.coe_mul]; group) }
    have hφ : (Work.GW2.oddCore ↥M).map φ.toMonoidHom = Work.GW2.oddCore ↥M :=
      oddCoreIn_le_aux_map_aut φ
    have hφval : φ (⟨h, hhM⟩ : ↥M) = ⟨k * h * k⁻¹, hconj ⟨h, hhM⟩⟩ := rfl
    have hmem : φ (⟨h, hhM⟩ : ↥M) ∈ Work.GW2.oddCore ↥M := by
      have h1 : φ (⟨h, hhM⟩ : ↥M) ∈ (Work.GW2.oddCore ↥M).map φ.toMonoidHom :=
        Subgroup.mem_map.mpr ⟨⟨h, hhM⟩, hhO, rfl⟩
      rwa [hφ] at h1
    exact Subgroup.mem_map.mpr ⟨⟨k * h * k⁻¹, hconj ⟨h, hhM⟩⟩, hφval ▸ hmem, rfl⟩
  -- `(oddCoreIn M).subgroupOf K` is a normal subgroup of `↥K` of odd order.
  have hAnorm : ((Work.GW2.oddCoreIn M).subgroupOf K).Normal :=
    (Subgroup.normal_subgroupOf_iff hAK).mpr fun h k hh hk => hInv h hh k hk
  have hcard1 : Nat.card ↥((Work.GW2.oddCoreIn M).subgroupOf K) =
      Nat.card ↥(Work.GW2.oddCoreIn M) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAK).toEquiv
  have hcard2 : Nat.card ↥(Work.GW2.oddCoreIn M) = Nat.card ↥(Work.GW2.oddCore ↥M) := by
    rw [Work.GW2.oddCoreIn]
    exact Subgroup.card_map_of_injective M.subtype_injective
  have hAodd : Odd (Nat.card ↥((Work.GW2.oddCoreIn M).subgroupOf K)) := by
    rw [hcard1, hcard2]
    exact Work.ASM.oddCore_odd ↥M
  have hAle : (Work.GW2.oddCoreIn M).subgroupOf K ≤ Work.GW2.oddCore ↥K :=
    oddCoreIn_le_aux_max hAnorm hAodd
  -- Transport back along `K.subtype`.
  intro x hx
  have hxK : x ∈ K := hAK hx
  have hxN : (⟨x, hxK⟩ : ↥K) ∈ (Work.GW2.oddCoreIn M).subgroupOf K :=
    Subgroup.mem_subgroupOf.mpr hx
  have hxO : (⟨x, hxK⟩ : ↥K) ∈ Work.GW2.oddCore ↥K := hAle hxN
  rw [Work.GW2.oddCoreIn]
  exact Subgroup.mem_map.mpr ⟨⟨x, hxK⟩, hxO, rfl⟩

end Work.CORE2A
