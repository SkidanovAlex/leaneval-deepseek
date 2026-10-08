import Mathlib
import Submission.Work.PGroup.Basic
import Submission.Work.PGroup.thompsonJ_map_of_injective

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `J(P)` is natural under homomorphisms that are injective on `P`

If `P ⊓ f.ker = ⊥` then the restriction of `f` to `P` is injective, so it is an isomorphism
`P ≃* P.map f`.  Both `Work.PGroup.maxAbelianOrder` and `Work.PGroup.thompsonJ` are natural for
isomorphisms, whence `J(P.map f) = J(P).map f`.

Formally the statement is reduced to the injective case
`Work.PGroup.thompsonJ_map_of_injective` applied to the group `↥P` and the restricted
homomorphism `f.comp P.subtype : ↥P →* H`, together with the compatibility lemma
`Work.PGroup.thompsonJ_top_map_subtype` relating `J(⊤)` computed inside `P` to `J(P)` computed
in the ambient group.
-/

set_option linter.style.haveILetI false

namespace Work.PGroup

variable {G : Type*} [Group G]

/-- `J` commutes with viewing `P` as a group in its own right: the image of `J(⊤)` under the
subtype embedding `↥P → G` is `J(P)`. -/
theorem thompsonJ_top_map_subtype (P : Subgroup G) :
    (thompsonJ (⊤ : Subgroup P)).map P.subtype = thompsonJ P := by
  have hm : maxAbelianOrder (⊤ : Subgroup P) = maxAbelianOrder P := by
    have h := maxAbelianOrder_map_of_injective P.subtype (Subgroup.subtype_injective P)
      (⊤ : Subgroup P)
    rw [Subgroup.map_top, Subgroup.range_subtype] at h
    exact h.symm
  refine le_antisymm ?_ ?_
  · rw [Subgroup.map_le_iff_le_comap, thompsonJ, Subgroup.closure_le]
    rintro y ⟨B, -, hBcomm, hBcard, hyB⟩
    haveI : IsMulCommutative B := hBcomm
    show P.subtype y ∈ thompsonJ P
    refine le_thompsonJ ?_ (Subgroup.map_isMulCommutative B P.subtype) ?_
      (Subgroup.mem_map_of_mem P.subtype hyB)
    · intro z hz
      obtain ⟨w, -, rfl⟩ := Subgroup.mem_map.mp hz
      exact w.2
    · calc Nat.card (B.map P.subtype) = Nat.card B :=
            Subgroup.card_map_of_injective (Subgroup.subtype_injective P)
        _ = maxAbelianOrder (⊤ : Subgroup P) := hBcard
        _ = maxAbelianOrder P := hm
  · rw [thompsonJ, Subgroup.closure_le]
    rintro x ⟨A, hA, hAcomm, hAcard, hxA⟩
    have hxP : x ∈ P := hA hxA
    haveI : IsMulCommutative A := hAcomm
    refine Subgroup.mem_map.mpr ⟨⟨x, hxP⟩, ?_, rfl⟩
    have hmap : (A.comap P.subtype).map P.subtype = A := by
      rw [Subgroup.map_comap_eq_self]
      rwa [Subgroup.range_subtype]
    refine le_thompsonJ le_top
      (Subgroup.comap_injective_isMulCommutative A (Subgroup.subtype_injective P)) ?_ ?_
    · calc Nat.card (A.comap P.subtype)
          = Nat.card ((A.comap P.subtype).map P.subtype) :=
            (Subgroup.card_map_of_injective (Subgroup.subtype_injective P)).symm
        _ = Nat.card A := by rw [hmap]
        _ = maxAbelianOrder P := hAcard
        _ = maxAbelianOrder (⊤ : Subgroup P) := hm.symm
    · show x ∈ A
      exact hxA

/-- `J(P)` is natural for homomorphisms that are injective on `P`: if `P ⊓ f.ker = ⊥`, then
`J(P.map f) = J(P).map f`.  Restricted to `P`, such an `f` is an isomorphism onto `P.map f`. -/
theorem thompsonJ_map_of_ker_inf_eq_bot {G H : Type*} [Group G] [Group H] (f : G →* H)
    (P : Subgroup G) (hker : P ⊓ f.ker = ⊥) :
    Work.PGroup.thompsonJ (P.map f) = (Work.PGroup.thompsonJ P).map f := by
  have hf : Function.Injective (f.comp P.subtype) := by
    intro x y hxy
    have hxy' : f (x : G) = f (y : G) := hxy
    have hmem : (x : G) * (y : G)⁻¹ ∈ P ⊓ f.ker := by
      refine ⟨P.mul_mem x.2 (P.inv_mem y.2), ?_⟩
      exact MonoidHom.mem_ker.mpr (by rw [map_mul, map_inv, hxy', mul_inv_cancel])
    have h1 : (x : G) * (y : G)⁻¹ = 1 := (Subgroup.eq_bot_iff_forall _).mp hker _ hmem
    exact Subtype.ext (mul_inv_eq_one.mp h1)
  have htop : (⊤ : Subgroup P).map P.subtype = P := by
    rw [Subgroup.map_top, Subgroup.range_subtype]
  have hstep : (⊤ : Subgroup P).map (f.comp P.subtype) = P.map f := by
    rw [← Subgroup.map_map (K := (⊤ : Subgroup P)) (g := f) (f := P.subtype), htop]
  have key := thompsonJ_map_of_injective (f.comp P.subtype) hf (⊤ : Subgroup P)
  rw [← hstep, ← thompsonJ_top_map_subtype P, Subgroup.map_map]
  exact key

end Work.PGroup
