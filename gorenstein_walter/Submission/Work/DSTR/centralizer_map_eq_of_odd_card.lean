import Mathlib
import Submission.Work.ASM.Defs

namespace Work.DSTR

set_option linter.style.haveILetI false

/-- **Centralizers of involutions in a quotient by a normal odd-order subgroup.**  (Bender 1981, 1.3 with `P = ⟨t⟩`.)  If `N ◁ G` has odd order and `t ∈ G` is an involution, then the centralizer of `tN` in `G ⧸ N` is exactly the image of `C_G(t)`. -/
theorem centralizer_map_eq_of_odd_card {G : Type*} [Group G] [Finite G]
    (N : Subgroup G) [N.Normal] (hN : Odd (Nat.card N)) (t : G) (ht : orderOf t = 2) :
    (Subgroup.centralizer ({t} : Set G)).map (QuotientGroup.mk' N) =
      Subgroup.centralizer ({(QuotientGroup.mk' N) t} : Set (G ⧸ N)) := by
  classical
  -- `t` is an involution
  have ht2 : t * t = 1 := by
    have h := pow_orderOf_eq_one t
    rw [ht, pow_two] at h
    exact h
  -- An element of `G` lies in `N` iff its image in `G ⧸ N` is trivial.
  have hker : ∀ x : G, (QuotientGroup.mk' N) x = 1 ↔ x ∈ N := by
    intro x
    rw [QuotientGroup.mk'_apply]
    exact QuotientGroup.eq_one_iff x
  refine le_antisymm ?_ ?_
  · -- `C_G(t) N / N` is always contained in the centralizer of `tN`.
    have h := Subgroup.map_centralizer_le_centralizer_image ({t} : Set G) (QuotientGroup.mk' N)
    simpa using h
  · -- Conversely, if `gN` centralizes `tN`, then the coset `gN` meets `C_G(t)`.
    intro y hy
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective N y
    have hcomm : (QuotientGroup.mk' N) t * (QuotientGroup.mk' N) g
        = (QuotientGroup.mk' N) g * (QuotientGroup.mk' N) t :=
      Subgroup.mem_centralizer_iff.mp hy _ (Set.mem_singleton _)
    have hqt2 : (QuotientGroup.mk' N) t * (QuotientGroup.mk' N) t = 1 := by
      rw [← map_mul, ht2, map_one]
    -- The coset `gN`, as a finite type.
    let S := {x : G // (QuotientGroup.mk' N) x = (QuotientGroup.mk' N) g}
    letI : Fintype S := Fintype.ofFinite S
    -- `gN ≃ N`, so `#(gN) = #N` is odd.
    let e : N ≃ S :=
      { toFun := fun n => ⟨g * (n : G), by
          rw [map_mul, (hker (n : G)).mpr n.2, mul_one]⟩
        invFun := fun x => ⟨g⁻¹ * (x : G), by
          rw [← hker, map_mul, map_inv, x.2, inv_mul_cancel]⟩
        left_inv := by
          intro n
          apply Subtype.ext
          change g⁻¹ * (g * (n : G)) = (n : G)
          rw [← mul_assoc, inv_mul_cancel, one_mul]
        right_inv := by
          intro x
          apply Subtype.ext
          change g * (g⁻¹ * (x : G)) = (x : G)
          rw [← mul_assoc, mul_inv_cancel, one_mul] }
    have hcardS : ¬ 2 ∣ Fintype.card S := by
      have h1 : Nat.card N % 2 = 1 := Nat.odd_iff.mp hN
      rw [← Nat.card_eq_fintype_card, ← Nat.card_congr e]
      intro h
      rw [Nat.dvd_iff_mod_eq_zero] at h
      omega
    -- Conjugation by `t` acts as an involution on the coset `gN`.
    let σfun : S → S := fun x => ⟨t * (x : G) * t, by
      rw [map_mul, map_mul, x.2, hcomm, mul_assoc, hqt2, mul_one]⟩
    have hinv : Function.Involutive σfun := by
      intro x
      apply Subtype.ext
      change t * (t * (x : G) * t) * t = (x : G)
      have hh : t * (t * (x : G) * t) * t = (t * t) * (x : G) * (t * t) := by group
      rw [hh, ht2]
      simp
    have hσ2 : (Function.Involutive.toPerm σfun hinv) ^ 2 = 1 := by
      refine Equiv.Perm.ext (fun x => ?_)
      simp only [pow_two, Equiv.Perm.mul_apply, Equiv.Perm.one_apply]
      exact hinv x
    -- An involution of a set of odd cardinality has a fixed point.
    obtain ⟨x, hx⟩ := Equiv.Perm.exists_fixed_point_of_prime (p := 2) (n := 1) hcardS hσ2
    have hxval : t * (x : G) * t = (x : G) := by
      simpa using Subtype.ext_iff.mp hx
    -- The fixed point of the coset lies in `C_G(t)` and represents `gN`.
    refine Subgroup.mem_map.mpr ⟨(x : G), ?_, x.2⟩
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff] at hh
    rw [hh]
    have h1 : t * (x : G) * t * t = t * (x : G) := by rw [mul_assoc, ht2, mul_one]
    calc t * (x : G) = t * (x : G) * t * t := h1.symm
      _ = (x : G) * t := by rw [hxval]

end Work.DSTR
