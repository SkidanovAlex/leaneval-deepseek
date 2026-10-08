import Mathlib
import Submission.Work.CORE3.Defs

/-!
# CORE3: an element of order `3` acting fixed-point-freely on a four-group

`Work.CORE3.FourGroupOrderThreeFixed`: if `V` is a Klein four-group (`|V| = 4` and every
element of `V` an involution), `x` normalizes `V`, `orderOf x = 3` and `x` does **not**
centralize `V`, then `C_V(x) = V ⊓ C_G(x) = ⊥`.

Informal proof.  Since `x` has order `3`, the conjugation action of `x` on `V` is an
automorphism `φ` of `V` with `φ³ = 1`; and `φ ≠ 1` because `x ∉ C_G(V)`.

Assume `w ∈ C_V(x)`, `w ≠ 1`, and pick `v ∈ V` with `x v ≠ v x`.  Then `1, v, w` are three
distinct nonidentity elements of the four-element group `V`, so `V = {1, v, w, v w}`.  As
`x` normalizes `V`, the element `u = x v x⁻¹` lies in `V`, and it is not `1` (else `v = 1`),
not `v` (else `x v = v x`) and not `w` (else `v = w`); hence `u = v w`.

Now `x * w * x⁻¹ = w` and `x * v * x⁻¹ = v * w` give
`(x * x) * v * (x * x)⁻¹ = (x v x⁻¹)(x w x⁻¹) = (v w) w = v` and
`(x * x) * w * (x * x)⁻¹ = w`, so `x * x` centralizes every element of `V`, i.e.
`x * x ∈ C_G(V)`.  Finally `x³ = 1` gives `x = (x * x)⁻¹ ∈ C_G(V)`, contradicting
`x ∉ C_G(V)`.

Hence `C_V(x)` is trivial.

The only auxiliary input is the elementary `fourGroup_eq_four`, proved below: in a Klein
four-group, two distinct nonidentity elements `a, b` generate it, i.e. `V = {1, a, b, a b}`.
-/

namespace Work.CORE3

open Subgroup

/-- The element structure of a Klein four-group.  If `V` satisfies `Nat.card V = 4` and
every element of `V` is an involution and `a, b ∈ V` are distinct nonidentity elements, then
`V = {1, a, b, a * b}`. -/
lemma fourGroup_eq_four {G : Type} [Group G] [Finite G] {V : Subgroup G} (hcard : Nat.card V = 4)
    (hsq : ∀ v ∈ V, v ^ 2 = 1) {a b : G}
    (ha : a ∈ V) (hb : b ∈ V) (ha1 : a ≠ 1) (hb1 : b ≠ 1) (hab : a ≠ b) :
    (V : Set G) = {1, a, b, a * b} := by
  have hb2 : b * b = 1 := by simpa [pow_two] using hsq b hb
  have hab1 : a * b ≠ 1 := by
    intro h
    exact hab (mul_right_cancel (show a * b = b * b by rw [h, hb2]))
  have haba : a * b ≠ a := by
    intro h
    exact hb1 (mul_left_cancel (show a * b = a * 1 by rw [h, mul_one]))
  have habb : a * b ≠ b := by
    intro h
    exact ha1 (mul_right_cancel (show a * b = 1 * b by rw [h, one_mul]))
  have hncard : ({1, a, b, a * b} : Set G).ncard = 4 := by
    have h1 : (1 : G) ∉ ({a, b, a * b} : Set G) := by
      intro hmem
      rcases (Set.mem_insert_iff.mp hmem) with h | h
      · exact ha1 h.symm
      · rcases (Set.mem_insert_iff.mp h) with h | h
        · exact hb1 h.symm
        · exact hab1 (Set.mem_singleton_iff.mp h).symm
    have h2 : a ∉ ({b, a * b} : Set G) := by
      intro hmem
      rcases (Set.mem_insert_iff.mp hmem) with h | h
      · exact hab h
      · exact haba (Set.mem_singleton_iff.mp h).symm
    have h3 : b ∉ ({a * b} : Set G) := by
      intro hmem
      exact habb (Set.mem_singleton_iff.mp hmem).symm
    rw [Set.ncard_insert_of_notMem h1, Set.ncard_insert_of_notMem h2,
      Set.ncard_insert_of_notMem h3, Set.ncard_singleton]
  have hsub : ({1, a, b, a * b} : Set G) ⊆ V := by
    intro x hx
    rcases (Set.mem_insert_iff.mp hx) with h | h
    · rw [h]; exact V.one_mem
    · rcases (Set.mem_insert_iff.mp h) with h | h
      · rw [h]; exact ha
      · rcases (Set.mem_insert_iff.mp h) with h | h
        · rw [h]; exact hb
        · rw [Set.mem_singleton_iff.mp h]; exact V.mul_mem ha hb
  have hVncard : (V : Set G).ncard = 4 := by
    rw [← Nat.card_coe_set_eq]; exact hcard
  exact (Set.eq_of_subset_of_ncard_le hsub (by rw [hVncard, hncard])).symm

theorem FourGroupOrderThreeFixed {G : Type} [Group G] [Finite G] {V : Subgroup G} {x : G}
    (hV4 : Work.GW2.IsFourGroup V)
    (hxN : x ∈ Subgroup.normalizer (V : Set G))
    (hx3 : orderOf x = 3)
    (hxnc : x ∉ Subgroup.centralizer (V : Set G)) :
    V ⊓ Subgroup.centralizer ({x} : Set G) = ⊥ := by
  rw [Subgroup.eq_bot_iff_forall]
  intro w hw
  rw [Subgroup.mem_inf] at hw
  obtain ⟨hwV, hwC⟩ := hw
  by_contra hw1
  -- `x ^ 3 = 1`
  have hx3' : x ^ 3 = 1 := by
    have h := pow_orderOf_eq_one x
    rwa [hx3] at h
  -- `x` commutes with `w`
  have hwx : x * w = w * x := (Subgroup.mem_centralizer_iff.mp hwC) x (by simp)
  have hxw : x * w * x⁻¹ = w := by
    rw [hwx, mul_assoc, mul_inv_cancel, mul_one]
  have hw2 : w * w = 1 := by simpa [pow_two] using hV4.2 w hwV
  -- some `v ∈ V` with `x * v ≠ v * x`
  have hxnc' : ∃ v ∈ V, x * v ≠ v * x := by
    by_contra h
    simp only [not_exists, not_and] at h
    exact hxnc (Subgroup.mem_centralizer_iff.mpr (fun y hy => (not_not.mp (h y hy)).symm))
  obtain ⟨v, hvV, hvx⟩ := hxnc'
  have hv1 : v ≠ 1 := by
    intro h
    apply hvx
    rw [h, mul_one, one_mul]
  have hvw : v ≠ w := by
    intro h
    exact hvx (by rw [h]; exact hwx)
  have huV : x * v * x⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.mp hxN v).mp hvV
  -- `V = {1, v, w, v * w}`
  have hVset : (V : Set G) = {1, v, w, v * w} :=
    fourGroup_eq_four hV4.1 hV4.2 hvV hwV hv1 hw1 hvw
  have hu_mem : x * v * x⁻¹ ∈ ({1, v, w, v * w} : Set G) := hVset ▸ huV
  -- hence `x * v * x⁻¹ = v * w`
  have hu_eq : x * v * x⁻¹ = v * w := by
    rcases (Set.mem_insert_iff.mp hu_mem) with h | h
    · exfalso
      apply hv1
      have hxveq : x * v = x * 1 := by
        rw [mul_one]
        calc x * v = x * v * x⁻¹ * x := by group
          _ = 1 * x := by rw [h]
          _ = x := one_mul x
      exact mul_left_cancel hxveq
    · rcases (Set.mem_insert_iff.mp h) with h | h
      · exfalso
        apply hvx
        calc x * v = x * v * x⁻¹ * x := by group
          _ = v * x := by rw [h]
      · rcases (Set.mem_insert_iff.mp h) with h | h
        · exfalso
          apply hvw
          have hxveq : x * v = x * w := by
            calc x * v = x * v * x⁻¹ * x := by group
              _ = w * x := by rw [h]
              _ = x * w := hwx.symm
          exact mul_left_cancel hxveq
        · exact Set.mem_singleton_iff.mp h
  -- `x * x` fixes `v` and `w`, hence all of `V`
  have hyv : (x * x) * v * (x * x)⁻¹ = v := by
    calc (x * x) * v * (x * x)⁻¹ = x * (x * v * x⁻¹) * x⁻¹ := by group
      _ = x * (v * w) * x⁻¹ := by rw [hu_eq]
      _ = (x * v * x⁻¹) * (x * w * x⁻¹) := by group
      _ = (v * w) * w := by rw [hu_eq, hxw]
      _ = v := by rw [mul_assoc, hw2, mul_one]
  have hyw : (x * x) * w * (x * x)⁻¹ = w := by
    calc (x * x) * w * (x * x)⁻¹ = x * (x * w * x⁻¹) * x⁻¹ := by group
      _ = x * w * x⁻¹ := by rw [hxw]; exact hxw
      _ = w := hxw
  have hyc : ∀ y ∈ V, (x * x) * y * (x * x)⁻¹ = y := by
    intro y hy
    have hyc : y ∈ ({1, v, w, v * w} : Set G) := hVset ▸ hy
    rcases (Set.mem_insert_iff.mp hyc) with h | h
    · rw [h]; group
    · rcases (Set.mem_insert_iff.mp h) with h | h
      · rw [h]; exact hyv
      · rcases (Set.mem_insert_iff.mp h) with h | h
        · rw [h]; exact hyw
        · rw [Set.mem_singleton_iff.mp h]
          have e1 : (x * x) * (v * w) * (x * x)⁻¹ =
              ((x * x) * v * (x * x)⁻¹) * ((x * x) * w * (x * x)⁻¹) := by group
          rw [e1, hyv, hyw]
  have hyC : x * x ∈ Subgroup.centralizer (V : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have h := hyc y hy
    calc y * (x * x) = ((x * x) * y * (x * x)⁻¹) * (x * x) := by rw [h]
      _ = (x * x) * y := by group
  -- `x = (x * x)⁻¹`, so `x ∈ C_G(V)`: contradiction
  have hx_eq : x = (x * x)⁻¹ := by
    apply eq_inv_of_mul_eq_one_right
    have e : (x * x) * x = x ^ 3 := by rw [← pow_two x, ← pow_succ x 2]
    rw [e, hx3']
  have hxmem : x ∈ Subgroup.centralizer (V : Set G) := by
    rw [hx_eq]
    exact Subgroup.inv_mem _ hyC
  exact hxnc hxmem

end Work.CORE3
