/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gorenstein–Walter formalisation team (area BSW, the `|K| = 4` case)

# Bender's Case 1: no involution outside `H = C_G(X)⟨t⟩` inverts `A = C_G(X)`

Let `G` be a finite group in which every involution centralizer is dihedral of order `8` and all
involutions are conjugate (`Work.BSW.Cases.K4.K4Hyp`), let `X ≤ G` have order `3` and let `t` be an
involution normalizing `X`.  Put `A = C_G(X)`, `H = A⟨t⟩`.

If `u` is an involution outside `H` and `a ∉ {1}` lies in `A`, then `u a u⁻¹ ≠ a⁻¹`: the inversion
of `A` is realized only by the involutions of the coset `A t`.

The proof is short.  Hypothesizing `u a u⁻¹ = a⁻¹`:

* `Z = C_G(a)` has odd order (`a` has odd order, and a `2`-element of `Z` would force the odd
  number `orderOf a` to divide `8`),
* `u` normalizes `Z` and has no nontrivial fixed point on it (a fixed point centralizes `u`, so has
  order dividing `8`), so the fixed-point-free-involution theorem inverts all of `Z`;
* `X ≤ A ≤ Z` (as `A` is abelian), so `u` inverts every element of `X`; since `t` inverts every
  element of `A ⊇ X` as well, `t⁻¹ * u` centralizes `X`, i.e. `t⁻¹ * u ∈ A`, whence
  `u = t * (t⁻¹ * u) ∈ H`, contradiction.
-/
import Mathlib
import Submission.Work.BSW.Cases.K4.case1Aux

namespace Work.BSW.Cases.K4

open Subgroup

/-- `C_G(a) = C_G(a⁻¹)`. -/
theorem cent_inv_eq {G : Type} [Group G] (a : G) : cent G a⁻¹ = cent G a := by
  unfold cent
  ext x
  rw [Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_centralizer_singleton_iff]
  exact Commute.inv_right_iff

/-- An involution `u` with `u a u⁻¹ = a⁻¹` normalizes `C_G(a)`. -/
theorem mem_normalizer_cent_of_conj_eq_inv {G : Type} [Group G] [Finite G] {u a : G}
    (hu2 : orderOf u = 2)
    (hconj : u * a * u⁻¹ = a⁻¹) : u ∈ Subgroup.normalizer (cent G a : Set G) := by
  have hu2mul : u * u = 1 := by rw [← pow_two, ← hu2]; exact pow_orderOf_eq_one u
  have hu_inv : u⁻¹ = u := inv_eq_of_mul_eq_one_right hu2mul
  have hmap : (cent G a).map (MulAut.conj u).toMonoidHom = cent G a := by
    rw [map_conj_cent u a, hconj, cent_inv_eq]
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    have hmem : u * x * u⁻¹ ∈ (cent G a).map (MulAut.conj u).toMonoidHom :=
      ⟨x, hx, by simp [MulAut.conj_apply]⟩
    rwa [hmap] at hmem
  · intro hx
    have hmem : u * x * u⁻¹ ∈ (cent G a).map (MulAut.conj u).toMonoidHom := by
      rw [hmap]; exact hx
    obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp hmem
    have hyx' : u * y * u⁻¹ = u * x * u⁻¹ := by simpa [MulAut.conj_apply] using hyx
    have h1 : u * y = u * x := by
      have h := congrArg (fun z => z * u) hyx'
      simpa [mul_assoc, hu_inv] using h
    rw [← mul_left_cancel h1]
    exact hy

/-- An involution `u` with `u a u⁻¹ = a⁻¹` inverts the whole centralizer of `a`, provided that this
centralizer has odd order. -/
theorem conj_eq_inv_on_cent_of_conj_eq_inv {G : Type} [Group G] [Finite G] {u a : G}
    (hu2 : orderOf u = 2)
    (hconj : u * a * u⁻¹ = a⁻¹) (hZodd : Odd (Nat.card ↥(cent G a)))
    (hcard8 : Nat.card ↥(cent G u) = 8) :
    ∀ x ∈ cent G a, u * x * u⁻¹ = x⁻¹ := by
  have hu2mul : u * u = 1 := by rw [← pow_two, ← hu2]; exact pow_orderOf_eq_one u
  have hmap : (cent G a).map (MulAut.conj u).toMonoidHom = cent G a := by
    rw [map_conj_cent u a, hconj, cent_inv_eq]
  -- conjugation by `u` as an endomorphism of `↥(C_G(a))`
  let φ : ↥(cent G a) →* ↥(cent G a) :=
    { toFun := fun x => ⟨u * (x : G) * u⁻¹, by
        have hmem : u * (x : G) * u⁻¹ ∈ (cent G a).map (MulAut.conj u).toMonoidHom :=
          ⟨x, x.2, by simp [MulAut.conj_apply]⟩
        rwa [hmap] at hmem⟩
      map_one' := by ext; simp
      map_mul' := by intro x y; ext; simp only [Subgroup.coe_mul]; group }
  have hφcoe : ∀ x : ↥(cent G a), ((φ x : ↥(cent G a)) : G) = u * (x : G) * u⁻¹ := fun x => rfl
  have hinvol : Function.Involutive ⇑φ := by
    intro x
    apply Subtype.ext
    rw [hφcoe, hφcoe]
    rw [show u * (u * (x : G) * u⁻¹) * u⁻¹ = (u * u) * (x : G) * (u⁻¹ * u⁻¹) from by group,
      show u⁻¹ * u⁻¹ = (u * u)⁻¹ from by group, hu2mul, inv_one, mul_one, one_mul]
  have hfp : MonoidHom.FixedPointFree ⇑φ := by
    intro x hx
    apply Subtype.ext
    have h1 : ((φ x : ↥(cent G a)) : G) = u * (x : G) * u⁻¹ := hφcoe x
    have h2 : ((φ x : ↥(cent G a)) : G) = (x : G) := congrArg Subtype.val hx
    rw [h1] at h2
    -- `x` commutes with `u`, so its order divides `8`; it also divides the odd number `|C_G(a)|`
    have hxc : (x : G) ∈ cent G u := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      calc (x : G) * u = (u * (x : G) * u⁻¹) * u := by rw [h2]
        _ = u * (x : G) := by rw [mul_assoc, inv_mul_cancel, mul_one]
    have hdvd8 : orderOf (x : G) ∣ 8 := by
      have hh := orderOf_dvd_natCard_of_mem hxc
      rwa [hcard8] at hh
    have hdvdZ : orderOf (x : G) ∣ Nat.card ↥(cent G a) := orderOf_dvd_natCard_of_mem x.2
    have hodd : Odd (orderOf (x : G)) := hZodd.of_dvd_nat hdvdZ
    exact orderOf_eq_one_iff.mp (eq_one_of_dvd_eight_of_odd hdvd8 hodd)
  have hφinv := MonoidHom.FixedPointFree.coe_eq_inv_of_involutive hfp hinvol
  intro x hx
  have h2 := congrArg Subtype.val (congrFun hφinv ⟨x, hx⟩)
  rw [hφcoe] at h2
  simpa using h2

theorem case1A_inv_trivial {G : Type} [Group G] [Finite G] (h : Work.BSW.Cases.K4.K4Hyp G)
    (X : Subgroup G) (t : G) (hX3 : Nat.card ↥X = 3) (ht2 : orderOf t = 2)
    (htN : t ∈ Subgroup.normalizer (X : Set G)) {u a : G} (hu2 : orderOf u = 2)
    (huH : u ∉ Work.BSW.Cases.K4.case1H X t) (ha : a ∈ Work.BSW.Cases.K4.case1A X)
    (ha1 : a ≠ 1) : u * a * u⁻¹ ≠ a⁻¹ := by
  intro hconj
  have hAu := case1A_comm_and_inv h hX3 ht2 htN
  have hAcomm : ∀ y ∈ case1A X, ∀ z ∈ case1A X, y * z = z * y := hAu.1
  have hAtinv : ∀ y ∈ case1A X, t * y * t⁻¹ = y⁻¹ := hAu.2
  have hAodd : Odd (Nat.card ↥(case1A X)) := case1A_odd h hX3
  have haodd : Odd (orderOf a) := hAodd.of_dvd_nat (orderOf_dvd_natCard_of_mem ha)
  have haord1 : orderOf a ≠ 1 := fun h1 => ha1 (orderOf_eq_one_iff.mp h1)
  -- `Z = C_G(a)` has odd order
  have hZodd : Odd (Nat.card ↥(cent G a)) := by
    by_contra hodd
    rw [Nat.not_odd_iff_even, even_iff_two_dvd] at hodd
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨z, hz2⟩ := exists_prime_orderOf_dvd_card' (G := ↥(cent G a)) 2 hodd
    have hzG : orderOf (z : G) = 2 := by rw [Subgroup.orderOf_coe]; exact hz2
    have hza : (z : G) * a = a * (z : G) := Subgroup.mem_centralizer_singleton_iff.mp z.2
    have hamem : a ∈ cent G (z : G) := by
      rw [Subgroup.mem_centralizer_singleton_iff]; exact hza.symm
    have hdvd : orderOf a ∣ Nat.card ↥(cent G (z : G)) := orderOf_dvd_natCard_of_mem hamem
    rw [h.2.1 (z : G) hzG] at hdvd
    exact haord1 (eq_one_of_dvd_eight_of_odd hdvd haodd)
  -- `u` inverts every element of `Z`
  have hinvZ : ∀ x ∈ cent G a, u * x * u⁻¹ = x⁻¹ :=
    conj_eq_inv_on_cent_of_conj_eq_inv hu2 hconj hZodd (h.2.1 u hu2)
  -- `X ≤ A ≤ Z`
  have hXZ : X ≤ cent G a := by
    intro y hy
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (hAcomm a ha y (le_centralizer_of_card_three hX3 hy)).symm
  -- `t⁻¹ * u` centralizes `X`, hence lies in `A = C_G(X)`
  have htu : t⁻¹ * u ∈ case1A X := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have hyA : y ∈ case1A X := le_centralizer_of_card_three hX3 hy
    have hu_inv_y : u * y * u⁻¹ = y⁻¹ := hinvZ y (hXZ hy)
    have ht_inv_y : t * y * t⁻¹ = y⁻¹ := hAtinv y hyA
    have hty : t⁻¹ * y⁻¹ * t = y := by
      have hh := congrArg (fun z => t⁻¹ * z * t) ht_inv_y
      have h2 : y = t⁻¹ * y⁻¹ * t := by
        calc y = t⁻¹ * (t * y * t⁻¹) * t := by group
          _ = t⁻¹ * y⁻¹ * t := hh
      exact h2.symm
    have key : (t⁻¹ * u) * y * (t⁻¹ * u)⁻¹ = y := by
      calc (t⁻¹ * u) * y * (t⁻¹ * u)⁻¹ = t⁻¹ * (u * y * u⁻¹) * t := by group
        _ = t⁻¹ * y⁻¹ * t := by rw [hu_inv_y]
        _ = y := hty
    have key2 : (t⁻¹ * u) * y = y * (t⁻¹ * u) := by
      rw [mul_inv_eq_iff_eq_mul] at key
      exact key
    exact key2.symm
  -- assemble: `u = t * (t⁻¹ * u) ∈ ⟨t⟩ * A ⊆ H`
  have h1 : t * (t⁻¹ * u) = u := by group
  have h2 : t * (t⁻¹ * u) ∈ Subgroup.zpowers t ⊔ case1A X :=
    Subgroup.mul_mem_sup (Subgroup.mem_zpowers t) htu
  rw [h1, sup_comm] at h2
  exact huH h2

end Work.BSW.Cases.K4
