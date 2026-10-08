/-
Area `A7REC`, file `Char/c1bD8.lean`: **the `D₈` sum** — the value of an irreducible character of `G`
summed over a Sylow `2`-subgroup `S ≅ DihedralGroup 4` (the group of order `8`), together with the
classification of the elements of `S` of order `4`.

## The mathematics

`DihedralGroup 4` is the dihedral group of order `8` with elements `r i`, `sr i` (`i : ZMod 4`):
the rotations `r 0 = 1`, `r 1`, `r 2`, `r 3 = (r 1)⁻¹` and the four reflections `sr i`, all of order
`2`.  Hence an order-`8` subgroup `S ≤ G` isomorphic to it has

* exactly one element of order `1` (the identity),
* exactly five elements of order `2` — the central involution and the four reflections,
* exactly two elements of order `4`, namely `π` and `π⁻¹` (mutually inverse, and conjugate in `S`
  by a reflection, hence in `G`).

Summing a class function `χ` over `S` therefore gives

`∑_{s ∈ S} χ(s) = χ(1) + χ(π) + χ(π⁻¹) + 5·χ(z) = χ(1) + 2·χ(π) + 5·χ(z)`

(the second equality because `π` and `π⁻¹` are conjugate, so `χ(π⁻¹) = χ(π)`), where `z` denotes
any involution of `S` (here every element of order `2` of `G` is conjugate to `z`, so `χ` takes the
value `χ(z)` on each of the five involutions).

## The formalisation

The computation is carried out by transporting the sum along the isomorphism `↥H ≃* DihedralGroup 4`
(`Equiv.sum_comp`) and expanding the sum over the eight enumerated elements of `DihedralGroup 4`
(`c1bD8_dih4_sum`).  Each of the eight values is then evaluated using the order-preservation of the
isomorphism and the classification of the order-`4` elements.
-/
import Mathlib
import Submission.Work.A7REC.Char.c1bLib

set_option linter.unusedVariables false

namespace Work.A7REC.Char

open OddOrder.RepresentationTheory

/-! ## 1. The group `DihedralGroup 4` -/

/-- In `DihedralGroup 4`, the elements of order `4` are `r 1` and `r 1⁻¹ = r 3`. -/
lemma c1bD8_dih4_order_four {x : DihedralGroup 4} (hx : orderOf x = 4) :
    x = DihedralGroup.r 1 ∨ x = (DihedralGroup.r 1)⁻¹ := by
  have key : ∀ i : ZMod 4, 4 / Nat.gcd 4 i.val = 4 →
      (DihedralGroup.r i : DihedralGroup 4) = DihedralGroup.r 1 ∨
        (DihedralGroup.r i : DihedralGroup 4) = (DihedralGroup.r 1)⁻¹ := by decide
  rcases x with i | i
  · rw [DihedralGroup.orderOf_r] at hx
    exact key i hx
  · rw [DihedralGroup.orderOf_sr] at hx
    norm_num at hx

/-- The sum over `DihedralGroup 4` is the sum over its eight enumerated elements. -/
lemma c1bD8_dih4_sum {M : Type} [AddCommMonoid M] (Ψ : DihedralGroup 4 → M) :
    ∑ x : DihedralGroup 4, Ψ x =
      Ψ (DihedralGroup.r 0) + Ψ (DihedralGroup.r 1) + Ψ (DihedralGroup.r 2) + Ψ (DihedralGroup.r 3)
      + Ψ (DihedralGroup.sr 0) + Ψ (DihedralGroup.sr 1) + Ψ (DihedralGroup.sr 2)
      + Ψ (DihedralGroup.sr 3) := by
  rw [show (Finset.univ : Finset (DihedralGroup 4)) =
      {DihedralGroup.r 0, DihedralGroup.r 1, DihedralGroup.r 2, DihedralGroup.r 3,
       DihedralGroup.sr 0, DihedralGroup.sr 1, DihedralGroup.sr 2, DihedralGroup.sr 3}
      from by decide]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_singleton]
  abel

/-! ## 2. The order-`4` elements of a subgroup isomorphic to `DihedralGroup 4` -/

/-- If `H ≤ G` is isomorphic to `DihedralGroup 4` and `π ∈ H` has order `4`, then the elements of
`H` of order `4` are exactly `π` and `π⁻¹`, and these are conjugate in `G`. -/
lemma c1bD8_order_four {G : Type} [Group G] {H : Subgroup G} (e : ↥H ≃* DihedralGroup 4)
    {π : G} (hπ : π ∈ H) (hπord : orderOf π = 4) :
    (∀ x ∈ H, orderOf x = 4 → x = π ∨ x = π⁻¹) ∧ IsConj π π⁻¹ := by
  set p : ↥H := ⟨π, hπ⟩ with hp
  have hpc : (p : G) = π := by rw [hp]
  have hpo : orderOf p = 4 := by rw [hp, Subgroup.orderOf_mk]; exact hπord
  have hep : orderOf (e p) = 4 := by rw [MulEquiv.orderOf_eq]; exact hpo
  have hclass : e p = DihedralGroup.r 1 ∨ e p = (DihedralGroup.r 1)⁻¹ :=
    c1bD8_dih4_order_four hep
  have hx4 : ∀ x : ↥H, orderOf x = 4 → x = p ∨ x = p⁻¹ := by
    intro x hx
    have hxe : orderOf (e x) = 4 := by rw [MulEquiv.orderOf_eq]; exact hx
    rcases c1bD8_dih4_order_four hxe with h | h <;> rcases hclass with hc | hc
    · left; apply e.injective; simp [h, hc]
    · right; apply e.injective; simp [h, hc]
    · right; apply e.injective; simp [h, hc]
    · left; apply e.injective; simp [h, hc]
  have hconjH : IsConj p p⁻¹ := by
    rw [isConj_iff]
    rcases hclass with hc | hc
    · refine ⟨e.symm (DihedralGroup.sr 0), ?_⟩
      apply e.injective
      simp only [map_mul, map_inv, MulEquiv.apply_symm_apply, hc]
      decide
    · refine ⟨e.symm (DihedralGroup.sr 0), ?_⟩
      apply e.injective
      simp only [map_mul, map_inv, MulEquiv.apply_symm_apply, hc]
      decide
  constructor
  · intro x hxH hxord
    have hx4' : (⟨x, hxH⟩ : ↥H) = p ∨ (⟨x, hxH⟩ : ↥H) = p⁻¹ := by
      apply hx4
      rw [Subgroup.orderOf_mk]
      exact hxord
    rcases hx4' with h' | h'
    · left
      have := congrArg Subtype.val h'
      rwa [hpc] at this
    · right
      have := congrArg Subtype.val h'
      simp only [Subgroup.coe_inv, hpc] at this
      exact this
  · rw [isConj_iff] at hconjH
    obtain ⟨c, hc⟩ := hconjH
    rw [isConj_iff]
    refine ⟨(c : G), ?_⟩
    have hcoe := congrArg Subtype.val hc
    simp only [Subgroup.coe_mul, Subgroup.coe_inv] at hcoe
    rw [← hpc]
    exact hcoe

/-! ## 3. The sum of a class function over a `D₈`-subgroup -/

/-- If `H ≤ G` is isomorphic to `DihedralGroup 4`, `π ∈ H` has order `4` and every element of `G`
of order `2` is conjugate to `z`, then for any class function `χ` on `G`

`∑_{s ∈ H} χ(s) = χ(1) + 5·χ(z) + 2·χ(π)`. -/
lemma c1bD8_sum_aux {G : Type} [Group G] [Finite G] {H : Subgroup G} [Fintype ↥H]
    (e : ↥H ≃* DihedralGroup 4) (z π : G) (χ : OddOrder.RepresentationTheory.ClassFunction G ℂ)
    (hπH : π ∈ H) (hπord : orderOf π = 4)
    (hone : ∀ x : G, orderOf x = 2 → IsConj x z) :
    ∑ s : ↥H, χ s = χ 1 + 5 * χ z + 2 * χ π := by
  set p : ↥H := ⟨π, hπH⟩ with hp
  have hpc : (p : G) = π := by rw [hp]
  have hpo : orderOf p = 4 := by rw [hp, Subgroup.orderOf_mk]; exact hπord
  have hep : orderOf (e p) = 4 := by rw [MulEquiv.orderOf_eq]; exact hpo
  have hclass : e p = DihedralGroup.r 1 ∨ e p = (DihedralGroup.r 1)⁻¹ :=
    c1bD8_dih4_order_four hep
  have hconjH : IsConj p p⁻¹ := by
    rw [isConj_iff]
    rcases hclass with hc | hc
    · refine ⟨e.symm (DihedralGroup.sr 0), ?_⟩
      apply e.injective
      simp only [map_mul, map_inv, MulEquiv.apply_symm_apply, hc]
      decide
    · refine ⟨e.symm (DihedralGroup.sr 0), ?_⟩
      apply e.injective
      simp only [map_mul, map_inv, MulEquiv.apply_symm_apply, hc]
      decide
  have hconj : IsConj π π⁻¹ := by
    rw [isConj_iff] at hconjH
    obtain ⟨c, hc⟩ := hconjH
    rw [isConj_iff]
    refine ⟨(c : G), ?_⟩
    have hcoe := congrArg Subtype.val hc
    simp only [Subgroup.coe_mul, Subgroup.coe_inv] at hcoe
    rw [← hpc]
    exact hcoe
  have hχinv : χ π⁻¹ = χ π :=
    OddOrder.RepresentationTheory.ClassFunction.of_isConj χ hconj.symm
  set Ψ : DihedralGroup 4 → ℂ := fun x => χ ((e.symm x : ↥H) : G) with hΨ
  have hstep : ∑ s : ↥H, χ (s : G) = ∑ x : DihedralGroup 4, Ψ x := by
    rw [hΨ]
    exact (Equiv.sum_comp e.toEquiv.symm (fun s : ↥H => χ (s : G))).symm
  have hPsi2 : ∀ y : DihedralGroup 4, orderOf y = 2 → Ψ y = χ z := by
    intro y hy
    rw [hΨ]
    show χ ((e.symm y : ↥H) : G) = χ z
    apply OddOrder.RepresentationTheory.ClassFunction.of_isConj
    apply hone
    have h1 : orderOf ((e.symm y : ↥H) : G) = orderOf (e.symm y) :=
      orderOf_injective (Subgroup.subtype H) Subtype.coe_injective (e.symm y)
    rw [h1, ← MulEquiv.orderOf_eq e (e.symm y), MulEquiv.apply_symm_apply]
    exact hy
  have h0 : Ψ (DihedralGroup.r 0) = χ 1 := by
    rw [hΨ]
    simp
  have h2 : Ψ (DihedralGroup.r 2) = χ z := by
    apply hPsi2
    rw [DihedralGroup.orderOf_r]
    decide
  have hs : ∀ i : ZMod 4, Ψ (DihedralGroup.sr i) = χ z :=
    fun i => hPsi2 _ (DihedralGroup.orderOf_sr i)
  rw [hstep, c1bD8_dih4_sum Ψ]
  rcases hclass with hc | hc
  · have h1 : Ψ (DihedralGroup.r 1) = χ π := by
      rw [hΨ]
      show χ ((e.symm (DihedralGroup.r 1) : ↥H) : G) = χ π
      have hy : e.symm (DihedralGroup.r 1) = p := by
        rw [MulEquiv.symm_apply_eq]
        exact hc.symm
      rw [hy, hpc]
    have h3 : Ψ (DihedralGroup.r 3) = χ π := by
      rw [hΨ]
      show χ ((e.symm (DihedralGroup.r 3) : ↥H) : G) = χ π
      have hy : e.symm (DihedralGroup.r 3) = p⁻¹ := by
        rw [MulEquiv.symm_apply_eq, MulEquiv.map_inv, hc]
        decide
      rw [hy, Subgroup.coe_inv, hpc, hχinv]
    rw [h0, h1, h2, h3, hs 0, hs 1, hs 2, hs 3]
    ring
  · have h3 : Ψ (DihedralGroup.r 3) = χ π := by
      rw [hΨ]
      show χ ((e.symm (DihedralGroup.r 3) : ↥H) : G) = χ π
      have hy : e.symm (DihedralGroup.r 3) = p := by
        rw [MulEquiv.symm_apply_eq, hc]
        decide
      rw [hy, hpc]
    have h1 : Ψ (DihedralGroup.r 1) = χ π := by
      rw [hΨ]
      show χ ((e.symm (DihedralGroup.r 1) : ↥H) : G) = χ π
      have hy : e.symm (DihedralGroup.r 1) = p⁻¹ := by
        rw [MulEquiv.symm_apply_eq, MulEquiv.map_inv, hc]
        simp
      rw [hy, Subgroup.coe_inv, hpc, hχinv]
    rw [h0, h1, h2, h3, hs 0, hs 1, hs 2, hs 3]
    ring

/-! ## 4. The lemma `c1bD8` -/

theorem c1bD8 {G : Type} [Group G] [Finite G] (S : Sylow 2 G) (z π : G)
    [Fintype ↥(S : Subgroup G)] (χ : OddOrder.RepresentationTheory.IrreducibleCharacter G)
    (hSdih : Nonempty ((S : Subgroup G) ≃* DihedralGroup 4))
    (hzS : z ∈ (S : Subgroup G)) (hz2 : orderOf z = 2)
    (hπS : π ∈ (S : Subgroup G)) (hπord : orderOf π = 4)
    (hone : ∀ x : G, orderOf x = 2 → IsConj x z) :
    (∀ x ∈ (S : Subgroup G), orderOf x = 4 → x = π ∨ x = π⁻¹) ∧ IsConj π π⁻¹ ∧
    ∑ s : (S : Subgroup G), (χ : OddOrder.RepresentationTheory.ClassFunction G ℂ) s =
      (χ : OddOrder.RepresentationTheory.ClassFunction G ℂ) 1
        + 5 * (χ : OddOrder.RepresentationTheory.ClassFunction G ℂ) z
        + 2 * (χ : OddOrder.RepresentationTheory.ClassFunction G ℂ) π := by
  obtain ⟨e⟩ := hSdih
  obtain ⟨hfour, hconj⟩ := c1bD8_order_four e hπS hπord
  refine ⟨hfour, hconj, ?_⟩
  exact c1bD8_sum_aux e z π (χ : OddOrder.RepresentationTheory.ClassFunction G ℂ) hπS hπord hone

end Work.A7REC.Char
