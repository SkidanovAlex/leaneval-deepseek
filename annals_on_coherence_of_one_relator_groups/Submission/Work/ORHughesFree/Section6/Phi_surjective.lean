/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Surjectivity of the universal morphism `Φ : Rat(Kˣ × G) →+* D_{K[G],U}`

[JZLA20, Lemma 4.2] (see also [Sthesis, Examples 5.37, 5.38]): for a field `K`, a group `G`, a
ring `U` and a ring homomorphism `φ : K[G] →+* U`, the universal morphism of rational
`Kˣ × G`-semirings

`Φ = Phi φ : Rat(Kˣ × G) →+* D`,  `D = divisionClosure (Set.range φ)`,

is **surjective** onto the division closure `D`.

The proof is the standard closure argument.  Write `ΦU : Rat(Kˣ × G) →+* U` for `Φ` followed by
the inclusion of `D` in `U`, and let `E` be the image of `ΦU` in `U` (a subring of `U`: it is
closed under `+`, `*`, `0`, `1`, and under negation because `-1` is in the image, being
`Φ (ofGroup (-1, 1)) = φ (-1)`).  Then

* `E` contains `Set.range φ`: every `φ (single g c)` is `φ (unitOf (c,g)) = ΦU (ofGroup (c,g))`,
  and the `single g c` generate `K[G]` as a ring (via `MonoidAlgebra.induction_linear`);
* `E` is closed under inverses in `U`: if `x = ΦU z` is invertible in `U` with inverse `y`, then
  `y` lies in `D` (the division closure is closed under inverses), `ΦU z` is a unit of `D`, and
  `y = ratOpClosure D (ΦU z) = ΦU (RatU.ratOp z)` by the defining property `map_rat` of `Φ`;
* hence, by `divisionClosure_le_of_invClosed`, the division closure of `Set.range φ` is contained
  in `E`, i.e. `D ≤ E`, and since `E ≤ D` we get `E = D`.

The last step is `Φ_surjective`: an element `x ∈ D` lies in `D = E = Set.range ΦU`, say
`x = ΦU z`, i.e. `↑(Φ z) = ↑x` in `U`, whence `Φ z = x`.

This is the bridge from the envelope data of [JZLA20, Theorem 6.1] to the existence clause of
`Prop51Data.treeH_spec`.
-/
import Mathlib
import Submission.Work.ORHughesFree.Section6.RatStruct
import Submission.Work.ORHughesFree.Section6.ratOpClosure_spec
import Submission.Work.ORHughesFree.DivisionClosure
import Submission.Work.ORHughesFree.DivisionClosure.divisionClosure_idem
import Submission.Work.ORHughesFree.DivisionClosure.divisionClosure_mono
import Submission.Work.ORHughesFree.Rat.OfGroup

set_option autoImplicit false

namespace Work.ORHughesFree.Section6

open Work.ORHughesFree

variable {K : Type} [Field K] {G : Type} [Group G] {U : Type} [Ring U]

/-- The antitone bijection `x ↦ x⁻¹` on the units of a subring is `ratOpClosure`: if `x` is a unit
of `D` with two-sided inverse `y`, then `ratOpClosure D x = y`. -/
private theorem ratOpClosure_eq_of_mul_eq_one (D : Subring U) {x : ↥D} (h : IsUnit x) {y : ↥D}
    (hxy : x * y = 1) (hyx : y * x = 1) : ratOpClosure D x = y := by
  have hu : h.unit = ⟨x, y, hxy, hyx⟩ := Units.ext rfl
  unfold ratOpClosure
  rw [dif_pos h, hu]
  rfl

/-- The group-like units `unitOf u = single g λ` of `K[G]` generate `K[G]` as a ring. -/
private theorem closure_range_unitOf_eq_top :
    Subring.closure (Set.range (unitOf (K := K) (G := G))) = ⊤ := by
  rw [Subring.eq_top_iff']
  intro a
  induction a using MonoidAlgebra.induction_linear with
  | zero => exact Subring.zero_mem _
  | add x y hx hy => exact Subring.add_mem _ hx hy
  | single m r =>
      by_cases hr : r = 0
      · subst hr
        rw [MonoidAlgebra.single_zero]
        exact Subring.zero_mem _
      · rw [show MonoidAlgebra.single m r = unitOf ((Units.mk0 r hr), m) from by
          simp [unitOf, Units.val_mk0]]
        exact Subring.subset_closure ⟨(Units.mk0 r hr, m), rfl⟩

/-- The group-like unit `(λ, g) = (-1, 1)` of `K[G]` is `-1`. -/
private theorem unitOf_neg_one :
    unitOf (K := K) (G := G) (Units.mk0 (-1 : K) (by simp), (1 : G)) = -1 := by
  unfold unitOf
  rw [Units.val_mk0, MonoidAlgebra.single_neg, ← MonoidAlgebra.one_def]

/-- The image under `φ` of `(-1, 1)` is `-1`; i.e. `-1` lies in the image of `Φ`. -/
private theorem imElem_neg_one (φ : MonoidAlgebra K G →+* U) :
    ((imElem φ (Units.mk0 (-1 : K) (by simp), (1 : G)) :
        ↥(divisionClosure (Set.range φ))) : U) = -1 := by
  show φ (unitOf (Units.mk0 (-1 : K) (by simp), (1 : G))) = -1
  rw [unitOf_neg_one, map_neg, map_one]

/-- The image of the universal morphism `Φ`, transported into `U` along the inclusion of the
division closure `D`, as a subring of `U`.  It is closed under negation because `-1` is the image
of `ofGroup (-1, 1)`. -/
private noncomputable def PhiImageU (φ : MonoidAlgebra K G →+* U) : Subring U where
  carrier := {y : U | ∃ z : RatU (Kˣ × G),
    ((Phi φ z : ↥(divisionClosure (Set.range φ))) : U) = y}
  mul_mem' := by
    rintro a b ⟨x, rfl⟩ ⟨y, rfl⟩
    exact ⟨x * y, by rw [map_mul, Subring.coe_mul]⟩
  one_mem' := ⟨1, by rw [map_one, Subring.coe_one]⟩
  add_mem' := by
    rintro a b ⟨x, rfl⟩ ⟨y, rfl⟩
    exact ⟨x + y, by rw [map_add, Subring.coe_add]⟩
  zero_mem' := ⟨0, by rw [map_zero, Subring.coe_zero]⟩
  neg_mem' := by
    rintro a ⟨x, rfl⟩
    refine ⟨RatU.ofGroup (Units.mk0 (-1 : K) (by simp), (1 : G)) * x, ?_⟩
    rw [map_mul, Phi_ofGroup φ (Units.mk0 (-1 : K) (by simp), (1 : G)), Subring.coe_mul,
      imElem_neg_one φ, neg_one_mul]

/-- **[JZLA20, Lemma 4.2]**: the universal morphism `Φ : Rat(Kˣ × G) →+* D_{K[G],U}` is
surjective onto the division closure `D_{K[G],U}` of `φ(K[G])` in `U`. -/
theorem Phi_surjective {K : Type} [Field K] {G : Type} [Group G] {U : Type} [Ring U]
    (φ : MonoidAlgebra K G →+* U) :
    Function.Surjective (Work.ORHughesFree.Phi φ) := by
  -- `Set.range φ` is contained in the image of `Φ`, transported into `U`.
  have hgen : ∀ u : Kˣ × G, φ (unitOf u) ∈ PhiImageU φ := by
    intro u
    exact ⟨RatU.ofGroup u, by rw [Phi_ofGroup]; rfl⟩
  have hsub_mem : ∀ a : MonoidAlgebra K G, φ a ∈ PhiImageU φ := by
    have hclosure : Subring.closure (Set.range (unitOf (K := K) (G := G))) ≤
        Subring.comap φ (PhiImageU φ) := by
      rw [Subring.closure_le]
      rintro x ⟨u, rfl⟩
      exact hgen u
    rw [closure_range_unitOf_eq_top] at hclosure
    intro a
    exact hclosure (Subring.mem_top a)
  have hsub : Set.range φ ⊆ (PhiImageU φ : Set U) := fun y hy => by
    obtain ⟨a, rfl⟩ := hy
    exact hsub_mem a
  -- The image of `Φ` is closed under inverses (in `U`) of its units: `⋄` is inversion on units.
  have hEinv : ∀ x ∈ PhiImageU φ, ∀ y, x * y = 1 → y * x = 1 → y ∈ PhiImageU φ := by
    intro x hx y hxy hyx
    obtain ⟨z, hz⟩ := hx
    have hxD : x ∈ (divisionClosure (Set.range φ) : Set U) := by
      rw [← hz]; exact (Phi φ z).2
    have hyD : y ∈ (divisionClosure (Set.range φ) : Set U) :=
      DivisionClosure.divisionClosure_inv_mem (Set.range φ) hxD hxy hyx
    refine ⟨RatU.ratOp z, ?_⟩
    have he1 : Phi φ z * (⟨y, hyD⟩ : ↥(divisionClosure (Set.range φ))) = 1 := by
      apply Subtype.ext
      show ((Phi φ z : ↥(divisionClosure (Set.range φ))) : U) * y = 1
      rw [hz]; exact hxy
    have he2 : (⟨y, hyD⟩ : ↥(divisionClosure (Set.range φ))) * Phi φ z = 1 := by
      apply Subtype.ext
      show y * ((Phi φ z : ↥(divisionClosure (Set.range φ))) : U) = 1
      rw [hz]; exact hyx
    have hunit : IsUnit (Phi φ z) := ⟨⟨Phi φ z, ⟨y, hyD⟩, he1, he2⟩, rfl⟩
    rw [show Phi φ (RatU.ratOp z) = (ratStruct φ).ratOp (Phi φ z) from (Phi_isRational φ).map_rat z,
      show (ratStruct φ).ratOp (Phi φ z) =
        ratOpClosure (divisionClosure (Set.range φ)) (Phi φ z) from ratStruct_ratOp φ _,
      ratOpClosure_eq_of_mul_eq_one (divisionClosure (Set.range φ)) hunit he1 he2]
  -- Hence the division closure of `Set.range φ` is contained in the image.
  have hDE : divisionClosure (Set.range φ) ≤ PhiImageU φ := by
    have h1 : (divisionClosure (Set.range φ) : Set U) ⊆
        ((divisionClosure ((PhiImageU φ : Set U))) : Set U) :=
      DivisionClosure.divisionClosure_mono hsub
    have h2 : (divisionClosure ((PhiImageU φ : Set U)) : Set U) ⊆ (PhiImageU φ : Set U) :=
      DivisionClosure.divisionClosure_le_of_invClosed (PhiImageU φ) hEinv
    exact fun x hx => h2 (h1 hx)
  intro x
  have hxE : (x : U) ∈ PhiImageU φ := hDE x.2
  obtain ⟨z, hz⟩ := hxE
  exact ⟨z, Subtype.ext hz⟩

end Work.ORHughesFree.Section6
