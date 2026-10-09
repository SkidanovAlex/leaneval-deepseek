/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# `F(d)/F(d)^2 ≅ 𝔽_p[G]^d`: the canonical map is bijective

This file proves `Work.CohomologicalShrinking.squareQuotientToFun_bijective`, the
identification, used silently by Schmidt–Wingberg in the proof of Proposition 6 of
arXiv:math/9809211, of the quotient `F(d)/F(d)^2 = F(d)/F(d)^p[F(d),F(d)]` of the free
`G`-operator group of rank `d` with the free `𝔽_p[G]`-module `𝔽_p[G]^d`
(realised as `Fin d × G → 𝔽_p` with the left regular action on the second factor).

The canonical map `squareQuotientToFun p G d : F(d)/F(d)^2 → (Fin d × G → 𝔽_p)` sends the
class `genMk p G d x` of the free generator `x_{i,g}` to the coordinate function at `(i,g)`
(lemma `squareQuotientToFun_genMk`).  We exhibit an explicit two-sided inverse

* `funToSquareQuotient p G d : (Fin d × G → 𝔽_p) →ₗ[𝔽_p] F(d)/F(d)^2`,
  `f ↦ ∑ x, f x • genMk p G d x`,

and show that the two composites are the identities
(`squareQuotientToFun_funToSquareQuotient`, `funToSquareQuotient_squareQuotientToFun`).

The second composite is the substantive one: writing an element of the quotient as the class
`squareQuotientClass p G d w` of a word `w` in the free group (which is possible because the
quotient map is surjective), one inducts on `w` using the multiplicativity of the class map
(`squareQuotientClass_one`, `_mul`, `_inv`); no structure theory of free abelian groups is
needed.

## Main results

* `Work.CohomologicalShrinking.modsquare.funToSquareQuotient` : the explicit inverse map.
* `Work.CohomologicalShrinking.modsquare.squareQuotientToFun_bijective` : the target.
-/

import Mathlib
import Submission.Work.CohomologicalShrinking.ModSquare
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

attribute [local instance] Classical.decEq

namespace Work.CohomologicalShrinking.modsquare

open Work.CohomologicalShrinking

open scoped IsMulCommutative

universe u

/-! ## The reconstruction of a function from its coordinates

A function `f : X → 𝔽_p` is the `𝔽_p`-linear combination `∑ x, f x • e_x` of the standard
basis vectors `e_x = Pi.single x 1`; this is the only place where the finiteness of `X`
is used (`Pi.single` is supported on a single point). -/

section Sum

variable (p : ℕ) (X : Type*) [Fintype X]

lemma sum_smul_pi_single [DecidableEq X] (f : X → ZMod p) :
    (∑ x, f x • (Pi.single x (1 : ZMod p) : X → ZMod p)) = f := by
  funext y
  rw [Finset.sum_apply]
  rw [Finset.sum_eq_single y]
  · simp
  · intro b _ hb
    rw [Pi.smul_apply, Pi.single_eq_of_ne (Ne.symm hb), smul_zero]
  · intro hy
    exact absurd (Finset.mem_univ y) hy

end Sum

/-! ## The class of a word of the free group in `F(d)/F(d)^2` -/

section Class

variable (p : ℕ) (G : Type*) [Group G] (d : ℕ)

/-- The class in `F(d)/F(d)^2` of a word of the free `G`-operator group `F(d)`; this is
`genMk p G d x` on the free generators `x_{i,g}` (`squareQuotientClass_of`). -/
noncomputable def squareQuotientClass (w : Work.Shrinking.freeOperatorGroup G d) :
    squareQuotient p G d :=
  Additive.ofMul (QuotientGroup.mk'
    ((Work.Shrinking.pCentralSeries p (Work.Shrinking.freeOperatorGroup G d) 1).subgroupOf
      (Work.Shrinking.pCentralSeries p (Work.Shrinking.freeOperatorGroup G d) 0))
    ⟨w, Subgroup.mem_top _⟩)

@[simp]
lemma squareQuotientClass_one : squareQuotientClass p G d 1 = 0 := by
  rw [squareQuotientClass]
  have h : (⟨(1 : Work.Shrinking.freeOperatorGroup G d), Subgroup.mem_top _⟩ :
      ↥(Work.Shrinking.pCentralSeries p (Work.Shrinking.freeOperatorGroup G d) 0)) = 1 :=
    Subtype.ext rfl
  rw [h, map_one, ofMul_one]

@[simp]
lemma squareQuotientClass_of (x : Fin d × G) :
    squareQuotientClass p G d (FreeGroup.of x) = genMk p G d x := rfl

@[simp]
lemma squareQuotientClass_inv (x : Fin d × G) :
    squareQuotientClass p G d (FreeGroup.of x)⁻¹ = - squareQuotientClass p G d (FreeGroup.of x) := by
  rw [squareQuotientClass, squareQuotientClass]
  have h : (⟨(FreeGroup.of x)⁻¹, Subgroup.mem_top _⟩ :
      ↥(Work.Shrinking.pCentralSeries p (Work.Shrinking.freeOperatorGroup G d) 0)) =
      (⟨FreeGroup.of x, Subgroup.mem_top _⟩ :
      ↥(Work.Shrinking.pCentralSeries p (Work.Shrinking.freeOperatorGroup G d) 0))⁻¹ :=
    Subtype.ext rfl
  rw [h, map_inv, ofMul_inv]

@[simp]
lemma squareQuotientClass_mul (v u : Work.Shrinking.freeOperatorGroup G d) :
    squareQuotientClass p G d (v * u) = squareQuotientClass p G d v + squareQuotientClass p G d u := by
  rw [squareQuotientClass, squareQuotientClass, squareQuotientClass]
  have h : (⟨v * u, Subgroup.mem_top _⟩ :
      ↥(Work.Shrinking.pCentralSeries p (Work.Shrinking.freeOperatorGroup G d) 0)) =
      (⟨v, Subgroup.mem_top _⟩ : ↥(Work.Shrinking.pCentralSeries p
        (Work.Shrinking.freeOperatorGroup G d) 0)) *
      (⟨u, Subgroup.mem_top _⟩ : ↥(Work.Shrinking.pCentralSeries p
        (Work.Shrinking.freeOperatorGroup G d) 0)) := Subtype.ext rfl
  rw [h, map_mul, ofMul_mul]

end Class

/-! ## The explicit inverse -/

section Inverse

variable (p : ℕ) (G : Type*) [Group G] [Fintype G] (d : ℕ)

/-- The explicit `𝔽_p`-linear map `(Fin d × G → 𝔽_p) → F(d)/F(d)^2` sending the coordinate
function at `x` to the class of `x`; it is a two-sided inverse of `squareQuotientToFun`. -/
noncomputable def funToSquareQuotient :
    (Fin d × G → ZMod p) →ₗ[ZMod p] squareQuotient p G d where
  toFun f := ∑ x, f x • genMk p G d x
  map_add' f g := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Pi.add_apply, add_smul]
  map_smul' c f := by
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Pi.smul_apply, smul_assoc, RingHom.id_apply]

@[simp]
lemma funToSquareQuotient_genMk (x : Fin d × G) :
    funToSquareQuotient p G d (Pi.single x (1 : ZMod p)) = genMk p G d x := by
  change (∑ y, (Pi.single x (1 : ZMod p) : Fin d × G → ZMod p) y • genMk p G d y)
    = genMk p G d x
  rw [Finset.sum_eq_single x]
  · simp
  · intro b _ hb
    rw [Pi.single_eq_of_ne hb, zero_smul]
  · intro hx
    exact absurd (Finset.mem_univ x) hx

/-- The composite `squareQuotientToFun ∘ funToSquareQuotient` is the identity. -/
theorem squareQuotientToFun_funToSquareQuotient (f : Fin d × G → ZMod p) :
    squareQuotientToFun p G d (funToSquareQuotient p G d f) = f := by
  change squareQuotientToFun p G d (∑ x, f x • genMk p G d x) = f
  simp only [map_sum, map_smul, squareQuotientToFun_genMk]
  exact sum_smul_pi_single p (Fin d × G) f

/-- The composite `funToSquareQuotient ∘ squareQuotientToFun` is the identity: every element of
`F(d)/F(d)^2` is the class of a word, and
`funToSquareQuotient ∘ squareQuotientToFun` fixes the classes of the words. -/
theorem funToSquareQuotient_squareQuotientToFun (y : squareQuotient p G d) :
    funToSquareQuotient p G d (squareQuotientToFun p G d y) = y := by
  obtain ⟨z, hz⟩ := QuotientGroup.mk'_surjective
    ((Work.Shrinking.pCentralSeries p (Work.Shrinking.freeOperatorGroup G d) 1).subgroupOf
      (Work.Shrinking.pCentralSeries p (Work.Shrinking.freeOperatorGroup G d) 0))
    (Additive.toMul y)
  have h2 : y = squareQuotientClass p G d z.1 := by
    show y = Additive.ofMul (QuotientGroup.mk' _ ⟨z.1, Subgroup.mem_top _⟩)
    exact (ofMul_toMul y).symm.trans (congrArg Additive.ofMul hz).symm
  rw [h2]
  clear h2 hz y
  have key : ∀ w : Work.Shrinking.freeOperatorGroup G d,
      funToSquareQuotient p G d (squareQuotientToFun p G d (squareQuotientClass p G d w))
        = squareQuotientClass p G d w := by
    intro w
    induction w using FreeGroup.induction_on with
    | one => rw [squareQuotientClass_one]; simp
    | of x => rw [squareQuotientClass_of, squareQuotientToFun_genMk, funToSquareQuotient_genMk]
    | inv_of x ih => rw [squareQuotientClass_inv, map_neg, map_neg, ih]
    | mul v u ihv ihu => rw [squareQuotientClass_mul, map_add, map_add, ihv, ihu]
  exact key z.1

end Inverse

/-! ## The target -/

theorem squareQuotientToFun_bijective (p : ℕ) [Fact p.Prime] (G : Type*) [Group G] [Fintype G]
    (d : ℕ) : Function.Bijective (squareQuotientToFun p G d) := by
  refine ⟨fun a b hab => ?_, fun v => ⟨funToSquareQuotient p G d v, ?_⟩⟩
  · rw [← funToSquareQuotient_squareQuotientToFun p G d a,
      ← funToSquareQuotient_squareQuotientToFun p G d b, hab]
  · exact squareQuotientToFun_funToSquareQuotient p G d v

end Work.CohomologicalShrinking.modsquare
