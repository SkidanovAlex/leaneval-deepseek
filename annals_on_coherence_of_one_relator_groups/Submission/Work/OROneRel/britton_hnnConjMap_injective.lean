import Mathlib
import Submission.Work.OROneRel.hnnCosetWord

set_option autoImplicit false
set_option linter.unusedVariables false

/-!
# Britton's lemma for the canonical HNN structure attached to a pair `(H, t)`

For a subgroup `H ≤ G` and an element `t : G` let `A = H ⊓ t⁻¹Ht` and `B = tAt⁻¹` (see
`Submission/Work/OROneRel/hnnConjSplit.lean`), so that `hnnConjMap H t` is the canonical map
`HNN(↥H, A, B, φ) →* G` (`of ↦ incl`, `t ↦ t`), with `φ = hnnConjEquiv H t` given by conjugation by
`t`.

This file proves `Work.OROneRel.britton_hnnConjMap_injective`: if `hnnConjMap H t` is injective (so
that `G` contains, away from generation, the HNN extension as a subgroup), then a list `L` of letters
`(ε, h)` such that the word `h₁ t^{ε₁} ⋯ hₙ t^{εₙ}` represents an element of `H`, and which admits no
"pinch" (no consecutive pair with `t^{ε} h' t^{-ε} ∈ H`), must be the empty list.

The proof is Mathlib's Britton lemma for `HNNExtension.NormalWord.ReducedWord`
(`ReducedWord.toList_eq_nil_of_mem_of_range`), applied to the reduced word of the *inverse* of the
image of the word: if `x ∈ HNN(↥H, A, B, φ)` denotes the image of `L`, then `hnnConjMap H t x` is the
word of `L`, hence lies in `H`; injectivity of `hnnConjMap` gives `x = of k` for some `k ∈ ↥H`, and
the reduced word `w` of `x⁻¹ = of k⁻¹` has `w.prod ∈ of.range`, so by Britton `w.toList = []`, which
forces `L = []` (the entries of `w.toList` are the entries of `L`, reversed).

The only bookkeeping is that the `NoPinch` condition on `L` is exactly Mathlib's chain condition on
the reversed list of `(ε, h⁻¹)`.
-/

namespace Work.OROneRel

universe u

variable {G : Type u} [Group G]

open HNNExtension

/-- `A = H ⊓ t⁻¹Ht`, viewed as a subgroup of the base group `↥H`. -/
abbrev hnnBaseA (H : Subgroup G) (t : G) : Subgroup ↥H := (hnnEdgeA H t).subgroupOf H

/-- `B = tAt⁻¹`, viewed as a subgroup of the base group `↥H`. -/
abbrev hnnBaseB (H : Subgroup G) (t : G) : Subgroup ↥H := (hnnEdgeB H t).subgroupOf H

theorem hnnEdgeSubBase_eq_toSubgroup (H : Subgroup G) (t : G) (u : ℤˣ) :
    hnnEdgeSubBase H t u = HNNExtension.toSubgroup (hnnBaseA H t) (hnnBaseB H t) u := rfl

/-- The element of the HNN extension `HNN(↥H, A, B, φ)` corresponding to the word `L`. -/
noncomputable def hnnConjWord (H : Subgroup G) (t : G) (L : List (ℤˣ × ↥H)) :
    HNNExtension ↥H (hnnBaseA H t) (hnnBaseB H t) (hnnConjEquiv H t) :=
  ((L.map fun x => HNNExtension.of x.2 * HNNExtension.t ^ (x.1 : ℤ)) :
    List (HNNExtension ↥H (hnnBaseA H t) (hnnBaseB H t) (hnnConjEquiv H t))).prod

/-- The comparison map sends `hnnConjWord H t L` to `hnnWord H t L`. -/
theorem hnnConjMap_hnnConjWord (H : Subgroup G) (t : G) (L : List (ℤˣ × ↥H)) :
    hnnConjMap H t (hnnConjWord H t L) = hnnWord H t L := by
  rw [hnnConjWord, hnnWord, MonoidHom.map_list_prod, List.map_map]
  congr 1
  apply List.map_congr_left
  intro x _
  simp only [Function.comp_apply, map_mul, map_zpow, hnnConjMap_of, hnnConjMap_t]

/-! ## The reduced word attached to a pinch-free list -/

/-- The `NoPinch` condition on `L` is precisely Mathlib's chain condition for the reduced word whose
letters are those of `L`, read backwards and inverted. -/
theorem noPinch_isChain (H : Subgroup G) (t : G) (L : List (ℤˣ × ↥H)) (h : NoPinch H t L) :
    (L.reverse.map (fun x : ℤˣ × ↥H => (-x.1, x.2⁻¹))).IsChain
      (fun a b : ℤˣ × ↥H =>
        a.2 ∈ HNNExtension.toSubgroup (hnnBaseA H t) (hnnBaseB H t) a.1 → a.1 = b.1) := by
  rw [NoPinch] at h
  rw [List.isChain_map, List.isChain_reverse]
  refine h.imp ?_
  intro a b hab hmem
  rw [hnnEdgeSubBase_eq_toSubgroup] at hab
  by_cases hba : b.1 = a.1
  · rw [hba]
  · exfalso
    have hneg : b.1 = -a.1 := by
      rcases Int.units_eq_one_or b.1 with hb | hb <;>
        rcases Int.units_eq_one_or a.1 with ha | ha <;> simp_all
    have hT : HNNExtension.toSubgroup (hnnBaseA H t) (hnnBaseB H t) (-b.1) =
        HNNExtension.toSubgroup (hnnBaseA H t) (hnnBaseB H t) a.1 := by rw [hneg, neg_neg]
    rw [hT] at hmem
    exact hab ⟨by simpa using inv_mem hmem, hneg⟩

/-- The reduced word of the inverse of `hnnConjWord H t L`, with letters read off `L` backwards. -/
noncomputable def hnnReduced (H : Subgroup G) (t : G) (L : List (ℤˣ × ↥H))
    (hchain : NoPinch H t L) : NormalWord.ReducedWord ↥H (hnnBaseA H t) (hnnBaseB H t) :=
  { head := 1
    toList := L.reverse.map fun x : ℤˣ × ↥H => (-x.1, x.2⁻¹)
    chain := noPinch_isChain H t L hchain }

/-- Reversing a list, inverting and mapping is the inverse of the product (a non-commutative
bookkeeping lemma). -/
theorem list_prod_reverse_inv {M : Type*} [Group M] (H : Subgroup G) (T : M) (f : ↥H →* M)
    (L : List (ℤˣ × ↥H)) :
    (List.map (fun x : ℤˣ × ↥H => T ^ (x.1 : ℤ) * f x.2)
        (L.reverse.map fun x : ℤˣ × ↥H => (-x.1, x.2⁻¹))).prod
      = (List.map (fun x : ℤˣ × ↥H => f x.2 * T ^ (x.1 : ℤ)) L).prod⁻¹ := by
  induction L with
  | nil => simp
  | cons x rest ih =>
    simp only [List.reverse_cons, List.map_append, List.map_cons, List.map_nil, List.prod_append,
      List.prod_cons, List.prod_nil, mul_one]
    rw [ih]
    simp [mul_inv_rev, zpow_neg, Units.val_neg]

/-- The product of the reduced word of `L` is the inverse of the image of the word of `L`. -/
theorem hnnReduced_prod (H : Subgroup G) (t : G) (L : List (ℤˣ × ↥H))
    (hchain : NoPinch H t L) :
    NormalWord.ReducedWord.prod (hnnConjEquiv H t) (hnnReduced H t L hchain) =
      (hnnConjWord H t L)⁻¹ := by
  have h := list_prod_reverse_inv H
    (M := HNNExtension ↥H (hnnBaseA H t) (hnnBaseB H t) (hnnConjEquiv H t))
    HNNExtension.t (HNNExtension.of : ↥H →* HNNExtension ↥H (hnnBaseA H t) (hnnBaseB H t)
      (hnnConjEquiv H t)) L
  simpa [hnnReduced, hnnConjWord, NormalWord.ReducedWord.prod] using h

/-! ## Britton's lemma -/

theorem britton_hnnConjMap_injective {G : Type u} [Group G] (H : Subgroup G) (t : G)
    (hinj : Function.Injective (Work.OROneRel.hnnConjMap H t))
    (L : List (ℤˣ × ↥H)) (hchain : Work.OROneRel.NoPinch H t L)
    (hprod : Work.OROneRel.hnnWord H t L ∈ H) :
    L = [] := by
  have hx : hnnConjWord H t L = HNNExtension.of ⟨hnnWord H t L, hprod⟩ := by
    apply hinj
    rw [hnnConjMap_hnnConjWord, hnnConjMap_of]
  have hmem : NormalWord.ReducedWord.prod (hnnConjEquiv H t) (hnnReduced H t L hchain) ∈
      MonoidHom.range (HNNExtension.of : ↥H →* HNNExtension ↥H (hnnBaseA H t) (hnnBaseB H t)
        (hnnConjEquiv H t)) := by
    rw [hnnReduced_prod, hx]
    exact ⟨(⟨hnnWord H t L, hprod⟩ : ↥H)⁻¹, by simp⟩
  have hnil := HNNExtension.ReducedWord.toList_eq_nil_of_mem_of_range (hnnConjEquiv H t)
    (hnnReduced H t L hchain) hmem
  rw [hnnReduced] at hnil
  exact List.reverse_eq_nil_iff.mp (List.map_eq_nil_iff.mp hnil)

end Work.OROneRel
