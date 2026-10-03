/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The Bass--Serre tree of an HNN extension: definitions and the `t`-length

This file sets up the combinatorial data used to build the Bass--Serre tree of an HNN
extension `E = HNNExtension G A B φ`.

* `ofE` is the canonical map `G →* E`;
* `RedWord` is the type of reduced words in `G ∗ ℤ` presenting `E` (Mathlib's
  `NormalWord.ReducedWord`);
* `tlen g` is the number of `t`-letters in a reduced word representing `g`; it is well defined
  (`tlen_eq_of_prod`) and invariant under right multiplication by elements of `ofE.range`
  (`tlen_mul_of`), hence descends to a function on the left coset space `E ⧸ ofE.range`.
-/
import Mathlib
import Submission.Work.ORBassSerre.Interface

set_option autoImplicit false
set_option linter.unusedVariables false

universe u

namespace Work.ORBassSerre.HNN

open HNNExtension

variable {G : Type u} [Group G] {A B : Subgroup G} {φ : A ≃* B}

/-- Reduced words of the coproduct `G ∗ ℤ` presenting the HNN extension `E`. -/
abbrev RedWord := NormalWord.ReducedWord G A B

/-- The canonical map `G →* HNNExtension G A B φ`. -/
abbrev ofE : G →* HNNExtension G A B φ := HNNExtension.of (A := A) (B := B) (φ := φ)

/-- The stable letter of the HNN extension. -/
abbrev tt : HNNExtension G A B φ := HNNExtension.t

/-- The stable letter raised to the (unit) power `ε`. -/
abbrev tpow (ε : ℤˣ) : HNNExtension G A B φ := (tt : HNNExtension G A B φ) ^ (ε : ℤ)

@[simp] theorem tpow_one : tpow (A := A) (B := B) (φ := φ) (1 : ℤˣ) = tt := by simp [tpow]

@[simp] theorem tpow_neg_one : tpow (A := A) (B := B) (φ := φ) (-1 : ℤˣ) = tt⁻¹ := by simp [tpow]

theorem tpow_inv (ε : ℤˣ) :
    (tpow (A := A) (B := B) (φ := φ) ε)⁻¹ = tpow (-ε) := by
  simp only [tpow, Units.val_neg, zpow_neg]

/-- The element `g * of m * t ^ ε`, a generic neighbour of `g` in the Bass--Serre tree. -/
abbrev step (g : HNNExtension G A B φ) (m : G) (ε : ℤˣ) : HNNExtension G A B φ :=
  g * ofE m * tpow (A := A) (B := B) (φ := φ) ε

@[simp] theorem step_eq (g : HNNExtension G A B φ) (m : G) (ε : ℤˣ) :
    step (A := A) (B := B) (φ := φ) g m ε = g * ofE m * tpow ε := rfl

@[simp] theorem step_one (g : HNNExtension G A B φ) (m : G) :
    step (A := A) (B := B) (φ := φ) g m 1 = g * ofE m * tt := by
  show g * ofE m * tpow (A := A) (B := B) (φ := φ) (1 : ℤˣ) = g * ofE m * tt
  rw [tpow_one]

@[simp] theorem step_neg_one (g : HNNExtension G A B φ) (m : G) :
    step (A := A) (B := B) (φ := φ) g m (-1) = g * ofE m * tt⁻¹ := by
  show g * ofE m * tpow (A := A) (B := B) (φ := φ) (-1 : ℤˣ) = g * ofE m * tt⁻¹
  rw [tpow_neg_one]

/-- The element of the HNN extension represented by a reduced word. -/
abbrev redProd (φ' : A ≃* B) (w : RedWord (A := A) (B := B)) : HNNExtension G A B φ' :=
  NormalWord.ReducedWord.prod φ' w

/-- Every element of the HNN extension is the product of a reduced word. -/
theorem exists_reducedWord (g : HNNExtension G A B φ) :
    ∃ w : RedWord (A := A) (B := B), NormalWord.ReducedWord.prod φ w = g := by
  classical
  obtain ⟨d⟩ := NormalWord.TransversalPair.nonempty G A B
  exact ⟨((NormalWord.equiv φ d) g).toReducedWord, (NormalWord.equiv φ d).left_inv g⟩

/-- The number of `t`-letters of an element of the HNN extension (the "`t`-length"). -/
noncomputable def tlen (g : HNNExtension G A B φ) : ℕ :=
  (Classical.choose (exists_reducedWord (A := A) (B := B) (φ := φ) g)).toList.length

/-- `tlen` is computed by any reduced word representing the element. -/
theorem tlen_prod (w : RedWord (A := A) (B := B)) :
    tlen (NormalWord.ReducedWord.prod φ w) = w.toList.length := by
  rw [tlen]
  have h2 := HNNExtension.ReducedWord.map_fst_eq_and_of_prod_eq (φ := φ)
    (w₁ := Classical.choose
      (exists_reducedWord (A := A) (B := B) (φ := φ) (NormalWord.ReducedWord.prod φ w)))
    (w₂ := w)
    (Classical.choose_spec
      (exists_reducedWord (A := A) (B := B) (φ := φ) (NormalWord.ReducedWord.prod φ w)))
  have h3 := congrArg List.length h2.1
  rw [List.length_map, List.length_map] at h3
  exact h3

theorem tlen_eq_of_prod {w : RedWord (A := A) (B := B)} {g : HNNExtension G A B φ}
    (h : NormalWord.ReducedWord.prod φ w = g) : tlen g = w.toList.length := by
  rw [← h]; exact tlen_prod w

/-- `tlen g = 0` exactly for the elements of the image of `G`. -/
theorem tlen_eq_zero_iff (g : HNNExtension G A B φ) : tlen g = 0 ↔ g ∈ ofE.range := by
  constructor
  · intro h
    rw [tlen] at h
    have hnil : (Classical.choose (exists_reducedWord (A := A) (B := B) (φ := φ) g)).toList = [] :=
      List.eq_nil_of_length_eq_zero h
    have hprod := Classical.choose_spec (exists_reducedWord (A := A) (B := B) (φ := φ) g)
    rw [← hprod]
    refine ⟨(Classical.choose (exists_reducedWord (A := A) (B := B) (φ := φ) g)).head, ?_⟩
    show HNNExtension.of (Classical.choose
        (exists_reducedWord (A := A) (B := B) (φ := φ) g)).head
        = NormalWord.ReducedWord.prod φ (Classical.choose
          (exists_reducedWord (A := A) (B := B) (φ := φ) g))
    rw [NormalWord.ReducedWord.prod, hnil]; simp
  · rintro ⟨k, rfl⟩
    refine tlen_eq_of_prod (w := { head := k, toList := [], chain := List.isChain_nil }) ?_
    simp [NormalWord.ReducedWord.prod]

/-- `tlen` is invariant under right multiplication by an element of the image of `G`
(equivalently: it is constant on the left cosets of `ofE.range`). -/
theorem tlen_mul_of (g : HNNExtension G A B φ) (m : G) : tlen (g * ofE m) = tlen g := by
  obtain ⟨w, hw⟩ := exists_reducedWord (A := A) (B := B) (φ := φ) g
  rw [tlen_eq_of_prod hw]
  by_cases hnil : w.toList = []
  · have hwhead : NormalWord.ReducedWord.prod φ w = HNNExtension.of w.head := by
      rw [NormalWord.ReducedWord.prod, hnil]; simp
    have hz : tlen (g * ofE m) = 0 := by
      rw [tlen_eq_zero_iff, ← hw, hwhead]
      exact ⟨w.head * m, by simp⟩
    rw [hz, List.length_eq_zero_iff.mpr hnil]
  · have hchain := w.chain
    rw [← List.dropLast_append_getLast hnil] at hchain
    obtain ⟨ha, _, hb⟩ := List.isChain_append.mp hchain
    have hchain' : List.IsChain (fun a b => a.2 ∈ toSubgroup A B a.1 → a.1 = b.1)
        (w.toList.dropLast ++ [((w.toList.getLast hnil).1, (w.toList.getLast hnil).2 * m)]) := by
      refine List.isChain_append.mpr ⟨ha, List.isChain_singleton _, ?_⟩
      intro y hy z hz
      simp only [List.head?_singleton, Option.mem_some_iff] at hz
      subst hz
      have h3 := hb y hy (w.toList.getLast hnil) (by simp)
      simpa using h3
    set w' : RedWord (A := A) (B := B) :=
      { head := w.head
        toList := w.toList.dropLast ++ [((w.toList.getLast hnil).1, (w.toList.getLast hnil).2 * m)]
        chain := hchain' } with hw'
    have hprod' : NormalWord.ReducedWord.prod φ w' = g * ofE m := by
      rw [← hw]
      show NormalWord.ReducedWord.prod φ w' = NormalWord.ReducedWord.prod φ w * ofE m
      simp only [NormalWord.ReducedWord.prod]
      rw [show w'.toList = w.toList.dropLast ++
          [((w.toList.getLast hnil).1, (w.toList.getLast hnil).2 * m)] from rfl]
      conv_rhs => rw [← List.dropLast_append_getLast hnil]
      simp only [List.map_append, List.map_singleton, List.prod_append, List.prod_singleton,
        ofE, map_mul]
      rw [show w'.head = w.head from rfl]
      group
    have hlen : w'.toList.length = w.toList.length := by
      rw [show w'.toList = w.toList.dropLast ++
          [((w.toList.getLast hnil).1, (w.toList.getLast hnil).2 * m)] from rfl]
      have e1 : (w.toList.dropLast ++
            [((w.toList.getLast hnil).1, (w.toList.getLast hnil).2 * m)]).length
          = (w.toList.dropLast ++ [w.toList.getLast hnil]).length := by simp
      rw [e1, List.dropLast_append_getLast hnil]
    rw [← hprod', tlen_prod w', hlen]

end Work.ORBassSerre.HNN
