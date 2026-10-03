/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Alternating lists of elements of the factors of a free product

`Work.ORBassSerre.CoprodTree.Defs` interprets a path in the Bass--Serre tree of `A ∗ B` as a
sequence of "steps", each lying in the factor of the side at which it is taken
(`sideFactor A B (sideAfter s j)` for the `j`-th step).  This file isolates the combinatorial
content of the resulting contradiction: a non-empty list of elements of the two factors, each
entry lying in the factor prescribed by the alternating side sequence and each entry non-trivial,
has non-trivial product in `A ∗ B`
(`Work.ORBassSerre.CoprodTree.altList_prod_ne_one`).

The proof of that theorem reduces to the normal form theorem for free products
(`Work.ORBassSerre.CoprodTree.coprod_mk_injective_of_isReduced_univ`) by choosing, for each entry,
its preimage under `inl` or `inr`; the present file contains the supporting definitions: the
alternating side sequence, the letter map of the free product, and the extraction of letters.
-/
import Mathlib
import Submission.Work.ORBassSerre.CoprodTree.NormalFormDefs
import Submission.Work.ORBassSerre.CoprodTree.Defs

set_option autoImplicit false
set_option linter.unusedVariables false

universe u v w

namespace Work.ORBassSerre.CoprodTree

open Monoid

variable {A : Type u} {B : Type v} [Group A] [Group B]

/-- The image of a letter in the free product. -/
def letter {A : Type u} {B : Type v} [MulOneClass A] [MulOneClass B] :
    A ⊕ B → Monoid.Coprod A B
  | Sum.inl a => Monoid.Coprod.inl a
  | Sum.inr b => Monoid.Coprod.inr b

@[simp] theorem letter_inl {A : Type u} {B : Type v} [MulOneClass A] [MulOneClass B] (a : A) :
    letter (Sum.inl a : A ⊕ B) = Monoid.Coprod.inl a := rfl
@[simp] theorem letter_inr {A : Type u} {B : Type v} [MulOneClass A] [MulOneClass B] (b : B) :
    letter (Sum.inr b : A ⊕ B) = Monoid.Coprod.inr b := rfl

theorem letter_ne_one_of_ne {c : A ⊕ B} (h : c ≠ Sum.inl 1) (h' : c ≠ Sum.inr 1) :
    letter c ≠ 1 := by
  rcases c with a | b
  · rw [letter_inl]
    intro hh
    exact h (congrArg Sum.inl (Monoid.Coprod.inl_injective (by rw [hh, map_one])))
  · rw [letter_inr]
    intro hh
    exact h' (congrArg Sum.inr (Monoid.Coprod.inr_injective (by rw [hh, map_one])))

/-- The side reached after `n` steps starting from the side `s`. -/
def sideAfter (s : Bool) (n : ℕ) : Bool := if n % 2 = 0 then s else !s

@[simp] theorem sideAfter_zero (s : Bool) : sideAfter s 0 = s := by simp [sideAfter]

theorem sideAfter_succ (s : Bool) (n : ℕ) : sideAfter s (n + 1) = !(sideAfter s n) := by
  have hn := Nat.mod_two_eq_zero_or_one n
  rcases hn with hn | hn
  · have h1 : (n + 1) % 2 = 1 := by omega
    simp [sideAfter, hn, h1]
  · have h1 : (n + 1) % 2 = 0 := by omega
    simp [sideAfter, hn, h1]

theorem sideAfter_ne (s : Bool) (n : ℕ) : sideAfter s (n + 1) ≠ sideAfter s n := by
  rw [sideAfter_succ]
  cases sideAfter s n <;> simp

theorem sideAfter_shift (s : Bool) (n : ℕ) : sideAfter s (n + 1) = sideAfter (!s) n := by
  induction n with
  | zero => simp [sideAfter]
  | succ k ih => rw [sideAfter_succ, ih, sideAfter_succ]

theorem sideAfter_not (s : Bool) (n : ℕ) : sideAfter (!s) n = !(sideAfter s n) := by
  rw [← sideAfter_shift s n, sideAfter_succ]

/-- If `x` lies in the factor of the side `s`, it is the image in the free product of a letter of
that factor. -/
theorem exists_letter_of_mem_sideFactor (s : Bool) {x : Monoid.Coprod A B}
    (hx : x ∈ sideFactor A B s) : ∃ c : A ⊕ B, letter c = x := by
  cases s
  · obtain ⟨b, rfl⟩ := hx
    exact ⟨Sum.inr b, rfl⟩
  · obtain ⟨a, rfl⟩ := hx
    exact ⟨Sum.inl a, rfl⟩

end Work.ORBassSerre.CoprodTree
