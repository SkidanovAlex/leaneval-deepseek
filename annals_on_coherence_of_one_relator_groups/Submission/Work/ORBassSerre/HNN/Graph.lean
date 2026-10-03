/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The Bass--Serre graph of an HNN extension

This file defines the graph on the left coset space `V = E ⧸ ofE.range` whose edges are the pairs
`{⟦h⟧, ⟦h * t⟧}` (`E = HNNExtension G A B φ`, `t` the stable letter), together with the
`t`-length function `N : V → ℕ` descending from `tlen`, and proves the elementary facts needed to
show that this graph is a tree.
-/
import Mathlib
import Submission.Work.ORBassSerre.HNN.Defs

set_option autoImplicit false
set_option linter.unusedVariables false

universe u

namespace Work.ORBassSerre.HNN

open HNNExtension

variable {G : Type u} [Group G] {A B : Subgroup G} {φ : A ≃* B}

/-- The vertex set of the Bass--Serre tree: the left cosets of the image of `G` in the HNN
extension. -/
abbrev VSet := HNNExtension G A B φ ⧸ (ofE (A := A) (B := B) (φ := φ)).range

/-- The class of an element of the HNN extension in the vertex set. -/
abbrev qmk (g : HNNExtension G A B φ) : VSet (A := A) (B := B) (φ := φ) := QuotientGroup.mk g

/-- The base vertex, the coset of the identity (i.e. of the image of `G`). -/
abbrev base : VSet (A := A) (B := B) (φ := φ) := qmk 1

/-- The adjacency relation of the Bass--Serre graph. -/
def adj (X Y : VSet (A := A) (B := B) (φ := φ)) : Prop :=
  ∃ h : HNNExtension G A B φ,
    (X = qmk h ∧ Y = qmk (h * tt)) ∨ (Y = qmk h ∧ X = qmk (h * tt))

theorem adj.symm {X Y : VSet (A := A) (B := B) (φ := φ)} (h : adj X Y) : adj Y X := by
  rcases h with ⟨k, hh⟩
  rcases hh with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact ⟨k, Or.inr ⟨h1, h2⟩⟩
  · exact ⟨k, Or.inl ⟨h1, h2⟩⟩

/-- The relation of having the same class, in terms of the subgroup. -/
theorem qmk_eq_iff {a b : HNNExtension G A B φ} :
    qmk a = qmk b ↔ a⁻¹ * b ∈ (ofE (A := A) (B := B) (φ := φ)).range :=
  QuotientGroup.eq

theorem exists_eq_mul_of_qmk_eq {a b : HNNExtension G A B φ} (h : qmk a = qmk b) :
    ∃ m : G, b = a * ofE m := by
  have h' : a⁻¹ * b ∈ (ofE (A := A) (B := B) (φ := φ)).range := qmk_eq_iff.mp h
  obtain ⟨m, hm⟩ := h'
  exact ⟨m, by rw [hm]; group⟩

@[simp] theorem qmk_mul_of (a : HNNExtension G A B φ) (m : G) :
    qmk (a * ofE m) = qmk a := by
  rw [qmk_eq_iff]
  have h : (a * ofE m)⁻¹ * a = (ofE m)⁻¹ := by group
  rw [h]
  exact Subgroup.inv_mem _ ⟨m, rfl⟩

/-- The `t`-length of the stable letter is `1`. -/
theorem tlen_tt : tlen (tt : HNNExtension G A B φ) = 1 := by
  have h := tlen_eq_of_prod (φ := φ)
    (w := { head := (1 : G), toList := [(1, 1)], chain := List.isChain_singleton _ })
    (g := (tt : HNNExtension G A B φ)) ?_
  · rw [h]; simp
  · show NormalWord.ReducedWord.prod φ
        { head := (1 : G), toList := [(1, 1)], chain := _ } = tt
    simp [NormalWord.ReducedWord.prod, tt]

/-- The stable letter is not in the image of `G`. -/
theorem t_notMem_range : (tt : HNNExtension G A B φ) ∉ (ofE (A := A) (B := B) (φ := φ)).range := by
  intro h
  have h0 : tlen (tt : HNNExtension G A B φ) = 0 := (tlen_eq_zero_iff tt).mpr h
  rw [tlen_tt] at h0
  exact absurd h0 (by norm_num)

theorem adj.irrefl (X : VSet (A := A) (B := B) (φ := φ)) : ¬ adj X X := by
  rintro ⟨h, hh⟩
  rcases hh with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact t_notMem_range (by
      have hm : qmk h = qmk (h * tt) := h1.symm.trans h2
      have := qmk_eq_iff.mp hm
      rwa [← mul_assoc, inv_mul_cancel, one_mul] at this)
  · exact t_notMem_range (by
      have hm : qmk h = qmk (h * tt) := h1.symm.trans h2
      have := qmk_eq_iff.mp hm
      rwa [← mul_assoc, inv_mul_cancel, one_mul] at this)

/-- The Bass--Serre graph. -/
def hnnGraph : SimpleGraph (VSet (A := A) (B := B) (φ := φ)) where
  Adj := adj
  symm := ⟨fun _ _ => adj.symm⟩
  loopless := ⟨fun X => adj.irrefl X⟩

@[simp] theorem hnnGraph_adj {X Y : VSet (A := A) (B := B) (φ := φ)} :
    (hnnGraph (A := A) (B := B) (φ := φ)).Adj X Y ↔ adj X Y := Iff.rfl

/-- The action of the HNN extension on the coset space, expressed on representatives. -/
@[simp] theorem smul_qmk (e g : HNNExtension G A B φ) :
    e • (qmk g : VSet (A := A) (B := B) (φ := φ)) = qmk (e * g) := rfl

theorem smul_adj (e : HNNExtension G A B φ) {X Y : VSet (A := A) (B := B) (φ := φ)}
    (h : adj X Y) : adj (e • X) (e • Y) := by
  rcases h with ⟨k, hh⟩
  rcases hh with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · refine ⟨e * k, Or.inl ⟨?_, ?_⟩⟩
    · rw [h1, smul_qmk]
    · rw [h2, smul_qmk, mul_assoc]
  · refine ⟨e * k, Or.inr ⟨?_, ?_⟩⟩
    · rw [h1, smul_qmk]
    · rw [h2, smul_qmk, mul_assoc]

/-- The `t`-length descends to the vertex set. -/
noncomputable def N (X : VSet (A := A) (B := B) (φ := φ)) : ℕ :=
  Quotient.liftOn X (fun g => tlen g) (by
    intro a b h
    have h' : a⁻¹ * b ∈ (ofE (A := A) (B := B) (φ := φ)).range :=
      QuotientGroup.leftRel_apply.mp h
    obtain ⟨m, hm⟩ := h'
    have hb : b = a * ofE m := by rw [hm]; group
    rw [hb, tlen_mul_of])

@[simp] theorem N_qmk (g : HNNExtension G A B φ) :
    N (qmk (A := A) (B := B) (φ := φ) g) = tlen g := rfl

/-- The vertices with `N = 0` are exactly the base vertex. -/
theorem N_eq_zero_iff (X : VSet (A := A) (B := B) (φ := φ)) :
    N X = 0 ↔ X = base (A := A) (B := B) (φ := φ) := by
  constructor
  · intro h
    obtain ⟨g, rfl⟩ := Quotient.exists_rep X
    have h0 : (tlen g) = 0 := h
    have hg : g ∈ (ofE (A := A) (B := B) (φ := φ)).range := (tlen_eq_zero_iff g).mp h0
    show qmk g = base
    rw [qmk_eq_iff]
    simpa using Subgroup.inv_mem _ hg
  · intro h
    rw [h]
    simpa using (tlen_eq_zero_iff (1 : HNNExtension G A B φ)).mpr (Subgroup.one_mem _)

/-- The neighbours of `⟦g⟧` are exactly the vertices `⟦g * ofE m * t ^ ε⟧`. -/
theorem adj_iff (g : HNNExtension G A B φ) (Y : VSet (A := A) (B := B) (φ := φ)) :
    adj (qmk g) Y ↔ ∃ (m : G) (ε : ℤˣ), Y = qmk (step g m ε) := by
  constructor
  · rintro ⟨h, hh⟩
    rcases hh with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · obtain ⟨m, hm⟩ := exists_eq_mul_of_qmk_eq h1
      exact ⟨m, 1, by rw [h2, hm, step_one]⟩
    · obtain ⟨m, hm⟩ := exists_eq_mul_of_qmk_eq h2
      have hk : h = g * ofE m * tt⁻¹ := by rw [← hm]; group
      exact ⟨m, -1, by rw [h1, hk, step_neg_one]⟩
  · rintro ⟨m, ε, rfl⟩
    rcases Int.units_eq_one_or ε with hε | hε
    · subst hε
      refine ⟨g * ofE m, Or.inl ⟨?_, ?_⟩⟩
      · rw [qmk_eq_iff]
        have h : g⁻¹ * (g * ofE m) = ofE m := by group
        rw [h]; exact ⟨m, rfl⟩
      · rw [step_one]
    · subst hε
      refine ⟨g * ofE m * tt⁻¹, Or.inr ⟨?_, ?_⟩⟩
      · rw [step_neg_one]
      · rw [qmk_eq_iff]
        have h : g⁻¹ * ((g * ofE m * tt⁻¹) * tt) = ofE m := by group
        rw [h]; exact ⟨m, rfl⟩

end Work.ORBassSerre.HNN
