/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The Bass--Serre graph of an HNN extension is a tree

Given an HNN extension `E = HNNExtension G A B φ`, this file proves that the graph `hnnGraph` on
the left coset space `E ⧸ ofE.range` (whose edges are `{⟦h⟧, ⟦h * t⟧}`) is a tree.  The proof uses
the `t`-length function `N`:

* along every edge `N` changes by `±1` (`N_adj`);
* every vertex other than the base has a unique neighbour with `N` one smaller
  (`parent_unique`, `parent_exists`);

and then the general combinatorial lemma `isTreeOfParent` produces the tree structure.  Finally the
vertex stabilizers are identified with the conjugates of the image of `G` (`stabilizer_qmk`).
-/
import Mathlib
import Submission.Work.ORBassSerre.HNN.Graph
import Submission.Work.ORBassSerre.HNN.tlenStepMinusB
import Submission.Work.ORBassSerre.HNN.tlenStepPlus
import Submission.Work.ORBassSerre.HNN.tconjMemRange
import Submission.Work.ORBassSerre.HNN.isTreeOfParent

set_option autoImplicit false
set_option linter.unusedVariables false

universe u

namespace Work.ORBassSerre.HNN

open HNNExtension

variable {G : Type u} [Group G] {A B : Subgroup G} {φ : A ≃* B}

/-- The `t`-length of an element of the form `of k * t ^ ε` is `1`. -/
theorem tlen_ofE_mul_tpow (k : G) (ε : ℤˣ) :
    tlen (A := A) (B := B) (φ := φ)
      (ofE (A := A) (B := B) (φ := φ) k * tpow (A := A) (B := B) (φ := φ) ε) = 1 := by
  have h := tlen_eq_of_prod (φ := φ)
    (w := { head := k, toList := [(ε, 1)], chain := List.isChain_singleton _ })
    (g := ofE k * tpow (A := A) (B := B) (φ := φ) ε) ?_
  · rw [h]; simp
  · show NormalWord.ReducedWord.prod φ
        { head := k, toList := [(ε, 1)], chain := _ } = ofE k * tpow ε
    simp [NormalWord.ReducedWord.prod, tpow]

/-- Along an edge of the Bass--Serre graph, the `t`-length changes by `±1`. -/
theorem N_adj {X Y : VSet (A := A) (B := B) (φ := φ)} (h : adj X Y) :
    N Y = N X + 1 ∨ N X = N Y + 1 := by
  obtain ⟨g, rfl⟩ := Quotient.exists_rep X
  obtain ⟨m, ε, rfl⟩ := (adj_iff g Y).mp h
  simp only [N_qmk]
  obtain ⟨w, hw⟩ := exists_reducedWord (A := A) (B := B) (φ := φ) g
  rw [← hw, tlen_prod w]
  by_cases hnil : w.toList = []
  · left
    have hwhead : redProd (A := A) (B := B) φ w = ofE w.head := by
      rw [redProd, NormalWord.ReducedWord.prod, hnil]; simp
    have hstep : step (redProd φ w) m ε = ofE (w.head * m) * tpow ε := by
      simp only [step_eq, hwhead, map_mul]
    rw [hstep, tlen_ofE_mul_tpow, List.length_eq_zero_iff.mpr hnil]
  · obtain ⟨L₁, u, x, hwx⟩ : ∃ (L₁ : List (ℤˣ × G)) (u : ℤˣ) (x : G),
        w.toList = L₁ ++ [(u, x)] :=
      ⟨w.toList.dropLast, (w.toList.getLast hnil).1, (w.toList.getLast hnil).2,
        (List.dropLast_append_getLast hnil).symm⟩
    by_cases hcase : u = -ε ∧ x * m ∈ HNNExtension.toSubgroup A B u
    · right
      have h1 := tlenStepMinusB (φ := φ) w m ε L₁ u x hwx hcase.1 hcase.2
      exact h1.symm
    · left
      exact tlenStepPlus (φ := φ) w m ε L₁ u x hwx hcase

/-- A non-base vertex has at most one neighbour whose `t`-length is one smaller. -/
theorem parent_unique (X : VSet (A := A) (B := B) (φ := φ)) :
    ∀ Y Z, adj X Y → adj X Z → N Y + 1 = N X → N Z + 1 = N X → Y = Z := by
  obtain ⟨g, rfl⟩ := Quotient.exists_rep X
  intro Y Z hY hZ eY eZ
  obtain ⟨m₁, ε₁, rfl⟩ := (adj_iff g Y).mp hY
  obtain ⟨m₂, ε₂, rfl⟩ := (adj_iff g Z).mp hZ
  simp only [N_qmk] at eY eZ
  obtain ⟨w, hw⟩ := exists_reducedWord (A := A) (B := B) (φ := φ) g
  rw [← hw, tlen_prod w] at eY eZ
  by_cases hnil : w.toList = []
  · exfalso
    rw [List.length_eq_zero_iff.mpr hnil] at eY
    omega
  · obtain ⟨L₁, u, x, hwx⟩ : ∃ (L₁ : List (ℤˣ × G)) (u : ℤˣ) (x : G),
        w.toList = L₁ ++ [(u, x)] :=
      ⟨w.toList.dropLast, (w.toList.getLast hnil).1, (w.toList.getLast hnil).2,
        (List.dropLast_append_getLast hnil).symm⟩
    have key : ∀ (m : G) (ε : ℤˣ), tlen (step (redProd φ w) m ε) + 1 = w.toList.length →
        (u = -ε ∧ x * m ∈ HNNExtension.toSubgroup A B u) := by
      intro m ε he
      by_contra hcon
      have hplus := tlenStepPlus (φ := φ) w m ε L₁ u x hwx hcon
      omega
    obtain ⟨hu₁, hx₁⟩ := key m₁ ε₁ eY
    obtain ⟨hu₂, hx₂⟩ := key m₂ ε₂ eZ
    have hε₁ : ε₁ = -u := by rw [hu₁, neg_neg]
    have hε₂ : ε₂ = -u := by rw [hu₂, neg_neg]
    rw [hε₁, hε₂]
    rw [qmk_eq_iff]
    simp only [step_eq, hw]
    have hm : m₁⁻¹ * m₂ ∈ HNNExtension.toSubgroup A B u := by
      have h1 : (x * m₁)⁻¹ * (x * m₂) ∈ HNNExtension.toSubgroup A B u :=
        (HNNExtension.toSubgroup A B u).mul_mem
          ((HNNExtension.toSubgroup A B u).inv_mem hx₁) hx₂
      have h2 : (x * m₁)⁻¹ * (x * m₂) = m₁⁻¹ * m₂ := by group
      rwa [h2] at h1
    have hconj : tpow (A := A) (B := B) (φ := φ) u *
        ofE (m₁⁻¹ * m₂) * tpow (A := A) (B := B) (φ := φ) (-u) ∈
        (ofE (A := A) (B := B) (φ := φ)).range :=
      (tconjMemRange (A := A) (B := B) (φ := φ) u (m₁⁻¹ * m₂)).mpr hm
    have heq : (g * ofE (A := A) (B := B) (φ := φ) m₁ *
            tpow (A := A) (B := B) (φ := φ) (-u))⁻¹ *
          (g * ofE (A := A) (B := B) (φ := φ) m₂ *
            tpow (A := A) (B := B) (φ := φ) (-u)) =
        tpow (A := A) (B := B) (φ := φ) u * ofE (A := A) (B := B) (φ := φ) (m₁⁻¹ * m₂) *
          tpow (A := A) (B := B) (φ := φ) (-u) := by
      have h1 : (g * ofE m₁ * tpow (A := A) (B := B) (φ := φ) (-u))⁻¹ =
          tpow u * (ofE m₁)⁻¹ * g⁻¹ := by
        rw [mul_inv_rev, mul_inv_rev, tpow_inv, neg_neg]
        group
      have h2 : tpow u * (ofE m₁)⁻¹ * g⁻¹ * (g * ofE m₂ * tpow (-u)) =
          tpow u * ((ofE m₁)⁻¹ * ofE m₂) * tpow (-u) := by group
      have h3 : (ofE (A := A) (B := B) (φ := φ) m₁)⁻¹ * ofE (A := A) (B := B) (φ := φ) m₂ =
          ofE (A := A) (B := B) (φ := φ) (m₁⁻¹ * m₂) := by
        rw [← map_inv, ← map_mul]
      rw [h1, h2, h3]
    rw [heq]
    exact hconj

/-- A non-base vertex has a neighbour whose `t`-length is one smaller. -/
theorem parent_exists (X : VSet (A := A) (B := B) (φ := φ)) (hX : X ≠ base) :
    ∃ Y, adj X Y ∧ N Y + 1 = N X := by
  obtain ⟨g, rfl⟩ := Quotient.exists_rep X
  obtain ⟨w, hw⟩ := exists_reducedWord (A := A) (B := B) (φ := φ) g
  have hgne : tlen g ≠ 0 := by
    intro h0
    exact hX ((N_eq_zero_iff (qmk g)).mp h0)
  have hnil : w.toList ≠ [] := by
    intro h
    exact hgne (by rw [tlen_eq_of_prod hw, List.length_eq_zero_iff.mpr h])
  obtain ⟨L₁, u, x, hwx⟩ : ∃ (L₁ : List (ℤˣ × G)) (u : ℤˣ) (x : G),
      w.toList = L₁ ++ [(u, x)] :=
    ⟨w.toList.dropLast, (w.toList.getLast hnil).1, (w.toList.getLast hnil).2,
      (List.dropLast_append_getLast hnil).symm⟩
  refine ⟨qmk (step g x⁻¹ (-u)), (adj_iff g _).mpr ⟨x⁻¹, -u, rfl⟩, ?_⟩
  simp only [N_qmk]
  rw [← hw, tlen_prod w]
  have hone : x * x⁻¹ ∈ HNNExtension.toSubgroup A B u := by
    rw [mul_inv_cancel]
    exact (HNNExtension.toSubgroup A B u).one_mem
  have h1 := tlenStepMinusB (φ := φ) w x⁻¹ (-u) L₁ u x hwx (by simp) hone
  omega

/-- **The Bass--Serre graph of an HNN extension is a tree.** -/
theorem hnnGraph_isTree : (hnnGraph (A := A) (B := B) (φ := φ)).IsTree :=
  isTreeOfParent (hnnGraph (A := A) (B := B) (φ := φ))
    (N (A := A) (B := B) (φ := φ)) (base (A := A) (B := B) (φ := φ))
    (fun _ _ h => N_adj h) parent_unique parent_exists N_eq_zero_iff

/-- The stabilizer of a vertex `⟦g⟧` is the conjugate of the image of `G` by `g`. -/
theorem stabilizer_qmk (g : HNNExtension G A B φ) :
    MulAction.stabilizer (HNNExtension G A B φ) (qmk g) =
      (ofE (A := A) (B := B) (φ := φ)).range.map
        (MulEquiv.toMonoidHom (MulAut.conj g)) := by
  ext e
  rw [MulAction.mem_stabilizer_iff, Subgroup.mem_map]
  constructor
  · intro h
    have h' : g⁻¹ * e * g ∈ (ofE (A := A) (B := B) (φ := φ)).range := by
      have h2 : (e * g)⁻¹ * g ∈ (ofE (A := A) (B := B) (φ := φ)).range := by
        rw [← qmk_eq_iff, ← smul_qmk]
        exact h
      have h3 : g⁻¹ * e * g = ((e * g)⁻¹ * g)⁻¹ := by group
      rw [h3]
      exact Subgroup.inv_mem _ h2
    refine ⟨g⁻¹ * e * g, h', ?_⟩
    show MulAut.conj g (g⁻¹ * e * g) = e
    rw [MulAut.conj_apply]; group
  · rintro ⟨k, hk, rfl⟩
    rw [smul_qmk, qmk_eq_iff]
    obtain ⟨m, rfl⟩ := hk
    have h1 : ((MulEquiv.toMonoidHom (MulAut.conj g)) (ofE m) * g)⁻¹ * g =
        (ofE m)⁻¹ := by
      show ((MulAut.conj g) (ofE m) * g)⁻¹ * g = (ofE m)⁻¹
      rw [MulAut.conj_apply]; group
    rw [h1]
    exact Subgroup.inv_mem _ ⟨m, rfl⟩

end Work.ORBassSerre.HNN
