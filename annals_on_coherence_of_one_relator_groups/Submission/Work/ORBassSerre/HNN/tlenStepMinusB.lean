/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The `t`-length after a step that cancels

If the reduced word `w` ends in the letter `(u, x)` and `x * m ∈ toSubgroup A B u` with
`u = -ε`, then multiplying `w.prod` by `of m` and by `t ^ ε` removes the last `t`-letter:
`tlen (w.prod * of m * t^ε) + 1 = w.toList.length`.
-/
import Mathlib
import Submission.Work.ORBassSerre.HNN.Defs

set_option autoImplicit false
set_option linter.unusedVariables false

universe u

namespace Work.ORBassSerre.HNN

open HNNExtension

variable {G : Type u} [Group G] {A B : Subgroup G} {φ : A ≃* B}

theorem tlenStepMinusB (w : RedWord (A := A) (B := B)) (m : G) (ε : ℤˣ)
    (L₁ : List (ℤˣ × G)) (u : ℤˣ) (x : G)
    (hw : w.toList = L₁ ++ [(u, x)]) (hu : u = -ε)
    (hx : x * m ∈ HNNExtension.toSubgroup A B u) :
    tlen (step (redProd φ w) m ε) + 1 = w.toList.length := by
  classical
  have hchain₁ : List.IsChain
      (fun a b : ℤˣ × G => a.2 ∈ HNNExtension.toSubgroup A B a.1 → a.1 = b.1) L₁ := by
    have h := w.chain
    rw [hw] at h
    exact (List.isChain_append.mp h).1
  -- the reduced word obtained by deleting the last letter of `w`
  set w₁ : RedWord (A := A) (B := B) :=
    { head := w.head, toList := L₁, chain := hchain₁ } with hw₁
  -- `t^u * of (x*m) * t^(-u)` lies in the base group
  have hconj : ∃ y : G, tpow (A := A) (B := B) (φ := φ) u * ofE (x * m) *
      tpow (A := A) (B := B) (φ := φ) (-u) = ofE y := by
    rcases Int.units_eq_one_or u with rfl | rfl
    · have hxA : x * m ∈ A := by simpa using hx
      refine ⟨(φ ⟨x * m, hxA⟩ : B), ?_⟩
      rw [tpow_one, tpow_neg_one, HNNExtension.equiv_eq_conj]
    · have hxB : x * m ∈ B := by simpa using hx
      refine ⟨(φ.symm ⟨x * m, hxB⟩ : A), ?_⟩
      rw [tpow_neg_one, neg_neg, tpow_one, HNNExtension.equiv_symm_eq_conj]
  obtain ⟨y, hy⟩ := hconj
  have hε : ε = -u := by rw [hu, neg_neg]
  -- the product decomposes as `redProd w₁ * (t^u * of x)`
  have hred : redProd (A := A) (B := B) φ w =
      redProd (A := A) (B := B) φ w₁ *
        (tpow (A := A) (B := B) (φ := φ) u * ofE x) := by
    rw [hw₁]
    simp only [NormalWord.ReducedWord.prod]
    rw [hw]
    simp only [List.map_append, List.map_singleton, List.prod_append, List.prod_singleton, tpow]
    group
  have hstep : step (redProd φ w) m ε = redProd φ w₁ * ofE y := by
    rw [step_eq, hred, hε]
    have hassoc : redProd φ w₁ * (tpow u * ofE x) * ofE m *
          tpow (A := A) (B := B) (φ := φ) (-u) =
        redProd φ w₁ * (tpow u * (ofE x * ofE m) * tpow (-u)) := by group
    rw [hassoc, ← map_mul, hy]
  rw [hstep, tlen_mul_of, tlen_prod w₁, hw, hw₁]
  simp

end Work.ORBassSerre.HNN
