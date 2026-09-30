/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import Submission.Work.Subdivision.OrderComplex

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# `D ∘ D = 0` for the order-complex differential

`D k` is the alternating sum of the face maps on the free `ℤ`-module on the
`k`-simplices of the order complex of a poset `α` (see
`Submission.Work.Subdivision.OrderComplex`).  This file proves the fundamental
chain-complex identity

  `(D k).comp (D (k+1)) = 0`

i.e. that consecutive differentials compose to zero.

The proof follows the classical double-sum cancellation: expanding the
composite as `∑_{i,j} (-1)^{i+j} d_i d_j` and using the cosimplicial identity
`d_i d_j = d_{j-1} d_i` (`Simplex.face_face`) for `i < j`, the index set
`Fin (k+2) × Fin (k+3)` is split into `S = {j ≤ i}` and its complement, and the
map `(i,j) ↦ (j, i+1)` is a bijection `S → Sᶜ` (this is Mathlib's
`Fin.predAbove` / `Fin.succAbove` correspondence) which changes the sign of the
summand.  Hence the two halves of the sum cancel.
-/

namespace Work.Subdivision

universe u

/-- Extensionality for linear maps out of the free `ℤ`-module on the
`n`-simplices: it suffices to check equality on the basis vectors
`Finsupp.single σ 1`. -/
theorem chainMod_ext {α : Type u} [Preorder α] [DecidableEq α] {M : Type*}
    [AddCommMonoid M] [Module ℤ M] {n : ℕ} {f g : chainMod α n →ₗ[ℤ] M}
    (h : ∀ σ : Simplex α n, f (Finsupp.single σ (1 : ℤ)) = g (Finsupp.single σ (1 : ℤ))) :
    f = g := by
  apply Finsupp.lhom_ext
  intro σ b
  rw [← Finsupp.smul_single_one σ b, map_smul, map_smul, h σ]

/-- `Simplex.face_face` in the case `j ≤ i`: deleting the vertex `j` and then
the vertex `i` of a `(k+2)`-simplex is the same as deleting `i + 1` and then
`j`.  This is the form of the simplicial identity used in the cancellation
argument (it exhibits `(i,j) ↦ (j, i+1)`). -/
theorem face_face_le {α : Type u} [Preorder α] (k : ℕ) (i : Fin (k + 2)) (j : Fin (k + 3))
    (h : (j : ℕ) ≤ (i : ℕ)) (σ : Simplex α (k + 2)) :
    Simplex.face i (Simplex.face j σ)
      = Simplex.face (Fin.castLT j (lt_of_le_of_lt h i.isLt)) (Simplex.face (i.succ) σ) := by
  have he : j ≤ i.castSucc := h
  have h1 : i.predAbove j = Fin.castLT j (lt_of_le_of_lt h i.isLt) := by
    rw [Fin.predAbove_of_le_castSucc _ _ he, Fin.castPred]
  have h2 : j.succAbove i = i.succ := Fin.succAbove_of_le_castSucc _ _ he
  rw [Simplex.face_face, h1, h2]

/-- The linear-map form of `face_face_le`. -/
theorem faceLM_comp_le {α : Type u} [Preorder α] [DecidableEq α] (k : ℕ) (i : Fin (k + 2))
    (j : Fin (k + 3)) (h : (j : ℕ) ≤ (i : ℕ)) :
    (faceLM (α := α) (k := k) i).comp (faceLM (α := α) (k := k + 1) j)
      = (faceLM (α := α) (k := k) (Fin.castLT j (lt_of_le_of_lt h i.isLt))).comp
          (faceLM (α := α) (k := k + 1) i.succ) := by
  apply chainMod_ext
  intro σ
  simp only [LinearMap.comp_apply, faceLM_single]
  rw [face_face_le k i j h σ]

/-- The applied form of `face_face_le`. -/
theorem faceLM_apply_le {α : Type u} [Preorder α] [DecidableEq α] (k : ℕ) (i : Fin (k + 2))
    (j : Fin (k + 3)) (h : (j : ℕ) ≤ (i : ℕ)) (x : chainMod α (k + 2)) :
    (faceLM (α := α) (k := k) i) ((faceLM (α := α) (k := k + 1) j) x)
      = (faceLM (α := α) (k := k) (Fin.castLT j (lt_of_le_of_lt h i.isLt)))
          ((faceLM (α := α) (k := k + 1) i.succ) x) := by
  rw [← LinearMap.comp_apply, ← LinearMap.comp_apply, faceLM_comp_le k i j h]

/-- The double sum that `(D k) ∘ (D (k+1))` produces on a basis vector,
arranged as a sum over `Fin (k+2) × Fin (k+3)`, vanishes.  This is the
double-sum cancellation at the heart of `D ∘ D = 0`. -/
theorem sum_pair_zero {α : Type u} [Preorder α] [DecidableEq α] (k : ℕ) (σ : Simplex α (k + 2)) :
    (∑ p : Fin (k + 2) × Fin (k + 3),
      (-1 : ℤ) ^ ((p.1 : ℕ) + (p.2 : ℕ)) • (faceLM (α := α) (k := k) p.1)
        ((faceLM (α := α) (k := k + 1) p.2) (Finsupp.single σ 1))) = 0 := by
  let φ : ∀ a : Fin (k + 2) × Fin (k + 3),
      a ∈ Finset.univ.filter (fun p : Fin (k + 2) × Fin (k + 3) => (p.2 : ℕ) ≤ (p.1 : ℕ)) →
      Fin (k + 2) × Fin (k + 3) :=
    fun a ha => (Fin.castLT a.2 (lt_of_le_of_lt (Finset.mem_filter.mp ha).2 a.1.isLt), a.1.succ)
  rw [← Finset.sum_add_sum_compl
      (Finset.univ.filter (fun p : Fin (k + 2) × Fin (k + 3) => (p.2 : ℕ) ≤ (p.1 : ℕ)))
      (fun p : Fin (k + 2) × Fin (k + 3) =>
        (-1 : ℤ) ^ ((p.1 : ℕ) + (p.2 : ℕ)) • (faceLM (α := α) (k := k) p.1)
          ((faceLM (α := α) (k := k + 1) p.2) (Finsupp.single σ 1)))]
  rw [← eq_neg_iff_add_eq_zero, ← Finset.sum_neg_distrib]
  apply Finset.sum_bij φ
  · rintro ⟨i, j⟩ hj
    simp only [φ, Finset.mem_compl, Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
    simp only [Fin.val_castLT, Fin.val_succ]
    omega
  · rintro ⟨i, j⟩ hij ⟨i', j'⟩ hij' h
    have h1 : i = i' := by
      have := congr_arg Prod.snd h
      simpa [φ] using this
    have h2 : j = j' := by
      have := congr_arg Fin.castSucc (congr_arg Prod.fst h)
      simpa [φ, Fin.castSucc_castLT] using this
    rw [h1, h2]
  · rintro ⟨i', j'⟩ hij'
    simp only [Finset.mem_compl, Finset.mem_filter, Finset.mem_univ, true_and, not_le] at hij'
    refine ⟨(j'.pred ?_, i'.castSucc), ?_, ?_⟩
    · intro h
      rw [h] at hij'
      simp at hij'
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fin.val_castSucc, Fin.val_pred]
      omega
    · simp only [φ, Fin.castLT_castSucc, Fin.succ_pred]
  · rintro ⟨i, j⟩ hj
    have hφ : φ (i, j) hj
        = (Fin.castLT j (lt_of_le_of_lt (Finset.mem_filter.mp hj).2 i.isLt), i.succ) := rfl
    rw [hφ, faceLM_apply_le k i j (Finset.mem_filter.mp hj).2 (Finsupp.single σ 1)]
    simp only [Fin.val_castLT, Fin.val_succ]
    have hc : (-1 : ℤ) ^ ((j : ℕ) + ((i : ℕ) + 1)) = -((-1 : ℤ) ^ ((i : ℕ) + (j : ℕ))) := by
      rw [show (j : ℕ) + ((i : ℕ) + 1) = ((i : ℕ) + (j : ℕ)) + 1 by omega, pow_succ]
      ring
    rw [hc, neg_smul, neg_neg]

theorem orderD_comp {α : Type u} [Preorder α] [DecidableEq α] (k : ℕ) :
    (D (α := α) k).comp (D (α := α) (k + 1)) = 0 := by
  apply chainMod_ext
  intro σ
  simp only [LinearMap.comp_apply, LinearMap.zero_apply]
  have hcomp : (D (α := α) k) ((D (α := α) (k + 1)) (Finsupp.single σ 1))
      = ∑ p : Fin (k + 2) × Fin (k + 3),
          (-1 : ℤ) ^ ((p.1 : ℕ) + (p.2 : ℕ)) • (faceLM (α := α) (k := k) p.1)
            ((faceLM (α := α) (k := k + 1) p.2) (Finsupp.single σ 1)) := by
    rw [D_single (k + 1) σ, map_sum]
    simp only [map_smul, D_single, Finset.smul_sum, smul_smul, ← pow_add]
    rw [Finset.sum_comm, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [add_comm, faceLM_single, faceLM_single]
  rw [hcomp, sum_pair_zero k σ]

end Work.Subdivision
