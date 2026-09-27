/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: hSpace_sphere_iff team

# A normalized cocycle vanishes on the "front `p`-projection" of a non-identity shuffle

For `A ⊆ {0,…,p+q-1}` with `#A = p`, let

`f_A := shuffleMapA A hA : ⦋p+q⦌ ⟶ ⦋p⦌`, `j ↦ #{i ∈ A : i < j}`

and let `⦋p⦌ ⟶ ⦋p+q⦌` be the front inclusion `subinterval 0 p` (`j ↦ j`).  The composite

`ρ_A := (subinterval 0 p) ≫ shuffleMapA A hA : ⦋p⦌ ⟶ ⦋p⦌`,  `j ↦ #{i ∈ A : i < j}`

is the "front `p`-projection" of the shuffle.  For the identity shuffle
`shuffleId p q = {0,…,p-1}` it is the identity (`frontProjA_shuffleId`); the content of this file
is that for every *other* shuffle it is **not injective**, hence the induced `p`-simplex
`X.map ρ_A.op a` of a simplicial set is *degenerate*, hence a *normalized* `p`-cochain `u`
satisfies `u (X.map ρ_A.op a) = 0`.

The two ingredients are

* the computation of `ρ_A` on vertices, `j ↦ #{i ∈ A : i < j}`, and the observation
  `#{i ∈ A : i < p} < p` for `A ≠ shuffleId p q` (a proper subset of the `p`-element set
  `shuffleId p q = {i : i < p}`, because `{i ∈ A : i < p} = A` would force `A = shuffleId`);
* the general fact that a simplex obtained from a non-injective endomorphism `f : ⦋n⦌ ⟶ ⦋n⦌`
  is degenerate: such `f` factors as `σ i ≫ θ` (`SimplexCategory.eq_σ_comp_of_not_injective`),
  and `X.σ i` lands in `X.degenerate _`.
-/
import Mathlib
import Submission.Work.Cohomology.EZShuffle
import Submission.Work.Cohomology.shuffleId_card

open CategoryTheory Simplicial Opposite

namespace Work.Cohomology

noncomputable section

/-- The front `p`-projection of a shuffle `A`, `ρ_A = (subinterval 0 p) ≫ shuffleMapA A hA`, is
given on vertices by `j ↦ #{i ∈ A : i < j}`. -/
lemma normFront_subinterval_shuffleMapA_val {p q : ℕ} (A : Finset (Fin (p + q)))
    (hA : A.card = p) (k : Fin (p + 1)) :
    ((CategoryTheory.CategoryStruct.comp (SimplexCategory.subinterval 0 p (by omega))
        (shuffleMapA A hA)).toOrderHom k).val
      = (A.filter fun i => i.val < k.val).card := by
  rw [SimplexCategory.comp_toOrderHom]
  rfl

/-- For `A ⊆ {0,…,p+q-1}` of cardinality `p`, if `A ≠ shuffleId p q` then strictly fewer than
`p` elements of `A` lie below `p`. -/
lemma normFront_card_filter_lt {p q : ℕ} (A : Finset (Fin (p + q))) (hA : A.card = p)
    (hne : A ≠ shuffleId p q) : (A.filter fun i => i.val < p).card < p := by
  by_contra h
  have hlep : p ≤ (A.filter fun i => i.val < p).card := by omega
  have hsub : A.filter (fun i => i.val < p) ⊆ A := Finset.filter_subset _ _
  have hAeq : A.filter (fun i => i.val < p) = A :=
    Finset.eq_of_subset_of_card_le hsub (by omega)
  have hAsub : A ⊆ shuffleId p q := by
    intro i hi
    have hif : i ∈ A.filter (fun i => i.val < p) := by rw [hAeq]; exact hi
    have hilt : i.val < p := (Finset.mem_filter.mp hif).2
    rw [shuffleId]
    simpa using hilt
  exact hne (Finset.eq_of_subset_of_card_le hAsub (by rw [shuffleId_card, hA]))

/-- A monotone self-map of `Fin (n+1)` whose value at the top vertex is not the top vertex is not
injective. -/
lemma normFront_not_injective_of_top_val_lt {n : ℕ} (F : Fin (n + 1) →o Fin (n + 1))
    (h : (F ⟨n, Nat.lt_succ_self n⟩).val < n) : ¬ Function.Injective F := by
  intro hinj
  obtain ⟨k, hk⟩ := (Finite.injective_iff_surjective.mp hinj) ⟨n, Nat.lt_succ_self n⟩
  have hk_le : k ≤ (⟨n, Nat.lt_succ_self n⟩ : Fin (n + 1)) := Nat.le_of_lt_succ k.isLt
  have h1 := F.monotone hk_le
  rw [hk] at h1
  have h2 : n ≤ (F ⟨n, Nat.lt_succ_self n⟩).val := h1
  omega

/-- A simplex obtained by applying a non-injective endomorphism `⦋n⦌ ⟶ ⦋n⦌` (i.e. an
`n`-simplex with a repeated vertex) is degenerate. -/
lemma normFront_mem_degenerate_of_not_injective {X : SSet.{0}} {n : ℕ} (f : ⦋n⦌ ⟶ ⦋n⦌)
    (hf : ¬ Function.Injective f.toOrderHom) (a : X _⦋n⦌) :
    X.map f.op a ∈ X.degenerate n := by
  rcases n with _ | n
  · exact absurd (fun x _ _ => Fin.ext (by have h0 : ⦋0⦌.len = 0 := rfl; omega)) hf
  · obtain ⟨i, θ, hθ⟩ := SimplexCategory.eq_σ_comp_of_not_injective f hf
    rw [hθ, op_comp, Functor.map_comp, CategoryTheory.comp_apply]
    exact SSet.σ_mem_degenerate X i (X.map θ.op a)

/-- The front `p`-projection `ρ_A` of a shuffle `A ≠ shuffleId p q` (with `#A = p`) is not an
injective map `Fin (p+1) → Fin (p+1)`. -/
lemma normFront_not_injective_comp {p q : ℕ} (A : Finset (Fin (p + q))) (hA : A.card = p)
    (hne : A ≠ shuffleId p q) :
    ¬ Function.Injective (CategoryTheory.CategoryStruct.comp
        (SimplexCategory.subinterval 0 p (by omega)) (shuffleMapA A hA)).toOrderHom := by
  rcases p with _ | p
  · have h1 : A = ∅ := Finset.card_eq_zero.mp hA
    have h2 : shuffleId 0 q = ∅ := Finset.card_eq_zero.mp (shuffleId_card 0 q)
    exact fun _ => hne (h1.trans h2.symm)
  · refine normFront_not_injective_of_top_val_lt _ ?_
    rw [normFront_subinterval_shuffleMapA_val]
    exact normFront_card_filter_lt A hA hne

/-- **A normalized cochain vanishes on the front `p`-projection of any shuffle other than the
identity shuffle.**  The composite `(subinterval 0 p) ≫ shuffleMapA A hA` is not injective, so it
produces a degenerate `p`-simplex, on which a normalized cochain `u` vanishes. -/
theorem normalized_frontProjA_eq_zero {X : SSet.{0}} {p q : ℕ}
    (u : Submission.Cohomology.Cochain X ℚ p) (hu : Work.Cohomology.IsNormalized u)
    (A : Finset (Fin (p + q))) (hA : A.card = p) (hne : A ≠ Work.Cohomology.shuffleId p q)
    (a : X.obj (Opposite.op (SimplexCategory.mk p))) :
    u (X.map (Quiver.Hom.op (CategoryTheory.CategoryStruct.comp
        (SimplexCategory.subinterval 0 p (by omega))
        (Work.Cohomology.shuffleMapA A hA))) a) = 0 := by
  refine hu _ ?_
  exact normFront_mem_degenerate_of_not_injective
    (f := CategoryTheory.CategoryStruct.comp (SimplexCategory.subinterval 0 p (by omega))
      (shuffleMapA A hA)) (normFront_not_injective_comp A hA hne) a

end

end Work.Cohomology
