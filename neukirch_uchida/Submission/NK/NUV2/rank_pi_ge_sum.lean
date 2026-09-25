import Mathlib

/-!
# The rank of a finite product is at least the sum of the ranks

Over a semiring `R` with `Nontrivial R`, the `R`-rank of a finite product of `R`-modules is at
least the sum of the ranks:

`∑ i ∈ s, Module.rank R (M i) ≤ Module.rank R ((i : {i // i ∈ s}) → M i)`.

This is the companion of `NK.RankTheoryDeep.rank_pi_le_sum` (the reverse inequality, which needs
`IsDomain R` and the rank–nullity theorem).  Here the two ingredients are

* the binary case `rank_add_rank_le_rank_prod` (`rank M + rank M' ≤ rank (M × M')`), which is
  Mathlib's `Module.rank_add_rank_le_rank_prod`, and
* the splitting of a product over `insert a t` into the `a`-coordinate times the product over `t`,

`∏_{i ∈ insert a t} M i ≃ₗ M a × ∏_{i ∈ t} M i`, an elementary linear equivalence (no freeness, no
domain hypothesis).

The finite product of *arbitrary* modules therefore has rank exactly the sum of the ranks, so the
`IsDomain` hypothesis of `rank_pi_le_sum` is only needed for the other direction.
-/

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace NK.NUV2

universe u

/-- **The rank of a finite product is at least the sum of the ranks.** -/
theorem sum_rank_le_rank_pi {R : Type u} [Semiring R] [Nontrivial R] {ι : Type u} (s : Finset ι)
    (M : ι → Type u) [∀ i, AddCommMonoid (M i)] [∀ i, Module R (M i)] :
    ∑ i ∈ s, Module.rank R (M i) ≤ Module.rank R ((i : {i // i ∈ s}) → M i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a t ha ih =>
      rw [Finset.sum_insert ha]
      have e : ((i : {i // i ∈ insert a t}) → M i.1) ≃ₗ[R]
          (M a × ((i : {i // i ∈ t}) → M i.1)) := by
        let σ : Option {i // i ∈ t} ≃ {i // i ∈ insert a t} :=
          { toFun := fun o => match o with
              | none => ⟨a, Finset.mem_insert_self a t⟩
              | some j => ⟨j.1, Finset.mem_insert_of_mem j.2⟩
            invFun := fun i => if h : (i : ι) = a then none
              else some ⟨i.1, (Finset.mem_insert.mp i.2).resolve_left h⟩
            left_inv := by
              intro o
              cases o with
              | none => dsimp only; rw [dif_pos rfl]
              | some j =>
                dsimp only
                rw [dif_neg (by intro hc; exact ha (hc ▸ j.2))]
            right_inv := by
              intro i
              dsimp only
              by_cases h : (i : ι) = a
              · rw [dif_pos h]
                exact Subtype.ext h.symm
              · rw [dif_neg h] }
        let φ : {i // i ∈ insert a t} → Type u := fun i => M i.1
        let e1 : ((o : Option {i // i ∈ t}) → φ (σ o)) ≃ₗ[R]
            ((i : {i // i ∈ insert a t}) → φ i) :=
          LinearEquiv.piCongrLeft R φ σ
        let e2 : ((o : Option {i // i ∈ t}) → φ (σ o)) ≃ₗ[R]
            (φ (σ none) × ((j : {i // i ∈ t}) → φ (σ (some j)))) :=
          LinearEquiv.piOptionEquivProd R
        exact e1.symm.trans e2
      rw [LinearEquiv.rank_eq e]
      calc Module.rank R (M a) + ∑ i ∈ t, Module.rank R (M i)
          ≤ Module.rank R (M a) + Module.rank R ((i : {i // i ∈ t}) → M i.1) :=
            add_le_add le_rfl ih
        _ ≤ Module.rank R (M a × ((i : {i // i ∈ t}) → M i.1)) :=
            rank_add_rank_le_rank_prod R (M a)

end NK.NUV2
