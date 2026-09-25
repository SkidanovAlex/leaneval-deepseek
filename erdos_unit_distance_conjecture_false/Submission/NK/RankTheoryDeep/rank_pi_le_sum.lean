import Mathlib
import Submission.NK.RankTheoryDeep.IdeleRankDefs

/-!
# The rank of a finite product is at most the sum of the ranks

Over a commutative domain `R`, the `R`-rank of a product of finitely many `R`-modules is bounded by
the sum of the ranks:

`Module.rank R ((i : {i // i ∈ s}) → M i) ≤ ∑ i ∈ s, Module.rank R (M i)`.

This is the generalisation of `Module.rank_pi` (which computes the rank of a finite product of
*free* modules) to arbitrary modules.  The proof is the rank-nullity theorem
(`LinearMap.rank_eq_of_surjective`, available since a commutative domain satisfies
`HasRankNullity`), applied by induction on the finset:

* for `s = insert a t`, the projection `π` onto the `a`-coordinate of the product over
  `{i // i ∈ insert a t}` is surjective, so
  `rank P = rank (M a) + rank (ker π)`;
* the restriction of a family in `ker π` to the coordinates of `t` is an *injective* linear map
  `ker π →ₗ (i : {i // i ∈ t}) → M i`, so `rank (ker π) ≤ rank (∏_{i ∈ t} M i)`, to which the
  induction hypothesis applies.

The interesting point is that no freeness hypothesis on the `M i` is needed: the rank of a finite
product is the sum of the ranks, even though the rank of a single module need not be attained by a
free submodule.
-/

universe v u

namespace NK.RankTheoryDeep

open Cardinal Module

/-- **The rank of a finite product of modules over a domain is at most the sum of the ranks.** -/
theorem rank_pi_le_sum {R : Type v} [CommRing R] [IsDomain R] {ι : Type u} (s : Finset ι)
    (M : ι → Type u) [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)] :
    Module.rank R ((i : {i // i ∈ s}) → M i) ≤ ∑ i ∈ s, Module.rank R (M i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      -- the empty product is the zero module, and it is the empty sum on the right
      have hsub : Subsingleton ((i : {i // i ∈ (∅ : Finset ι)}) → M i) :=
        ⟨fun f g => funext fun i => (Finset.notMem_empty i.1 i.2).elim⟩
      have h0 : Module.rank R ((i : {i // i ∈ (∅ : Finset ι)}) → M i) = 0 := by
        rw [rank_eq_zero_iff]
        exact fun x => ⟨1, one_ne_zero, by rw [one_smul]; exact hsub.elim x 0⟩
      rw [Finset.sum_empty]
      exact h0.le
  | insert a t ha ih =>
      rw [Finset.sum_insert ha]
      -- the projection onto the `a`-coordinate
      let π : ((i : {i // i ∈ insert a t}) → M i) →ₗ[R] M a :=
        { toFun := fun v => v ⟨a, Finset.mem_insert_self a t⟩
          map_add' := fun v w => rfl
          map_smul' := fun c v => rfl }
      have hsurj : Function.Surjective π := by
        intro x
        refine ⟨Function.update (0 : (i : {i // i ∈ insert a t}) → M i)
            ⟨a, Finset.mem_insert_self a t⟩ x, ?_⟩
        show (Function.update (0 : (i : {i // i ∈ insert a t}) → M i)
            ⟨a, Finset.mem_insert_self a t⟩ x) ⟨a, Finset.mem_insert_self a t⟩ = x
        rw [Function.update_self]
      have hrank := LinearMap.rank_eq_of_surjective (f := π) hsurj
      rw [hrank]
      -- restriction of a family in the kernel to the coordinates of `t` is injective
      have hker : Module.rank R (LinearMap.ker π) ≤
          Module.rank R ((i : {i // i ∈ t}) → M i) := by
        let g : (LinearMap.ker π) →ₗ[R] ((i : {i // i ∈ t}) → M i) :=
          { toFun := fun v i => v.1 ⟨i.1, Finset.mem_insert_of_mem i.2⟩
            map_add' := fun v w => by funext i; rfl
            map_smul' := fun c v => by funext i; rfl }
        refine LinearMap.rank_le_of_injective g ?_
        intro v w hvw
        apply Subtype.ext
        funext i
        rcases Finset.mem_insert.mp i.2 with hi | hi
        · -- the `a`-coordinate: both families lie in the kernel
          rw [show i = (⟨a, Finset.mem_insert_self a t⟩ : {i // i ∈ insert a t})
              from Subtype.ext hi]
          exact v.2.trans w.2.symm
        · -- a coordinate in `t`: use the injectivity hypothesis
          exact congrFun hvw ⟨i.1, hi⟩
      exact add_le_add le_rfl (hker.trans ih)

end NK.RankTheoryDeep
