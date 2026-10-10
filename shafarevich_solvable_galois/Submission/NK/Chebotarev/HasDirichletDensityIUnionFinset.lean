import Mathlib.Order.CompletePartialOrder
import Mathlib.NumberTheory.NumberField.DirichletDensity
import Submission.NK.Chebotarev.Density
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace NK.Chebotarev

/-- **Dirichlet density is additive over a finite disjoint family of sets of primes.**

If `s` is a finite index set, `f i` has Dirichlet density `δ i` for each `i ∈ s`, and the
sets `f i` are pairwise disjoint, then `⋃ i ∈ s, f i` has Dirichlet density `∑ i ∈ s, δ i`.
This is the `Finset`-indexed form of
`Commons.NumberTheory.NumberField.Set.hasDirichletDensity_union_of_disjoint`, obtained by
induction on `s`. -/
theorem HasDirichletDensityIUnionFinset {K : Type*} [Field K] [NumberField K] {ι : Type*}
    (s : Finset ι) (f : ι → Set (NK.Chebotarev.PrimeIdeal K)) (δ : ι → ℝ)
    (h : ∀ i ∈ s, NumberField.Set.HasDirichletDensity (f i) (δ i))
    (hdisj : (s : Set ι).Pairwise fun i j => Disjoint (f i) (f j)) :
    NumberField.Set.HasDirichletDensity (⋃ i ∈ s, f i) (∑ i ∈ s, δ i) := by
  classical
  have key : ∀ s : Finset ι,
      (∀ i ∈ s, NumberField.Set.HasDirichletDensity (f i) (δ i)) →
      (s : Set ι).Pairwise (fun i j => Disjoint (f i) (f j)) →
      NumberField.Set.HasDirichletDensity (⋃ i ∈ s, f i) (∑ i ∈ s, δ i) := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
        intro _ _
        have h1 : (⋃ i ∈ (∅ : Finset ι), f i) = (∅ : Set (NK.Chebotarev.PrimeIdeal K)) := by
          ext x; simp
        have h2 : (∑ i ∈ (∅ : Finset ι), δ i) = 0 := Finset.sum_empty
        rw [h1, h2]
        exact Commons.NumberTheory.NumberField.Set.hasDirichletDensity_zero_of_finite
          Set.finite_empty
    | insert a s ha ih =>
        intro h hdisj
        have hunion : (⋃ i ∈ (insert a s : Finset ι), f i) = f a ∪ ⋃ i ∈ s, f i := by
          ext x
          simp only [Set.mem_iUnion, Finset.mem_insert, exists_prop, Set.mem_union]
          constructor
          · rintro ⟨i, (rfl | hi), hx⟩
            · exact Or.inl hx
            · exact Or.inr ⟨i, hi, hx⟩
          · rintro (hx | ⟨i, hi, hx⟩)
            · exact ⟨a, Or.inl rfl, hx⟩
            · exact ⟨i, Or.inr hi, hx⟩
        rw [hunion, Finset.sum_insert ha]
        refine Commons.NumberTheory.NumberField.Set.hasDirichletDensity_union_of_disjoint ?_ ?_ ?_
        · refine (Set.disjoint_iUnion_right).mpr fun i =>
            (Set.disjoint_iUnion_right).mpr fun hi => ?_
          exact hdisj (Finset.mem_insert_self a s) (Finset.mem_insert_of_mem hi)
            (by rintro rfl; exact ha hi)
        · exact h a (Finset.mem_insert_self a s)
        · exact ih (fun i hi => h i (Finset.mem_insert_of_mem hi))
            (fun i hi j hj hij =>
              hdisj (Finset.mem_insert_of_mem hi) (Finset.mem_insert_of_mem hj) hij)
  exact key s h hdisj

end NK.Chebotarev
