import Mathlib.Algebra.Module.NatInt
import Mathlib.Data.Finsupp.Multiset
import Mathlib.Data.Multiset.Sort

namespace Commons.Algebra.BigOperators

/-- For a finitely supported `ℕ`-valued function `f`, the `Finsupp.sum` of the
`ℕ`-weighted `M`-elements `n • g i` agrees with the finite sum `∑ i, f i • g i`. -/
private lemma finsupp_sum_smul_eq_sum {ι M : Type*} [Fintype ι] [AddCommMonoid M]
    (f : ι →₀ ℕ) (g : ι → M) :
    f.sum (fun i n => n • g i) = ∑ i, f i • g i := by
  rw [Finsupp.sum_fintype f (fun i n => n • g i) (fun i => zero_smul _ _)]

/-- The sum of the images under `g` of the elements of a multiset `s` agrees with the
`ℕ`-weighted sum of the multiplicities of `s`, read as a finitely supported function. -/
private lemma multiset_sum_eq_toFinsupp_sum {ι M : Type*} [DecidableEq ι] [AddCommMonoid M]
    (s : Multiset ι) (g : ι → M) :
    (s.map g).sum = (Multiset.toFinsupp s).sum (fun i n => n • g i) := by
  rw [Finset.sum_multiset_map_count]
  rw [Finsupp.sum]
  simp [Multiset.toFinsupp_support, Multiset.toFinsupp_apply]

/-- The sorted lists of elements of a finite type `ι` with a given value of the sum of the images
under `g : ι → M` are in bijection with the functions `ι → ℕ` whose weighted sum is the same: a
sorted list is determined by its multiplicity function, i.e. by the multiset of its elements, and
either description determines the other.  (Stated as an existence of the equivalence, so that the
bijection can be used directly.)

Recommended proof: build the equivalence explicitly from
* `Multiset.sort` and the coercion `List → Multiset`: use
  `Multiset.sort_eq : ↑(s.sort r) = s` and `Multiset.pairwise_sort : (s.sort r).Pairwise r` in one
  direction, and `Multiset.coe_sort : (↑l).sort r = l.mergeSort (decide ∘ r)` together with
  `List.mergeSort_eq_self : List.Pairwise r l → l.mergeSort (fun a b => decide (r a b)) = l` in the
  other;
* `Finsupp.toMultiset : (ι →₀ ℕ) →+ Multiset ι` and `Multiset.toFinsupp : Multiset ι ≃+ (ι →₀ ℕ)`
  (`Finsupp.toMultiset_toFinsupp`, `Multiset.toFinsupp_symm_apply`, `Multiset.toFinsupp_apply`,
  `Finsupp.count_toMultiset`, `Finsupp.sum_toMultiset`, `Multiset.sum_coe`);
* `Finsupp.equivFunOnFinite : (ι →₀ ℕ) ≃ (ι → ℕ)` to replace `ι → ℕ` by `ι →₀ ℕ`
  (the condition `∑ i, k i • g i = γ` becomes `∑ i ∈ f.support, f i • g i = γ`, the same sum).
The sum condition is preserved because a list and its sorted version are permutations, hence have
the same multiset, and the sum of the images of the elements of a multiset is the sum of the
images of the elements of any of its lists. -/
theorem exists_equiv_sortedList_fun {ι : Type*} [Fintype ι] [DecidableEq ι] (r : ι → ι → Prop)
    [DecidableRel r] [IsTrans ι r] [Std.Antisymm r] [Std.Total r]
    {M : Type*} [AddCommMonoid M] (g : ι → M) (γ : M) :
    ∃ e : {w : List ι // w.Pairwise r ∧ (w.map g).sum = γ} ≃
        {k : ι → ℕ // ∑ i, k i • g i = γ}, ∀ x, e x = e x := by
  -- Sorted lists with a given image-sum are the multisets with the same image-sum.
  have eAB : {w : List ι // w.Pairwise r ∧ (w.map g).sum = γ} ≃
      {s : Multiset ι // (s.map g).sum = γ} :=
  { toFun := fun w => ⟨(w.1 : Multiset ι), by
      rw [Multiset.map_coe, Multiset.sum_coe]; exact w.2.2⟩
    invFun := fun s => ⟨s.1.sort r, s.1.pairwise_sort r, by
      rw [← Multiset.sum_coe, ← Multiset.map_coe, Multiset.sort_eq]; exact s.2⟩
    left_inv := fun w => by
      apply Subtype.ext
      simp only
      rw [Multiset.coe_sort, List.mergeSort_eq_self r w.2.1]
    right_inv := fun s => by
      apply Subtype.ext
      simp only
      rw [Multiset.sort_eq] }
  -- Multisets are the same as finitely supported `ℕ`-valued multiplicity functions.
  have eBC : {s : Multiset ι // (s.map g).sum = γ} ≃
      {f : ι →₀ ℕ // f.sum (fun i n => n • g i) = γ} :=
    Equiv.subtypeEquiv Multiset.toFinsupp.toEquiv (fun s => by
      rw [multiset_sum_eq_toFinsupp_sum s g]
      exact Iff.rfl)
  -- A finitely supported function on a finite type is an arbitrary function.
  have eCD : {f : ι →₀ ℕ // f.sum (fun i n => n • g i) = γ} ≃
      {k : ι → ℕ // ∑ i, k i • g i = γ} :=
    Equiv.subtypeEquiv Finsupp.equivFunOnFinite (fun f => by
      rw [finsupp_sum_smul_eq_sum f g]
      simp)
  exact ⟨eAB.trans (eBC.trans eCD), fun x => rfl⟩

end Commons.Algebra.BigOperators