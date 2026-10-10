import Mathlib

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.MotK.JunkLinAux

/-- A polynomial over a field with total degree exactly `1` has a nonzero coefficient at some
single variable `X i`, i.e. `f.coeff (Finsupp.single i 1) ≠ 0` for some `i`.

Route: `MvPolynomial.totalDegree_eq` writes `f.totalDegree = f.support.sup (fun m =>
(Finsupp.toMultiset m).card)`.  The value is `1 ≠ 0 = ⊥`, so `f.support` is nonempty and
`Finset.exists_mem_eq_sup` produces `m ∈ f.support` with `(Finsupp.toMultiset m).card = 1`.
`Finsupp.card_toMultiset` turns this into `m.sum (fun _ e => e) = 1`, and `Finsupp.sum_eq_one_iff`
gives `m = Finsupp.single i 1` for some `i`; finish with `MvPolynomial.mem_support_iff`. -/
lemma exists_coeff_single_of_totalDegree_eq_one {K : Type} [Field K] {n : ℕ}
    (f : MvPolynomial (Fin (n + 1)) K) (hf : f.totalDegree = 1) :
    ∃ i : Fin (n + 1), f.coeff (Finsupp.single i 1) ≠ 0 := by
  -- `totalDegree` is the supremum over the support of the degree of each monomial.
  have hsup : f.support.sup (fun m => (Finsupp.toMultiset m).card) = 1 := by
    rw [← MvPolynomial.totalDegree_eq]; exact hf
  -- the value `1` is not `⊥ = 0`, so the support is nonempty and the supremum is attained
  have hne : f.support.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro h
    rw [h, Finset.sup_empty] at hsup
    exact one_ne_zero hsup.symm
  obtain ⟨m, hm, hmsup⟩ :=
    Finset.exists_mem_eq_sup f.support hne (fun m => (Finsupp.toMultiset m).card)
  have hcard : (Finsupp.toMultiset m).card = 1 := by rw [← hmsup, hsup]
  -- a multiset of cardinality one forces the monomial to be a single variable
  obtain ⟨i, hi⟩ := (Finsupp.sum_eq_one_iff m).mp (by
    rw [Finsupp.card_toMultiset m] at hcard
    exact hcard)
  refine ⟨i, ?_⟩
  have hm' : f.coeff m ≠ 0 := MvPolynomial.mem_support_iff.mp hm
  rwa [hi] at hm'

end Work.MotK.JunkLinAux
