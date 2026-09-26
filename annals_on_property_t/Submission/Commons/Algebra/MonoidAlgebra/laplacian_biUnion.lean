import Submission.Commons.Algebra.MonoidAlgebra.conj_laplacian

open scoped BigOperators

set_option autoImplicit false

namespace Commons.Algebra.MonoidAlgebra

/-- For a finite set `S` of a group `G`, the cardinality `Nat.card S` of the
underlying subtype coincides with the `Finset` cardinality `S.card`. -/
lemma nat_card_finset_coe {G : Type*} (S : Finset G) : Nat.card S = S.card := by
  rw [Nat.card_eq_fintype_card, Fintype.card_coe]

/-- **The Laplacian of a union of a pairwise disjoint family of finite sets is the
sum of the Laplacians.**  This is the algebraic content of the paper's
"Δ_n = ∑_{e ∈ E_n} Δ_e" (Kaluba–Kielak–Nowak, Lemma `delta using edges`): the
generating set of `G_n` is partitioned by the fibres of the edge label `l_n`,
and both the cardinality and the sum over the generating set split accordingly.
Hint: `Finset.card_biUnion` and `Finset.sum_biUnion`. -/
theorem laplacian_biUnion {G ι : Type*} [Group G] [DecidableEq G] [DecidableEq ι]
    (E : Finset ι) (Se : ι → Finset G)
    (hdisj : ∀ e ∈ E, ∀ f ∈ E, e ≠ f → Disjoint (Se e) (Se f)) :
    Commons.Algebra.MonoidAlgebra.Laplacian (E.biUnion Se)
      = ∑ e ∈ E, Commons.Algebra.MonoidAlgebra.Laplacian (Se e) := by
  have hdisj' : (↑E : Set ι).PairwiseDisjoint Se := hdisj
  have hnat : Nat.card (E.biUnion Se) = ∑ e ∈ E, Nat.card (Se e) := by
    simp only [nat_card_finset_coe]
    exact Finset.card_biUnion hdisj'
  have hcard : ((Nat.card (E.biUnion Se) : ℕ) : MonoidAlgebra ℝ G)
      = ∑ e ∈ E, ((Nat.card (Se e) : ℕ) : MonoidAlgebra ℝ G) := by
    rw [← Nat.cast_sum]
    exact congrArg (fun n : ℕ => (n : MonoidAlgebra ℝ G)) hnat
  have hsum : (∑ s ∈ E.biUnion Se, MonoidAlgebra.of ℝ G s)
      = ∑ e ∈ E, ∑ s ∈ Se e, MonoidAlgebra.of ℝ G s :=
    Finset.sum_biUnion (f := fun s => MonoidAlgebra.of ℝ G s) hdisj'
  unfold Laplacian
  rw [Finset.sum_sub_distrib, hcard, hsum]

end Commons.Algebra.MonoidAlgebra
