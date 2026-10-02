/-
# The upper tail of the unretained occupancy count

For the uniform random colouring `f : V → Fin k` (`colSpace`, see
`Submission/Work/Deep/Sparse/ProbBasic.lean`) and a finite vertex set `A`,
`occRaw A f j` (see `Submission/Work/Deep/Sparse/SliceDefs.lean`) is the number of colours
occurring at least `j` times among the vertices of `A`.

The target of this file, `occRaw_tail`, bounds the upper tail of `occRaw A · j`: the
probability that at least `K` colours occur `j` times each on `A` is at most

  `(k * ((|A| / k)^j / j!))^K / K!`.

The proof is a union bound over the `K`-subsets of colours together with a union bound over
the choices of the `j` witnesses of each of these colours:

* if `occRaw A f j ≥ K`, then there is a set `S` of `K` colours each occurring `j` times on
  `A`, so the event `{f | K ≤ occRaw A f j}` is contained in the union, over all
  `K`-element sets `S` of colours, of the events `{f | ∀ c ∈ S, j ≤ occ(f,c)}`
  (`Finset.exists_subset_card_eq`), and the union bound
  `FinSpace.prob_biUnion_le_sum` gives
  `P[K ≤ occRaw A · j] ≤ ∑_{|S| = K} P[∀ c ∈ S, j ≤ occ(f,c)]`;
* each summand is at most `(choose |A| j)^K / k^(jK)`: for a fixed `j`-subset `T_c ⊆ A` per
  colour `c ∈ S` the event "all of `T_c` has colour `c`, for every `c ∈ S`" has probability
  `k^(-jK)` by the product law (`colSpace_prob_pi`), and there are at most `(choose |A| j)^K`
  families `(T_c)`; this is `colSpace_prob_all_occ_le` in
  `Submission/Work/Deep/Sparse/colSpace_prob_all_occ_le.lean`;
* `choose k K ≤ k^K / K!` and `choose |A| j ≤ |A|^j / j!` turn the resulting
  `(choose k K) * (choose |A| j)^K / k^(jK)` into the target
  `(k ((|A|/k)^j / j!))^K / K!`; this is `choose_mul_pow_div_le` in
  `Submission/Work/Deep/Sparse/choose_mul_pow_div_le.lean`.

The degenerate case `|A| < j` is immediate: then no colour occurs `j` times on `A` at all,
so the event is empty (recall `K ≥ 1`) and the bound is nonnegative.
-/
import Submission.Work.Deep.Sparse.Prelude
import Submission.Work.Deep.Sparse.ProbBasic
import Submission.Work.Deep.Sparse.SliceDefs
import Submission.Work.Deep.Sparse.colSpace_prob_all_occ_le
import Submission.Work.Deep.Sparse.choose_mul_pow_div_le

set_option autoImplicit false

open scoped BigOperators

namespace Work.Deep.Sparse

namespace FinSpace

/-- **Union bound** for the finite probability space `FinSpace`: the probability of a finite
union of events is at most the sum of the probabilities. -/
theorem prob_biUnion_le_sum {Ω : Type*} [Fintype Ω] (P : FinSpace Ω) {ι : Type*}
    (s : Finset ι) (A : ι → Set Ω) :
    P.prob (⋃ i ∈ s, A i) ≤ ∑ i ∈ s, P.prob (A i) := by
  classical
  calc P.prob (⋃ i ∈ s, A i) = ∑ ω, (⋃ i ∈ s, A i).indicator P.mass ω := rfl
    _ ≤ ∑ ω, ∑ i ∈ s, (A i).indicator P.mass ω := by
        refine Finset.sum_le_sum (fun ω _ => ?_)
        by_cases h : ω ∈ ⋃ i ∈ s, A i
        · rw [Set.indicator_of_mem h]
          obtain ⟨i, hi⟩ := Set.mem_iUnion.mp h
          obtain ⟨his, hAi⟩ := Set.mem_iUnion.mp hi
          have hsum : (A i).indicator P.mass ω ≤ ∑ x ∈ s, (A x).indicator P.mass ω :=
            Finset.single_le_sum (f := fun j => (A j).indicator P.mass ω) (fun j _ => by
              by_cases hj : ω ∈ A j
              · rw [Set.indicator_of_mem hj]; exact P.mass_nonneg ω
              · rw [Set.indicator_of_notMem hj]) his
          rwa [Set.indicator_of_mem hAi] at hsum
        · rw [Set.indicator_of_notMem h]
          exact Finset.sum_nonneg (fun i _ => FinSpace.ind_nonneg P (A i) ω)
    _ = ∑ i ∈ s, ∑ ω, (A i).indicator P.mass ω := Finset.sum_comm
    _ = ∑ i ∈ s, P.prob (A i) := rfl

end FinSpace

/-- **Upper tail of the unretained occupancy count.**  Under the uniform random colouring of
`V` by `k` colours, the probability that at least `K` colours occur at least `j` times each
among the vertices of `A` is at most `(k * ((|A|/k)^j / j!))^K / K!`. -/
theorem occRaw_tail {V : Type*} [Fintype V] [DecidableEq V] {k : ℕ} [Nonempty (V → Fin k)] (A : Finset V) {j K : ℕ}
    (hj : 0 < j) (hK : 0 < K) :
    (colSpace (V := V) k).prob {f : V → Fin k | K ≤ occRaw A f j}
      ≤ ((k : ℝ) * (((A.card : ℝ) / (k : ℝ)) ^ j / (j.factorial : ℝ))) ^ K / (K.factorial : ℝ) := by
  classical
  by_cases hja : j ≤ A.card
  · -- in this case `A` is nonempty, hence `k ≥ 1`
    have hk : 0 < k := by
      obtain ⟨v, _⟩ := Finset.card_pos.mp (lt_of_lt_of_le hj hja)
      have h := (Classical.arbitrary (V → Fin k) v).isLt
      omega
    -- the `K`-element sets of colours
    set colSets : Finset (Finset (Fin k)) := (Finset.univ : Finset (Fin k)).powersetCard K with hP
    -- the event `{K ≤ occRaw A · j}` is contained in the union of the events `{∀ c ∈ S, ...}`
    have hsub : {f : V → Fin k | K ≤ occRaw A f j} ⊆
        ⋃ S ∈ colSets, {f : V → Fin k | ∀ c ∈ S, j ≤ (A.filter (fun x => f x = c)).card} := by
      intro f hf
      simp only [Set.mem_ofPred_eq] at hf ⊢
      obtain ⟨S, hSsub, hScard⟩ := Finset.exists_subset_card_eq hf
      refine Set.mem_iUnion.mpr ⟨S, Set.mem_iUnion.mpr ⟨?_, ?_⟩⟩
      · rw [hP, Finset.mem_powersetCard]
        exact ⟨Finset.subset_univ S, hScard⟩
      · intro c hc
        exact (Finset.mem_filter.mp (hSsub hc)).2
    calc (colSpace (V := V) k).prob {f : V → Fin k | K ≤ occRaw A f j}
        ≤ (colSpace (V := V) k).prob
            (⋃ S ∈ colSets, {f : V → Fin k | ∀ c ∈ S, j ≤ (A.filter (fun x => f x = c)).card}) :=
          FinSpace.prob_mono _ hsub
      _ ≤ ∑ S ∈ colSets, (colSpace (V := V) k).prob
            {f : V → Fin k | ∀ c ∈ S, j ≤ (A.filter (fun x => f x = c)).card} :=
          FinSpace.prob_biUnion_le_sum _ _ _
      _ ≤ ∑ S ∈ colSets, (((A.powersetCard j).card : ℝ) ^ K / (k : ℝ) ^ (j * K)) := by
          refine Finset.sum_le_sum (fun S hS => ?_)
          have hScard : S.card = K := (Finset.mem_powersetCard.mp (by rw [← hP]; exact hS)).2
          have h := colSpace_prob_all_occ_le hk A hj S
          rw [hScard] at h
          exact h
      _ = (colSets.card : ℝ) * (((A.powersetCard j).card : ℝ) ^ K / (k : ℝ) ^ (j * K)) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ = (k.choose K : ℝ) * (((A.card.choose j : ℝ)) ^ K / (k : ℝ) ^ (j * K)) := by
          rw [hP, Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin,
            Finset.card_powersetCard]
      _ ≤ ((k : ℝ) * (((A.card : ℝ) / (k : ℝ)) ^ j / (j.factorial : ℝ))) ^ K /
            (K.factorial : ℝ) := choose_mul_pow_div_le hk hK
  · -- `|A| < j`: no colour occurs `j` times on `A`, so the event is empty
    have hzero : {f : V → Fin k | K ≤ occRaw A f j} = ∅ := by
      ext f
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
      intro hKle
      have hocc : occRaw A f j = 0 := by
        unfold occRaw
        rw [Finset.card_eq_zero]
        ext c
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false,
          not_le]
        exact lt_of_le_of_lt (Finset.card_filter_le _ _) (not_le.mp hja)
      rw [hocc] at hKle
      omega
    rw [hzero]
    have : (colSpace (V := V) k).prob (∅ : Set (V → Fin k)) = 0 := by
      rw [FinSpace.prob, Set.indicator_empty, Finset.sum_const_zero]
    rw [this]
    positivity

end Work.Deep.Sparse
