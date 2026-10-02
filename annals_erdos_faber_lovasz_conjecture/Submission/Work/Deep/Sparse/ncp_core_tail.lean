/-
# The slice occupancy of the naive colouring: first and K-th moment bounds

`ncpN G f v j` is the number of colours carried by at least `j` *retained* neighbours of `v`.
Retained vertices of a common colour form an independent set (two adjacent same-coloured
vertices cannot both retain their colour), so a colour occurring on `j` retained neighbours of
`v` witnesses an independent `j`-subset of `N(v)`.  Combining the union bound
`colCount_prob_all_le` over such witnesses with the counting bound `indepSets_card_mul` gives

* `ncpN_tail` — `Pr[K ≤ ncpN G · v j] ≤ μ_j^K / K!`, and
* `ncpN_expect_le` — `𝔼[ncpN G · v j] ≤ μ_j`,

with the envelope `μ_j = (|nonAdjPairs G v|/2)/k · 2^j/j!` of `ncpTailDefs`.
-/
import Submission.Work.Deep.Sparse.Prelude
import Submission.Work.Deep.Sparse.ncpTailDefs
import Submission.Work.Deep.Sparse.colCount_prob_all_le
import Submission.Work.Deep.Sparse.indepSets_card_mul
import Submission.Work.Deep.Sparse.occRaw_tail

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 2000000

open scoped BigOperators

namespace Work.Deep.Sparse

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Permutation of four factors. -/
private lemma mul23 (a b c d : ℝ) : a * b * c * d = a * b * (d * c) := by ring

/-- `j! = (j-2)! · j (j-1)` for `j ≥ 2`. -/
private lemma factorial_eq (j : ℕ) (hj : 2 ≤ j) :
    (j.factorial : ℝ) = ((j - 2).factorial : ℝ) * ((j : ℝ) * ((j : ℝ) - 1)) := by
  have h2 : j.descFactorial 2 = (j - 1) * j := by
    have := Nat.descFactorial_succ j 1
    rw [Nat.descFactorial_one] at this
    exact this
  have h := Nat.factorial_mul_descFactorial (n := j) (k := 2) (by omega)
  rw [h2] at h
  have hnat : j.factorial = (j - 2).factorial * ((j - 1) * j) := h.symm
  rw [hnat]
  push_cast [Nat.cast_sub (by omega : 1 ≤ j)]
  ring

/-- The envelope `μ_j`, written without the division by `k` and `j!`: for `1 ≤ j`,
`μ_j = (|nonAdjPairs|/2) · 2^j / (k · j!) = |nonAdjPairs| · 2^(j-1) / (k · j!)`. -/
private lemma ncpMuT_eq (G : SimpleGraph V) [DecidableRel G.Adj] (k : ℕ) (v : V) {j : ℕ}
    (hj : 1 ≤ j) :
    ncpMuT G k v j
      = ((nonAdjPairs G v).card : ℝ) * (2 : ℝ) ^ (j - 1)
        / ((k : ℝ) * (j.factorial : ℝ)) := by
  rw [ncpMuT]
  have h2 : (2 : ℝ) ^ j = 2 ^ (j - 1) * 2 := by
    rw [← pow_succ]
    congr 1
    omega
  rw [h2]
  field_simp

/-- The counting bound in the ratio form used by the moment estimates. -/
private lemma indepSets_ratio_le (G : SimpleGraph V) [DecidableRel G.Adj] {k D : ℕ} (hk : 0 < k)
    (hDk : D ≤ 2 * k) (hdeg : ∀ x : V, G.degree x ≤ D) (v : V) {j : ℕ} (hj : 2 ≤ j) :
    ((indepSets G (G.neighborFinset v) j).card : ℝ) / (k : ℝ) ^ (j - 1) ≤ ncpMuT G k v j := by
  classical
  have hkR : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  have hd2k : ((G.neighborFinset v).card : ℝ) ≤ 2 * (k : ℝ) := by
    have h1 : ((G.neighborFinset v).card : ℝ) ≤ (D : ℝ) := by
      rw [SimpleGraph.card_neighborFinset_eq_degree]
      exact_mod_cast hdeg v
    have h2 : (D : ℝ) ≤ 2 * (k : ℝ) := by exact_mod_cast hDk
    linarith
  -- the counting bound in product form
  have hcount : ((indepSets G (G.neighborFinset v) j).card : ℝ) * (j.factorial : ℝ)
      ≤ ((nonAdjPairs G v).card : ℝ) * (2 : ℝ) ^ (j - 1) * (k : ℝ) ^ (j - 2) := by
    have h1 := indepSets_card_mul G v hj
    have h2 : (((G.neighborFinset v).card - 2).choose (j - 2) : ℝ)
        ≤ ((G.neighborFinset v).card : ℝ) ^ (j - 2) / ((j - 2).factorial : ℝ) := by
      refine le_trans (Nat.choose_le_pow_div (j - 2) ((G.neighborFinset v).card - 2)) ?_
      refine div_le_div_of_nonneg_right ?_ (by positivity)
      exact pow_le_pow_left₀ (by positivity)
        (by exact_mod_cast (Nat.sub_le (G.neighborFinset v).card 2 :
          (G.neighborFinset v).card - 2 ≤ (G.neighborFinset v).card)) (j - 2)
    have hfac : (0 : ℝ) < ((j - 2).factorial : ℝ) := by positivity
    have hmul : ((indepSets G (G.neighborFinset v) j).card : ℝ) * (j.factorial : ℝ)
        ≤ ((nonAdjPairs G v).card : ℝ) * ((G.neighborFinset v).card : ℝ) ^ (j - 2) := by
      have hle : (((indepSets G (G.neighborFinset v) j).card : ℝ)
            * ((j : ℝ) * ((j : ℝ) - 1))) * ((j - 2).factorial : ℝ)
          ≤ ((nonAdjPairs G v).card : ℝ) * ((G.neighborFinset v).card : ℝ) ^ (j - 2) := by
        calc (((indepSets G (G.neighborFinset v) j).card : ℝ)
              * ((j : ℝ) * ((j : ℝ) - 1))) * ((j - 2).factorial : ℝ)
            ≤ (((nonAdjPairs G v).card : ℝ)
                * (((G.neighborFinset v).card - 2).choose (j - 2) : ℝ))
              * ((j - 2).factorial : ℝ) := mul_le_mul_of_nonneg_right h1 hfac.le
          _ ≤ (((nonAdjPairs G v).card : ℝ)
                * (((G.neighborFinset v).card : ℝ) ^ (j - 2)
                  / ((j - 2).factorial : ℝ))) * ((j - 2).factorial : ℝ) :=
              mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h2 (by positivity)) hfac.le
          _ = ((nonAdjPairs G v).card : ℝ) * ((G.neighborFinset v).card : ℝ) ^ (j - 2) := by
              field_simp
      rw [factorial_eq j hj]
      nlinarith [hle]
    calc ((indepSets G (G.neighborFinset v) j).card : ℝ) * (j.factorial : ℝ)
        ≤ ((nonAdjPairs G v).card : ℝ) * ((G.neighborFinset v).card : ℝ) ^ (j - 2) := hmul
      _ ≤ ((nonAdjPairs G v).card : ℝ)
            * ((2 : ℝ) ^ (j - 1) * (k : ℝ) ^ (j - 2)) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          calc ((G.neighborFinset v).card : ℝ) ^ (j - 2) ≤ (2 * (k : ℝ)) ^ (j - 2) :=
                pow_le_pow_left₀ (by positivity) hd2k (j - 2)
            _ = (2 : ℝ) ^ (j - 2) * (k : ℝ) ^ (j - 2) := mul_pow 2 _ _
            _ ≤ (2 : ℝ) ^ (j - 1) * (k : ℝ) ^ (j - 2) :=
                mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) (by omega))
                  (by positivity)
      _ = ((nonAdjPairs G v).card : ℝ) * (2 : ℝ) ^ (j - 1) * (k : ℝ) ^ (j - 2) := by
          rw [mul_assoc]
  rw [div_le_iff₀ (pow_pos hkR (j - 1)), ncpMuT_eq G k v (by omega : 1 ≤ j)]
  rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity : (0 : ℝ) < (k : ℝ) * (j.factorial : ℝ))]
  have hkpow : (k : ℝ) ^ (j - 1) = (k : ℝ) * (k : ℝ) ^ (j - 2) := by
    conv_lhs => rw [show j - 1 = j - 2 + 1 by omega]
    rw [pow_succ']
  rw [hkpow]
  have hgoal : ((indepSets G (G.neighborFinset v) j).card : ℝ) * ((k : ℝ) * (j.factorial : ℝ))
      ≤ ((nonAdjPairs G v).card : ℝ) * (2 : ℝ) ^ (j - 1) * ((k : ℝ) * (k : ℝ) ^ (j - 2)) := by
    calc ((indepSets G (G.neighborFinset v) j).card : ℝ) * ((k : ℝ) * (j.factorial : ℝ))
        = (((indepSets G (G.neighborFinset v) j).card : ℝ) * (j.factorial : ℝ)) * (k : ℝ) := by
          ring
      _ ≤ (((nonAdjPairs G v).card : ℝ) * (2 : ℝ) ^ (j - 1) * (k : ℝ) ^ (j - 2)) * (k : ℝ) :=
          mul_le_mul_of_nonneg_right hcount hkR.le
      _ = ((nonAdjPairs G v).card : ℝ) * (2 : ℝ) ^ (j - 1) * ((k : ℝ) * (k : ℝ) ^ (j - 2)) :=
          mul23 _ _ _ _
  linarith [hgoal]

/-- **First moment.** The expected number of colours occurring on at least `j` retained
neighbours of `v` is at most `μ_j`. -/
theorem ncpN_expect_le (G : SimpleGraph V) [DecidableRel G.Adj]
    {k D : ℕ} (hk : 0 < k) (hDk : D ≤ 2 * k) [Nonempty (V → Fin k)]
    (hdeg : ∀ x : V, G.degree x ≤ D) (v : V) {j : ℕ} (hj : 2 ≤ j) :
    (colSpace (V := V) k).expect (fun f => (ncpN G f v j : ℝ)) ≤ ncpMuT G k v j := by
  classical
  have hkR : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  have hratio := indepSets_ratio_le (G := G) hk hDk hdeg v hj
  have hkey : (colSpace (V := V) k).expect (fun f => (ncpN G f v j : ℝ))
      = ∑ c : Fin k, ∑ f : V → Fin k,
          (colSpace (V := V) k).mass f *
            (if j ≤ colourClassCount G f v c then (1 : ℝ) else 0) := by
    simp only [FinSpace.expect, ncpN, Finset.card_filter, Nat.cast_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun f _ => ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun c _ => ?_)
    by_cases hc : j ≤ colourClassCount G f v c
    · rw [if_pos hc, if_pos hc]; norm_num
    · rw [if_neg hc, if_neg hc]; norm_num
  rw [hkey]
  calc ∑ c : Fin k, ∑ f : V → Fin k,
        (colSpace (V := V) k).mass f *
          (if j ≤ colourClassCount G f v c then (1 : ℝ) else 0)
      ≤ ∑ _c : Fin k, ((indepSets G (G.neighborFinset v) j).card : ℝ) / (k : ℝ) ^ j := by
        refine Finset.sum_le_sum (fun c _ => ?_)
        have h := colCount_prob_all_le (G := G) hk (v := v) (j := j) (by omega)
          ({c} : Finset (Fin k))
        have h' : (colSpace (V := V) k).prob {f : V → Fin k | j ≤ colourClassCount G f v c}
            ≤ ((indepSets G (G.neighborFinset v) j).card : ℝ) / (k : ℝ) ^ j := by
          simpa using h
        have heq : (∑ f : V → Fin k, (colSpace (V := V) k).mass f *
              (if j ≤ colourClassCount G f v c then (1 : ℝ) else 0))
            = (colSpace (V := V) k).prob {f : V → Fin k | j ≤ colourClassCount G f v c} := by
          simp only [FinSpace.prob, Set.indicator, Set.mem_ofPred_eq]
          refine Finset.sum_congr rfl (fun f _ => ?_)
          by_cases hc : j ≤ colourClassCount G f v c
          · rw [if_pos hc, if_pos hc, mul_one]
          · rw [if_neg hc, if_neg hc, mul_zero]
        rw [heq]; exact h'
    _ = (k : ℝ) * (((indepSets G (G.neighborFinset v) j).card : ℝ) / (k : ℝ) ^ j) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    _ = ((indepSets G (G.neighborFinset v) j).card : ℝ) / (k : ℝ) ^ (j - 1) := by
        have hkj : (k : ℝ) ^ j = (k : ℝ) * (k : ℝ) ^ (j - 1) := by
          conv_lhs => rw [show j = (j - 1) + 1 by omega]
          rw [pow_succ, mul_comm]
        rw [mul_div_assoc', hkj, mul_div_mul_left _ _ hkR.ne']
    _ ≤ ncpMuT G k v j := hratio

/-- **K-th moment.** The probability that at least `K` colours occur on `j` retained neighbours
of `v` each is at most `μ_j^K / K!`. -/
theorem ncpN_tail (G : SimpleGraph V) [DecidableRel G.Adj]
    {k D : ℕ} (hk : 0 < k) (hDk : D ≤ 2 * k) [Nonempty (V → Fin k)]
    (hdeg : ∀ x : V, G.degree x ≤ D) (v : V) {j K : ℕ} (hj : 2 ≤ j) (hK : 0 < K) :
    (colSpace (V := V) k).prob {f : V → Fin k | K ≤ ncpN G f v j}
      ≤ (ncpMuT G k v j) ^ K / (K.factorial : ℝ) := by
  classical
  have hkR : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  have hratio := indepSets_ratio_le (G := G) hk hDk hdeg v hj
  have hratio0 : (0 : ℝ) ≤ ((indepSets G (G.neighborFinset v) j).card : ℝ) / (k : ℝ) ^ (j - 1) := by
    positivity
  set colSets : Finset (Finset (Fin k)) := (Finset.univ : Finset (Fin k)).powersetCard K with hP
  have hsub : {f : V → Fin k | K ≤ ncpN G f v j} ⊆
      ⋃ S ∈ colSets, {f : V → Fin k | ∀ c ∈ S, j ≤ colourClassCount G f v c} := by
    intro f hf
    simp only [Set.mem_ofPred_eq] at hf ⊢
    obtain ⟨S, hSsub, hScard⟩ := Finset.exists_subset_card_eq hf
    refine Set.mem_iUnion.mpr ⟨S, Set.mem_iUnion.mpr ⟨?_, ?_⟩⟩
    · rw [hP, Finset.mem_powersetCard]
      exact ⟨Finset.subset_univ S, hScard⟩
    · intro c hc
      exact (Finset.mem_filter.mp (hSsub hc)).2
  calc (colSpace (V := V) k).prob {f : V → Fin k | K ≤ ncpN G f v j}
      ≤ (colSpace (V := V) k).prob
          (⋃ S ∈ colSets, {f : V → Fin k | ∀ c ∈ S, j ≤ colourClassCount G f v c}) :=
        FinSpace.prob_mono _ hsub
    _ ≤ ∑ S ∈ colSets, (colSpace (V := V) k).prob
          {f : V → Fin k | ∀ c ∈ S, j ≤ colourClassCount G f v c} :=
        FinSpace.prob_biUnion_le_sum _ _ _
    _ ≤ ∑ S ∈ colSets, (((indepSets G (G.neighborFinset v) j).card : ℝ) ^ K
          / (k : ℝ) ^ (j * K)) := by
        refine Finset.sum_le_sum (fun S hS => ?_)
        have hScard : S.card = K := (Finset.mem_powersetCard.mp (by rw [← hP]; exact hS)).2
        have h := colCount_prob_all_le (G := G) hk (v := v) (j := j) (by omega) S
        rwa [hScard] at h
    _ = (colSets.card : ℝ) *
          (((indepSets G (G.neighborFinset v) j).card : ℝ) ^ K / (k : ℝ) ^ (j * K)) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ = (k.choose K : ℝ) *
          (((indepSets G (G.neighborFinset v) j).card : ℝ) ^ K / (k : ℝ) ^ (j * K)) := by
        rw [hP, Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]
    _ ≤ (((k : ℝ) ^ K / (K.factorial : ℝ))) *
          (((indepSets G (G.neighborFinset v) j).card : ℝ) ^ K / (k : ℝ) ^ (j * K)) := by
        refine mul_le_mul_of_nonneg_right (Nat.choose_le_pow_div K k) (by positivity)
    _ = (((indepSets G (G.neighborFinset v) j).card : ℝ) / (k : ℝ) ^ (j - 1)) ^ K /
          (K.factorial : ℝ) := by
        have hexp : j * K = (j - 1) * K + K := by
          conv_lhs => rw [show j = (j - 1) + 1 by omega]
          rw [add_mul, one_mul]
        have hpow : (k : ℝ) ^ (j * K) = ((k : ℝ) ^ (j - 1)) ^ K * (k : ℝ) ^ K := by
          rw [← pow_mul, ← pow_add, hexp]
        rw [div_pow, hpow]
        field_simp
    _ ≤ (ncpMuT G k v j) ^ K / (K.factorial : ℝ) := by
        refine div_le_div_of_nonneg_right (pow_le_pow_left₀ hratio0 hratio K) (by positivity)

end Work.Deep.Sparse
