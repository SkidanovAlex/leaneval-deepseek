import Mathlib
import Submission.Work.BMF.mr_direct.dupExtra_defs
import Submission.Work.BMF.mr_direct.sum_inv_primes_near
import Submission.Work.BMF.mr_direct.sum_inv_primes_extraRange
import Submission.Work.BMF.mr_direct.card_winPrimes_filter_inQ_ne_jdex_le_one
import Submission.Work.BMF.mr_direct.card_filter_winPrimes_le_two
import Submission.Work.BMF.mr_direct.sum_winPrimes_notInQ_le

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

namespace Work.BMF.mr_direct

open scoped BigOperators
open Work.BMF.mrDirect

/-- `pairSetD K P Q` is the set of pairs `(j,p)` with `j ∈ indexSet K P Q`, `p` a prime in the
`j`-th logarithmic window `winPrimes K j`, and `p` *not* canonical for `j` (i.e. either `p ∉ [P,Q]`
or `j ≠ jdex K p`).  We split the reciprocal sum over it into the contribution of the primes
`p ∈ [P,Q]` occurring in a non-canonical window (at most one such pair) and the contribution of
the primes outside `[P,Q]` (which lie in the extra range and occur in at most two windows). -/
theorem pairSetD_inv_le (K P Q : ℝ) (hK : 1 ≤ K) (hP : 2 ≤ P) (hPQ : P ≤ Q) :
    ∑ y ∈ Work.BMF.mr_direct.pairSetD K P Q, (1 : ℝ) / (y.2 : ℝ)
      ≤ 65 * (1 / K + 1 / P) := by
  have hKpos : 0 < K := lt_of_lt_of_le one_pos hK
  have hPpos : 0 < P := by linarith
  have h1K : 0 ≤ 1 / K := by positivity
  have h1P : 0 ≤ 1 / P := by positivity
  -- ### Step 1: unfold the `sigma`-indexed sum
  have hS : ∑ y ∈ pairSetD K P Q, (1 : ℝ) / (y.2 : ℝ)
      = ∑ j ∈ indexSet K P Q,
          ∑ p ∈ (winPrimes K j).filter
            (fun (p : ℕ) => ¬ (P ≤ (p : ℝ) ∧ (p : ℝ) ≤ Q ∧ j = jdex K p)),
            (1 : ℝ) / (p : ℝ) := by
    rw [pairSetD_eq]
    exact Finset.sum_sigma _ _ _
  -- ### Step 2: split each inner sum into `p ∈ [P,Q]` and `p ∉ [P,Q]`
  have hsplit : ∀ j : ℕ,
      (∑ p ∈ (winPrimes K j).filter
          (fun (p : ℕ) => ¬ (P ≤ (p : ℝ) ∧ (p : ℝ) ≤ Q ∧ j = jdex K p)), (1 : ℝ) / (p : ℝ))
      = (∑ p ∈ (winPrimes K j).filter
          (fun (p : ℕ) => P ≤ (p : ℝ) ∧ (p : ℝ) ≤ Q ∧ j ≠ jdex K p), (1 : ℝ) / (p : ℝ))
        + (∑ p ∈ (winPrimes K j).filter
          (fun (p : ℕ) => ¬ (P ≤ (p : ℝ) ∧ (p : ℝ) ≤ Q)), (1 : ℝ) / (p : ℝ)) := by
    intro j
    have hset : (winPrimes K j).filter
          (fun (p : ℕ) => ¬ (P ≤ (p : ℝ) ∧ (p : ℝ) ≤ Q ∧ j = jdex K p))
        = (winPrimes K j).filter
            (fun (p : ℕ) => P ≤ (p : ℝ) ∧ (p : ℝ) ≤ Q ∧ j ≠ jdex K p)
          ∪ (winPrimes K j).filter (fun (p : ℕ) => ¬ (P ≤ (p : ℝ) ∧ (p : ℝ) ≤ Q)) := by
      ext p
      simp only [Finset.mem_filter, Finset.mem_union]
      constructor
      · rintro ⟨hw, hnc⟩
        by_cases hA : P ≤ (p : ℝ) ∧ (p : ℝ) ≤ Q
        · exact Or.inl ⟨hw, hA.1, hA.2, fun h => hnc ⟨hA.1, hA.2, h⟩⟩
        · exact Or.inr ⟨hw, hA⟩
      · rintro (⟨hw, hA1, hA2, hne⟩ | ⟨hw, hna⟩)
        · exact ⟨hw, fun h => hne h.2.2⟩
        · exact ⟨hw, fun h => hna ⟨h.1, h.2.1⟩⟩
    have hdisj : Disjoint
        ((winPrimes K j).filter (fun (p : ℕ) => P ≤ (p : ℝ) ∧ (p : ℝ) ≤ Q ∧ j ≠ jdex K p))
        ((winPrimes K j).filter (fun (p : ℕ) => ¬ (P ≤ (p : ℝ) ∧ (p : ℝ) ≤ Q))) := by
      rw [Finset.disjoint_left]
      intro p hp hq
      obtain ⟨-, hPp, hpQ, -⟩ := Finset.mem_filter.mp hp
      exact (Finset.mem_filter.mp hq).2 ⟨hPp, hpQ⟩
    rw [hset, Finset.sum_union hdisj]
  have hS2 : ∑ y ∈ pairSetD K P Q, (1 : ℝ) / (y.2 : ℝ)
      = (∑ j ∈ indexSet K P Q,
            ∑ p ∈ (winPrimes K j).filter
              (fun (p : ℕ) => P ≤ (p : ℝ) ∧ (p : ℝ) ≤ Q ∧ j ≠ jdex K p),
              (1 : ℝ) / (p : ℝ))
        + (∑ j ∈ indexSet K P Q,
            ∑ p ∈ (winPrimes K j).filter
              (fun (p : ℕ) => ¬ (P ≤ (p : ℝ) ∧ (p : ℝ) ≤ Q)),
              (1 : ℝ) / (p : ℝ)) := by
    rw [hS, Finset.sum_congr rfl (fun j _ => hsplit j), Finset.sum_add_distrib]
  -- ### Step 3: the primes `p ∈ [P,Q]` contribute at most `1/P`
  have hA : (∑ j ∈ indexSet K P Q,
            ∑ p ∈ (winPrimes K j).filter
              (fun (p : ℕ) => P ≤ (p : ℝ) ∧ (p : ℝ) ≤ Q ∧ j ≠ jdex K p),
              (1 : ℝ) / (p : ℝ)) ≤ 1 / P := by
    have hunion : (∑ j ∈ indexSet K P Q,
            ∑ p ∈ (winPrimes K j).filter
              (fun (p : ℕ) => P ≤ (p : ℝ) ∧ (p : ℝ) ≤ Q ∧ j ≠ jdex K p),
              (1 : ℝ) / (p : ℝ))
        = ∑ x ∈ (indexSet K P Q).sigma (fun j =>
            (winPrimes K j).filter
              (fun (p : ℕ) => P ≤ (p : ℝ) ∧ (p : ℝ) ≤ Q ∧ j ≠ jdex K p)),
            (1 : ℝ) / ((x.2 : ℕ) : ℝ) :=
      (Finset.sum_sigma (indexSet K P Q)
        (fun j => (winPrimes K j).filter
              (fun (p : ℕ) => P ≤ (p : ℝ) ∧ (p : ℝ) ≤ Q ∧ j ≠ jdex K p))
        (fun y : Sigma (fun _ : ℕ => ℕ) => (1 : ℝ) / ((y.2 : ℕ) : ℝ))).symm
    have hcard : ((indexSet K P Q).sigma (fun j =>
            (winPrimes K j).filter
              (fun (p : ℕ) => P ≤ (p : ℝ) ∧ (p : ℝ) ≤ Q ∧ j ≠ jdex K p))).card ≤ 1 :=
      card_winPrimes_filter_inQ_ne_jdex_le_one K P Q hKpos
    rw [hunion]
    calc ∑ x ∈ (indexSet K P Q).sigma (fun j =>
            (winPrimes K j).filter
              (fun (p : ℕ) => P ≤ (p : ℝ) ∧ (p : ℝ) ≤ Q ∧ j ≠ jdex K p)),
            (1 : ℝ) / ((x.2 : ℕ) : ℝ)
        ≤ ∑ x ∈ (indexSet K P Q).sigma (fun j =>
            (winPrimes K j).filter
              (fun (p : ℕ) => P ≤ (p : ℝ) ∧ (p : ℝ) ≤ Q ∧ j ≠ jdex K p)),
            (1 : ℝ) / P := by
          refine Finset.sum_le_sum (fun x hx => ?_)
          obtain ⟨j, p⟩ := x
          obtain ⟨-, hPp, -, -⟩ := Finset.mem_filter.mp (Finset.mem_sigma.mp hx).2
          exact one_div_le_one_div_of_le hPpos hPp
      _ = (((indexSet K P Q).sigma (fun j =>
            (winPrimes K j).filter
              (fun (p : ℕ) => P ≤ (p : ℝ) ∧ (p : ℝ) ≤ Q ∧ j ≠ jdex K p))).card : ℝ)
            * (1 / P) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ 1 * (1 / P) := by
          have h1 : (((indexSet K P Q).sigma (fun j =>
            (winPrimes K j).filter
              (fun (p : ℕ) => P ≤ (p : ℝ) ∧ (p : ℝ) ≤ Q ∧ j ≠ jdex K p))).card : ℝ) ≤ 1 := by
            exact_mod_cast hcard
          exact mul_le_mul_of_nonneg_right h1 h1P
      _ = 1 / P := by ring
  -- ### Step 4: the primes `p ∉ [P,Q]` contribute at most `2 ∑_{p ∈ extraRange} 1/p`
  have hB : (∑ j ∈ indexSet K P Q,
            ∑ p ∈ (winPrimes K j).filter
              (fun (p : ℕ) => ¬ (P ≤ (p : ℝ) ∧ (p : ℝ) ≤ Q)),
              (1 : ℝ) / (p : ℝ))
        ≤ 2 * ∑ p ∈ extraRange K P Q, (1 : ℝ) / (p : ℝ) :=
    sum_winPrimes_notInQ_le K P Q hK hP hPQ
  have hC : ∑ p ∈ extraRange K P Q, (1 : ℝ) / (p : ℝ) ≤ 32 * (1 / K + 1 / P) :=
    sum_inv_primes_extraRange K P Q hK hP hPQ
  -- ### Assembly
  calc ∑ y ∈ pairSetD K P Q, (1 : ℝ) / (y.2 : ℝ)
      = (∑ j ∈ indexSet K P Q,
            ∑ p ∈ (winPrimes K j).filter
              (fun (p : ℕ) => P ≤ (p : ℝ) ∧ (p : ℝ) ≤ Q ∧ j ≠ jdex K p),
              (1 : ℝ) / (p : ℝ))
        + (∑ j ∈ indexSet K P Q,
            ∑ p ∈ (winPrimes K j).filter
              (fun (p : ℕ) => ¬ (P ≤ (p : ℝ) ∧ (p : ℝ) ≤ Q)),
              (1 : ℝ) / (p : ℝ)) := hS2
    _ ≤ 1 / P + 2 * (∑ p ∈ extraRange K P Q, (1 : ℝ) / (p : ℝ)) := add_le_add hA hB
    _ ≤ 1 / P + 2 * (32 * (1 / K + 1 / P)) := by
        have h2 : (0 : ℝ) ≤ 2 := by norm_num
        exact add_le_add le_rfl (mul_le_mul_of_nonneg_left hC h2)
    _ ≤ 65 * (1 / K + 1 / P) := by nlinarith [h1K]

end Work.BMF.mr_direct
