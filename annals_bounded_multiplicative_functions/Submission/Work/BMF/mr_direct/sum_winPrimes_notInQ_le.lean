import Mathlib
import Submission.Work.BMF.mr_direct.buchstab_aux
import Submission.Work.BMF.mr_direct.dupExtra_defs
import Submission.Work.BMF.mr_direct.card_filter_winPrimes_le_two

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF.mr_direct

open scoped BigOperators
open Work.BMF.mrDirect

/-!
# The sum over non-canonical window primes is controlled by the extra range

For `j ∈ indexSet K P Q` the primes of `winPrimes K j` outside `[P,Q]` are exactly the primes
of the extra range `extraRange K P Q` that happen to lie in `winPrimes K j`. Since a prime lies
in at most two windows, the double sum `Σ_j Σ_{p non-canonical} 1/p` is at most twice the sum
of `1/p` over the extra range.
-/

/-- If every `p ∈ t` lies in at most `c` of the index sets `{j ∈ s | R j p}`, then
`Σ_{j ∈ s} Σ_{p ∈ t, R j p} f p ≤ c · Σ_{p ∈ t} f p` for nonnegative `f` on `t`. -/
lemma sum_sum_filter_le_mul_sum {s t : Finset ℕ} (R : ℕ → ℕ → Prop) [DecidableRel R]
    (c : ℕ) (hc : ∀ p ∈ t, (s.filter (fun j => R j p)).card ≤ c)
    (f : ℕ → ℝ) (hf : ∀ p ∈ t, 0 ≤ f p) :
    ∑ j ∈ s, ∑ p ∈ t.filter (fun p => R j p), f p ≤ (c : ℝ) * ∑ p ∈ t, f p := by
  calc ∑ j ∈ s, ∑ p ∈ t.filter (fun p => R j p), f p
      = ∑ j ∈ s, ∑ p ∈ t, (if R j p then f p else 0) := by
        refine Finset.sum_congr rfl (fun j _ => ?_)
        exact Finset.sum_filter (s := t) (fun p => R j p) f
    _ = ∑ p ∈ t, ∑ j ∈ s, (if R j p then f p else 0) := Finset.sum_comm
    _ = ∑ p ∈ t, ∑ j ∈ s.filter (fun j => R j p), f p := by
        refine Finset.sum_congr rfl (fun p _ => ?_)
        exact (Finset.sum_filter (s := s) (fun j => R j p) (fun _ => f p)).symm
    _ ≤ ∑ p ∈ t, (c : ℝ) * f p := by
        refine Finset.sum_le_sum (fun p hp => ?_)
        rw [Finset.sum_const, nsmul_eq_mul]
        exact mul_le_mul_of_nonneg_right (by exact_mod_cast hc p hp) (hf p hp)
    _ = (c : ℝ) * ∑ p ∈ t, f p := by rw [Finset.mul_sum]

/-- A prime of the extra range is prime. -/
lemma prime_of_mem_extraRange (K P Q : ℝ) {p : ℕ} (hp : p ∈ extraRange K P Q) : p.Prime := by
  rw [extraRange, Finset.mem_union] at hp
  rcases hp with h | h <;>
    · rw [Work.BMF.primesIn, Finset.mem_filter] at h
      exact h.2

/-- For a window index `j` in `indexSet K P Q`, the primes of `winPrimes K j` lying outside
`[P,Q]` are exactly the primes of the extra range `[P e^{-1/K},P] ∪ [Q,Q e^{1/K}]` that lie in
`winPrimes K j`. -/
lemma winPrimes_filter_notInQ_eq (K P Q : ℝ) (hK : 1 ≤ K) (hP : 2 ≤ P) (hPQ : P ≤ Q)
    {j : ℕ} (hj : j ∈ Work.BMF.mrDirect.indexSet K P Q) :
    (Work.BMF.mrDirect.winPrimes K j).filter
        (fun (p : ℕ) => ¬ (P ≤ (p : ℝ) ∧ (p : ℝ) ≤ Q))
      = (Work.BMF.mr_direct.extraRange K P Q).filter
          (fun (p : ℕ) => p ∈ Work.BMF.mrDirect.winPrimes K j ∧
            ¬ (P ≤ (p : ℝ) ∧ (p : ℝ) ≤ Q)) := by
  ext p
  simp only [Finset.mem_filter]
  constructor
  · rintro ⟨hpw, hnon⟩
    refine ⟨?_, hpw, hnon⟩
    have hKpos : 0 < K := lt_of_lt_of_le one_pos hK
    have hextra : (p : ℝ) < P ∨ Q < (p : ℝ) := by
      rcases not_and_or.mp hnon with h | h
      · exact Or.inl (not_le.mp h)
      · exact Or.inr (not_le.mp h)
    exact extra_prime_mem hKpos (by linarith) (by linarith) (by linarith) (by linarith)
      hj hpw hextra
  · rintro ⟨-, hpw, hnon⟩
    exact ⟨hpw, hnon⟩

theorem sum_winPrimes_notInQ_le (K P Q : ℝ) (hK : 1 ≤ K) (hP : 2 ≤ P) (hPQ : P ≤ Q) :
    ∑ j ∈ Work.BMF.mrDirect.indexSet K P Q,
        (∑ p ∈ (Work.BMF.mrDirect.winPrimes K j).filter
            (fun (p : ℕ) => ¬ (P ≤ (p : ℝ) ∧ (p : ℝ) ≤ Q)), (1 : ℝ) / (p : ℝ))
      ≤ 2 * ∑ p ∈ Work.BMF.mr_direct.extraRange K P Q, (1 : ℝ) / (p : ℝ) := by
  have hKpos : 0 < K := lt_of_lt_of_le one_pos hK
  calc ∑ j ∈ Work.BMF.mrDirect.indexSet K P Q,
        (∑ p ∈ (Work.BMF.mrDirect.winPrimes K j).filter
            (fun (p : ℕ) => ¬ (P ≤ (p : ℝ) ∧ (p : ℝ) ≤ Q)), (1 : ℝ) / (p : ℝ))
      = ∑ j ∈ Work.BMF.mrDirect.indexSet K P Q,
          (∑ p ∈ (extraRange K P Q).filter
              (fun (p : ℕ) => p ∈ Work.BMF.mrDirect.winPrimes K j ∧
                ¬ (P ≤ (p : ℝ) ∧ (p : ℝ) ≤ Q)), (1 : ℝ) / (p : ℝ)) := by
        refine Finset.sum_congr rfl (fun j hj => ?_)
        rw [winPrimes_filter_notInQ_eq K P Q hK hP hPQ hj]
    _ ≤ 2 * ∑ p ∈ extraRange K P Q, (1 : ℝ) / (p : ℝ) := by
        refine sum_sum_filter_le_mul_sum
          (R := fun (j p : ℕ) => p ∈ Work.BMF.mrDirect.winPrimes K j ∧
            ¬ (P ≤ (p : ℝ) ∧ (p : ℝ) ≤ Q)) (c := 2)
          (f := fun p => (1 : ℝ) / (p : ℝ)) ?_ ?_
        · intro p hp
          have hsub : (Work.BMF.mrDirect.indexSet K P Q).filter
                (fun j => p ∈ Work.BMF.mrDirect.winPrimes K j ∧
                  ¬ (P ≤ (p : ℝ) ∧ (p : ℝ) ≤ Q))
              ⊆ (Work.BMF.mrDirect.indexSet K P Q).filter
                (fun j => p ∈ Work.BMF.mrDirect.winPrimes K j) := by
            intro j hjm
            rw [Finset.mem_filter] at hjm ⊢
            exact ⟨hjm.1, hjm.2.1⟩
          exact le_trans (Finset.card_le_card hsub)
            (card_filter_winPrimes_le_two K hKpos (Work.BMF.mrDirect.indexSet K P Q) p)
        · intro p hp
          have hp2 : (2 : ℝ) ≤ (p : ℝ) :=
            by exact_mod_cast (prime_of_mem_extraRange K P Q hp).two_le
          have hp0 : (0 : ℝ) < (p : ℝ) := by linarith
          exact le_of_lt (div_pos zero_lt_one hp0)

end Work.BMF.mr_direct
