import Mathlib

namespace Work.FIArea7

/-- Reindexing a double sum over `n ≤ T` and divisors `d ∣ n` with `d ≤ C` as a sum over pairs
`(d, ℓ)` with `d ∈ [1,T]`, `d ≤ C`, `ℓ ∈ [1,T]`.  The hypothesis `hf` kills the terms with
`d * ℓ > T`, which is what makes the extension of the inner sum to all `ℓ ≤ T` legitimate. -/
lemma divisors_pair_reindex (T : ℕ) (C : ℝ) (f : ℕ → ℕ → ℂ)
    (hf : ∀ d ℓ : ℕ, T < d * ℓ → f (d * ℓ) d = 0) :
    (∑ n ∈ Finset.Icc 1 T, ∑ d ∈ n.divisors.filter (fun d => ((d : ℕ) : ℝ) ≤ C), f n d)
      = ∑ d ∈ (Finset.Icc 1 T).filter (fun d => ((d : ℕ) : ℝ) ≤ C),
          ∑ ℓ ∈ Finset.Icc 1 T, f (d * ℓ) d := by
  set A : Finset ℕ := (Finset.Icc 1 T).filter (fun d => ((d : ℕ) : ℝ) ≤ C) with hA
  have step0 : (∑ n ∈ Finset.Icc 1 T, ∑ d ∈ n.divisors.filter (fun d => ((d : ℕ) : ℝ) ≤ C), f n d)
      = ∑ n ∈ Finset.Icc 1 T, ∑ d ∈ A, (if d ∣ n then f n d else 0) := by
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [Finset.mem_Icc] at hn
    have hset : n.divisors.filter (fun d => ((d : ℕ) : ℝ) ≤ C) = A.filter (fun d => d ∣ n) := by
      rw [hA]
      ext d
      simp only [Finset.mem_filter, Finset.mem_Icc, Nat.mem_divisors]
      constructor
      · rintro ⟨⟨hdvd, hn0⟩, hC⟩
        exact ⟨⟨⟨Nat.pos_of_dvd_of_pos hdvd (by omega),
            le_trans (Nat.le_of_dvd (by omega) hdvd) hn.2⟩, hC⟩, hdvd⟩
      · rintro ⟨⟨⟨hd1, hdT⟩, hC⟩, hdvd⟩
        exact ⟨⟨hdvd, by omega⟩, hC⟩
    rw [hset, Finset.sum_filter]
  rw [step0, Finset.sum_comm]
  refine Finset.sum_congr rfl ?_
  intro d hd
  rw [hA] at hd
  have hdpos : 0 < d := (Finset.mem_Icc.mp (Finset.mem_filter.mp hd).1).1
  have hlhs : (∑ n ∈ Finset.Icc 1 T, (if d ∣ n then f n d else 0))
      = ∑ n ∈ (Finset.Icc 1 T).filter (fun n => d ∣ n), f n d := by
    rw [Finset.sum_filter]
  have hrhs : (∑ ℓ ∈ Finset.Icc 1 T, f (d * ℓ) d)
      = ∑ ℓ ∈ (Finset.Icc 1 T).filter (fun ℓ => d * ℓ ≤ T), f (d * ℓ) d := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl ?_
    intro ℓ _
    by_cases h : d * ℓ ≤ T
    · simp [h]
    · rw [if_neg h]; exact hf d ℓ (not_le.mp h)
  rw [hlhs, hrhs]
  refine Finset.sum_bij' (fun n _ => n / d) (fun ℓ _ => d * ℓ) ?_ ?_ ?_ ?_ ?_
  · intro n hn
    rw [Finset.mem_filter] at hn ⊢
    obtain ⟨hnIcc, hdvd⟩ := hn
    rw [Finset.mem_Icc] at hnIcc ⊢
    obtain ⟨hn1, hnT⟩ := hnIcc
    exact ⟨⟨Nat.div_pos (Nat.le_of_dvd (by omega) hdvd) hdpos,
        le_trans (Nat.div_le_self n d) hnT⟩,
      by rw [Nat.mul_div_cancel' hdvd]; exact hnT⟩
  · intro ℓ hℓ
    rw [Finset.mem_filter] at hℓ ⊢
    obtain ⟨hℓIcc, hℓT⟩ := hℓ
    rw [Finset.mem_Icc] at hℓIcc ⊢
    obtain ⟨hℓ1, hℓT'⟩ := hℓIcc
    exact ⟨⟨Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega)), hℓT⟩,
      dvd_mul_right d ℓ⟩
  · intro n hn
    rw [Finset.mem_filter] at hn
    exact Nat.mul_div_cancel' hn.2
  · intro ℓ hℓ
    exact Nat.mul_div_cancel_left ℓ hdpos
  · intro n hn
    rw [Finset.mem_filter] at hn
    rw [Nat.mul_div_cancel' hn.2]

end Work.FIArea7
