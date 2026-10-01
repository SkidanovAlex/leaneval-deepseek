import Mathlib

namespace Work.ZeroDensity.Jutila.LzDiffAux

/-- For `t ∈ [1,T]`, the divisors of `t` are exactly the elements `d` of `[1,T]` that divide `t`.
(Every divisor of `t ≥ 1` is automatically in `[1,T]`, and conversely dividing is all that
matters.) -/
private lemma divisors_eq_filter_Icc {T t : ℕ} (ht : t ∈ Finset.Icc 1 T) :
    t.divisors = (Finset.Icc 1 T).filter (fun d => d ∣ t) := by
  have ht1 : 1 ≤ t := (Finset.mem_Icc.mp ht).1
  have htT : t ≤ T := (Finset.mem_Icc.mp ht).2
  ext d
  simp only [Nat.mem_divisors, Finset.mem_filter, Finset.mem_Icc]
  constructor
  · rintro ⟨hdvd, hne⟩
    refine ⟨⟨Nat.pos_of_dvd_of_pos hdvd (by omega), ?_⟩, hdvd⟩
    exact (Nat.le_of_dvd (by omega) hdvd).trans htT
  · rintro ⟨⟨hd1, _⟩, hdvd⟩
    exact ⟨hdvd, by omega⟩

/-- For a fixed `d ∈ [1,T]`, the multiples of `d` lying in `[1,T]` are exactly `d * m` with
`m ∈ [1, T / d]`. -/
private lemma sum_filter_dvd_eq {T d : ℕ} (hd : d ∈ Finset.Icc 1 T) (F : ℕ → ℕ → ℝ) :
    (∑ t ∈ (Finset.Icc 1 T).filter (fun t => d ∣ t), F d t)
      = ∑ m ∈ Finset.Icc 1 (T / d), F d (d * m) := by
  have hd1 : 1 ≤ d := (Finset.mem_Icc.mp hd).1
  have hdT : d ≤ T := (Finset.mem_Icc.mp hd).2
  have hdpos : 0 < d := by omega
  refine Finset.sum_nbij' (fun t => t / d) (fun m => d * m) ?_ ?_ ?_ ?_ ?_
  · intro t ht
    rw [Finset.mem_filter] at ht
    obtain ⟨htIcc, hdt⟩ := ht
    have ht1 : 1 ≤ t := (Finset.mem_Icc.mp htIcc).1
    have htT : t ≤ T := (Finset.mem_Icc.mp htIcc).2
    rw [Finset.mem_Icc]
    refine ⟨?_, Nat.div_le_div_right htT⟩
    rw [Nat.one_le_div_iff hdpos]
    exact Nat.le_of_dvd (by omega) hdt
  · intro m hm
    rw [Finset.mem_Icc] at hm
    obtain ⟨hm1, hm2⟩ := hm
    rw [Finset.mem_filter, Finset.mem_Icc]
    refine ⟨⟨by simpa using Nat.mul_le_mul hd1 hm1, ?_⟩, dvd_mul_right d m⟩
    · have h2 : m * d ≤ T := (Nat.le_div_iff_mul_le hdpos).mp hm2
      calc d * m = m * d := by ring
        _ ≤ T := h2
  · intro t ht
    rw [Finset.mem_filter] at ht
    exact Nat.mul_div_cancel' ht.2
  · intro m hm
    exact Nat.mul_div_cancel_left m hdpos
  · intro t ht
    rw [Finset.mem_filter] at ht
    rw [Nat.mul_div_cancel' ht.2]

/-- Reindexing a double sum over divisors: summing `F d t` over all pairs `(t,d)` with
`1 ≤ t ≤ T` and `d ∣ t` is the same as summing `F d (d * m)` over all pairs `(d,m)` with
`1 ≤ d ≤ T` and `1 ≤ m ≤ T / d`. -/
theorem SumDivisorsIccSwap (F : ℕ → ℕ → ℝ) (T : ℕ) :
    (∑ t ∈ Finset.Icc 1 T, ∑ d ∈ t.divisors, F d t)
      = ∑ d ∈ Finset.Icc 1 T, ∑ m ∈ Finset.Icc 1 (T / d), F d (d * m) := by
  calc
    (∑ t ∈ Finset.Icc 1 T, ∑ d ∈ t.divisors, F d t)
        = ∑ t ∈ Finset.Icc 1 T, ∑ d ∈ Finset.Icc 1 T, (if d ∣ t then F d t else 0) := by
            apply Finset.sum_congr rfl
            intro t ht
            rw [divisors_eq_filter_Icc ht, Finset.sum_filter]
    _ = ∑ d ∈ Finset.Icc 1 T, ∑ t ∈ Finset.Icc 1 T, (if d ∣ t then F d t else 0) :=
            Finset.sum_comm
    _ = ∑ d ∈ Finset.Icc 1 T, ∑ m ∈ Finset.Icc 1 (T / d), F d (d * m) := by
            apply Finset.sum_congr rfl
            intro d hd
            rw [← Finset.sum_filter]
            exact sum_filter_dvd_eq hd F

end Work.ZeroDensity.Jutila.LzDiffAux
