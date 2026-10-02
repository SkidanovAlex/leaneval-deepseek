import Mathlib
import Submission.Work.BzHard.Bz_sq_reindex

namespace Work.LinnikAreas.Density4.BzHard

open Finset

noncomputable section

/-- `(μ m)²`, as a real number, is the indicator of `m` being squarefree. -/
lemma s3_moebius_sq_cast_ite (m : ℕ) :
    ((ArithmeticFunction.moebius m : ℝ)) ^ 2 = if Squarefree m then 1 else 0 := by
  by_cases h : Squarefree m
  · rw [if_pos h]
    have h1 : (ArithmeticFunction.moebius m : ℤ) ^ 2 = 1 :=
      ArithmeticFunction.moebius_sq_eq_one_of_squarefree h
    have h2 : ((ArithmeticFunction.moebius m : ℝ)) ^ 2
        = (((ArithmeticFunction.moebius m : ℤ) ^ 2 : ℤ) : ℝ) := by push_cast; ring
    rw [h2, h1]; norm_num
  · rw [if_neg h, ArithmeticFunction.moebius_eq_zero_of_not_squarefree h]; norm_num

/-- **The `m`-sum of the reindexed form equals the `m`-sum of the quadruple form.**
The reindexing `Bz_sq_reindex` produces the inner sum over the range `m ≤ N/(qrt)` with the
weight `μ(m)²·log(mt/z)·log(mr/z)`; here this is rewritten as a sum over `m ≤ N` with the
squarefree indicator and the constraint `q·r·t·m ≤ N`. -/
lemma s3_m_sum (z N q r t : ℕ) (hqrt : 0 < q * r * t) :
    (if Nat.Coprime r t then
        (ArithmeticFunction.moebius r : ℝ) * (ArithmeticFunction.moebius t : ℝ) *
          (∑ m ∈ (Finset.Icc 1 (N / (q * r * t))).filter
              (fun m => Nat.Coprime m (r * t) ∧ z < m * t ∧ z < m * r),
            ((ArithmeticFunction.moebius m : ℝ)) ^ 2 *
              Real.log ((m : ℝ) * (t : ℝ) / (z : ℝ)) *
              Real.log ((m : ℝ) * (r : ℝ) / (z : ℝ)))
      else 0)
      = (if Nat.Coprime r t then
          (ArithmeticFunction.moebius r : ℝ) * (ArithmeticFunction.moebius t : ℝ) else 0) *
        (∑ m ∈ Finset.Icc 1 N,
            if Nat.Coprime m (r * t) ∧ Squarefree m ∧ z < t * m ∧ z < r * m
                ∧ q * r * t * m ≤ N
              then Real.log (((t * m : ℕ) : ℝ) / (z : ℝ))
                    * Real.log (((r * m : ℕ) : ℝ) / (z : ℝ))
              else 0) := by
  by_cases hc : Nat.Coprime r t
  · rw [if_pos hc, if_pos hc]
    congr 1
    have hset : (Finset.Icc 1 (N / (q * r * t))).filter
          (fun m => Nat.Coprime m (r * t) ∧ z < m * t ∧ z < m * r)
        = (Finset.Icc 1 N).filter
          (fun m => Nat.Coprime m (r * t) ∧ z < m * t ∧ z < m * r ∧ q * r * t * m ≤ N) := by
      ext m
      simp only [Finset.mem_filter, Finset.mem_Icc]
      constructor
      · rintro ⟨⟨hm1, hm2⟩, hP⟩
        obtain ⟨hC, hz1, hz2⟩ := hP
        have hmul : q * r * t * m ≤ N := by
          rw [← Nat.mul_comm m (q * r * t)]
          exact (Nat.le_div_iff_mul_le hqrt).mp hm2
        exact ⟨⟨hm1, le_trans hm2 (Nat.div_le_self N (q * r * t))⟩, hC, hz1, hz2, hmul⟩
      · rintro ⟨⟨hm1, _⟩, hP⟩
        obtain ⟨hC, hz1, hz2, hmul⟩ := hP
        refine ⟨⟨hm1, ?_⟩, hC, hz1, hz2⟩
        exact (Nat.le_div_iff_mul_le hqrt).mpr (by rw [Nat.mul_comm m (q * r * t)]; exact hmul)
    rw [hset, Finset.sum_filter]
    refine Finset.sum_congr rfl (fun m _ => ?_)
    rw [s3_moebius_sq_cast_ite]
    by_cases hA : Nat.Coprime m (r * t) ∧ z < m * t ∧ z < m * r ∧ q * r * t * m ≤ N
    · rw [if_pos hA]
      by_cases hs : Squarefree m
      · have hB : Nat.Coprime m (r * t) ∧ Squarefree m ∧ z < t * m ∧ z < r * m
            ∧ q * r * t * m ≤ N :=
          ⟨hA.1, hs, by rw [Nat.mul_comm t m]; exact hA.2.1,
            by rw [Nat.mul_comm r m]; exact hA.2.2.1, hA.2.2.2⟩
        rw [if_pos hB, if_pos hs, one_mul]
        congr 1
        · congr 1; push_cast; ring
        · congr 1; push_cast; ring
      · have hB : ¬ (Nat.Coprime m (r * t) ∧ Squarefree m ∧ z < t * m ∧ z < r * m
            ∧ q * r * t * m ≤ N) := fun h => hs h.2.1
        rw [if_neg hB, if_neg hs]
        ring
    · have hB : ¬ (Nat.Coprime m (r * t) ∧ Squarefree m ∧ z < t * m ∧ z < r * m
          ∧ q * r * t * m ≤ N) :=
        fun h => hA ⟨h.1, by rw [Nat.mul_comm m t]; exact h.2.2.1,
          by rw [Nat.mul_comm m r]; exact h.2.2.2.1, h.2.2.2.2⟩
      rw [if_neg hA, if_neg hB]
  · rw [if_neg hc, if_neg hc, zero_mul]

theorem S3_eq_quadruple (z N : ℕ) (hz : 2 ≤ z) (hN : N < z * z) :
    (∑ n ∈ Finset.Icc 1 N, (Work.LinnikAreas.Density4.Bz z n) ^ 2)
      = ∑ q ∈ Finset.Icc 1 N, ∑ r ∈ Finset.Icc 1 N, ∑ t ∈ Finset.Icc 1 N,
          (if Nat.Coprime r t then
              (ArithmeticFunction.moebius r : ℝ) * (ArithmeticFunction.moebius t : ℝ)
            else 0)
          * (∑ m ∈ Finset.Icc 1 N,
              if Nat.Coprime m (r * t) ∧ Squarefree m ∧ z < t * m ∧ z < r * m
                  ∧ q * r * t * m ≤ N
                then Real.log (((t * m : ℕ) : ℝ) / (z : ℝ))
                      * Real.log (((r * m : ℕ) : ℝ) / (z : ℝ))
                else 0) := by
  have _hN := hN
  have hz1 : 1 ≤ z := by omega
  have hLHS : (∑ n ∈ Finset.Icc 1 N, (Work.LinnikAreas.Density4.Bz z n) ^ 2)
      = ∑ n ∈ Finset.Icc 2 N, (Work.LinnikAreas.Density4.Bz z n) ^ 2 := by
    refine (Finset.sum_subset ?_ ?_).symm
    · intro x hx
      simp only [Finset.mem_Icc] at hx ⊢
      omega
    · intro x hx hx2
      simp only [Finset.mem_Icc] at hx hx2
      have hx1 : x = 1 := by omega
      rw [hx1, Work.LinnikAreas.Density4.Bz_one]
      norm_num
  rw [hLHS, Work.BzHard.Bz_sq_reindex z N hz1]
  refine Finset.sum_congr rfl (fun q hq => Finset.sum_congr rfl (fun r hr =>
    Finset.sum_congr rfl (fun t ht => ?_)))
  have hq1 : 1 ≤ q := (Finset.mem_Icc.mp hq).1
  have hr1 : 1 ≤ r := (Finset.mem_Icc.mp hr).1
  have ht1 : 1 ≤ t := (Finset.mem_Icc.mp ht).1
  exact s3_m_sum z N q r t (by positivity)

end

end Work.LinnikAreas.Density4.BzHard
