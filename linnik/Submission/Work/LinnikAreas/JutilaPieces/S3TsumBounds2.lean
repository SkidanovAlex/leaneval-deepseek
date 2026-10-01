import Mathlib
import Submission.Work.ZeroDensity.Jutila.Bz3Defs
import Submission.Work.LinnikAreas.JutilaPieces.HarmonicLogBound

namespace Work.LinnikAreas.JutilaPieces

/-! ## Helper lemmas for `S3TsumBounds2` (verified, sorry-free)

`t/κ(t) ≤ 1` on squarefree `t`; the pointwise reduction of the first summand; the divisor-count
bound `#{t ≤ T : d ∣ t} ≤ T/d`; and the telescoping estimate `Σ_{d≤T} 1/(d√d) ≤ 3`.
These are the steps of the first conjunct; the second conjunct uses
`σ_{−1/2}(t)/κ(t) ≤ (1/t)∏_{p|t}(1+1/√p)` and the same divisor swap. -/

lemma s3Tsum_div_kap_le_one (t : ℕ) (ht : Squarefree t) :
    (t:ℝ)/Work.ZeroDensity.Jutila.kap t ≤ 1 := by
  have hprod : (∏ p ∈ t.primeFactors, (p:ℝ)) = (t:ℝ) := by
    rw [← Nat.cast_prod, Nat.prod_primeFactors_of_squarefree ht]
  have hkey : (t : ℝ)/Work.ZeroDensity.Jutila.kap t
      = ∏ p ∈ t.primeFactors, ((p:ℝ)/((p:ℝ)+1)) := by
    rw [Work.ZeroDensity.Jutila.kap, ← hprod, ← Finset.prod_div_distrib]
  rw [hkey]
  refine Finset.prod_le_one₀ (fun p hp => ?_) (fun p hp => ?_)
  · exact div_nonneg (by positivity) (by positivity)
  · rw [div_le_one (by positivity)]; linarith [show (0:ℝ) ≤ (p:ℝ) by positivity]

lemma s3Tsum_pointwise (t : ℕ) :
    |(ArithmeticFunction.moebius t : ℝ)| * ((t:ℝ)/Work.ZeroDensity.Jutila.kap t)
      * (∑ d ∈ t.divisors, 1/Real.sqrt (d:ℝ))
    ≤ |(ArithmeticFunction.moebius t : ℝ)| * (∑ d ∈ t.divisors, 1/Real.sqrt (d:ℝ)) := by
  by_cases h : Squarefree t
  · have hk := s3Tsum_div_kap_le_one t h
    have hs : (0:ℝ) ≤ ∑ d ∈ t.divisors, 1/Real.sqrt (d:ℝ) :=
      Finset.sum_nonneg (fun d _ => by positivity)
    have hm : (0:ℝ) ≤ |(ArithmeticFunction.moebius t : ℝ)| := abs_nonneg _
    calc |(ArithmeticFunction.moebius t : ℝ)| * ((t:ℝ)/Work.ZeroDensity.Jutila.kap t)
          * (∑ d ∈ t.divisors, 1/Real.sqrt (d:ℝ))
        = |(ArithmeticFunction.moebius t : ℝ)|
            * (((t:ℝ)/Work.ZeroDensity.Jutila.kap t)
                * (∑ d ∈ t.divisors, 1/Real.sqrt (d:ℝ))) := by ring
      _ ≤ |(ArithmeticFunction.moebius t : ℝ)|
            * (1 * (∑ d ∈ t.divisors, 1/Real.sqrt (d:ℝ))) := by
          apply mul_le_mul_of_nonneg_left _ hm
          exact mul_le_mul_of_nonneg_right hk hs
      _ = _ := by ring
  · have hm : (ArithmeticFunction.moebius t : ℝ) = 0 := by
      rw [ArithmeticFunction.moebius_eq_zero_of_not_squarefree h]; simp
    rw [hm]; simp

lemma s3Tsum_card_le (T d : ℕ) : ((Finset.Icc 1 T).filter (fun t => d ∣ t)).card ≤ T / d := by
  rcases Nat.eq_zero_or_pos d with h | h
  · subst h
    have hsub : (Finset.Icc 1 T).filter (fun t => 0 ∣ t) ⊆ (∅ : Finset ℕ) := by
      intro t ht
      rw [Finset.mem_filter, Finset.mem_Icc] at ht
      have h2 : t = 0 := Nat.eq_zero_of_zero_dvd ht.2
      omega
    have hc := Finset.card_le_card hsub
    rw [Finset.card_empty] at hc
    rw [Nat.div_zero]
    omega
  · have h1 : ((Finset.Icc 1 T).filter (fun t => d ∣ t)).card ≤ (Finset.Icc 1 (T/d)).card := by
      refine Finset.card_le_card_of_injOn (fun t => t / d) ?_ ?_
      · intro t ht
        rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_Icc] at ht
        obtain ⟨⟨ht1, ht2⟩, ht3⟩ := ht
        rw [Finset.mem_coe, Finset.mem_Icc]
        exact ⟨Nat.div_pos (Nat.le_of_dvd (by omega) ht3) h, Nat.div_le_div_right ht2⟩
      · intro t ht u hu htu
        rw [Finset.mem_coe, Finset.mem_filter] at ht hu
        change t / d = u / d at htu
        have h1 : d * (t/d) = t := Nat.mul_div_cancel' ht.2
        have h2 : d * (u/d) = u := Nat.mul_div_cancel' hu.2
        rw [htu, h2] at h1
        exact h1.symm
    rw [Nat.card_Icc] at h1
    simpa [Nat.add_sub_cancel] using h1

lemma s3Tsum_rpow (d : ℕ) (hd : 2 ≤ d) :
    (1:ℝ)/((d:ℝ)*Real.sqrt d) ≤ 2/Real.sqrt ((d-1:ℕ):ℝ) - 2/Real.sqrt (d:ℝ) := by
  have hd0 : (0:ℝ) < ((d-1:ℕ):ℝ) := by
    have : 1 ≤ d-1 := by omega
    have : (1:ℝ) ≤ ((d-1:ℕ):ℝ) := by exact_mod_cast this
    linarith
  have hdp : (0:ℝ) < (d:ℝ) := by positivity
  have hs0 : 0 < Real.sqrt ((d-1:ℕ):ℝ) := Real.sqrt_pos_of_pos hd0
  have hsp : 0 < Real.sqrt (d:ℝ) := Real.sqrt_pos_of_pos hdp
  have hsq1 : Real.sqrt ((d-1:ℕ):ℝ)^2 = ((d-1:ℕ):ℝ) := Real.sq_sqrt hd0.le
  have hsq2 : Real.sqrt (d:ℝ)^2 = (d:ℝ) := Real.sq_sqrt hdp.le
  have hcast : ((d-1:ℕ):ℝ) = (d:ℝ) - 1 := by
    have : 1 ≤ d := by omega
    push_cast [Nat.cast_sub this]; ring
  have hkey : Real.sqrt (d:ℝ) - Real.sqrt ((d-1:ℕ):ℝ)
      = 1/(Real.sqrt (d:ℝ) + Real.sqrt ((d-1:ℕ):ℝ)) := by
    rw [eq_div_iff (by positivity)]
    nlinarith [hsq1, hsq2, hcast]
  have h1 : Real.sqrt (d:ℝ) * Real.sqrt ((d-1:ℕ):ℝ) ≤ (d:ℝ) := by
    nlinarith [hsq1, hsq2, Real.sqrt_nonneg (d:ℝ), Real.sqrt_nonneg ((d-1:ℕ):ℝ), hdp.le]
  have h2 : (Real.sqrt (d:ℝ) + Real.sqrt ((d-1:ℕ):ℝ)) * Real.sqrt ((d-1:ℕ):ℝ) ≤ 2*(d:ℝ) := by
    nlinarith [hsq1, h1, hcast]
  have hden : 0 < Real.sqrt ((d-1:ℕ):ℝ) * Real.sqrt (d:ℝ) := by positivity
  rw [div_sub_div (2:ℝ) (2:ℝ) hs0.ne' hsp.ne']
  rw [show 2 * Real.sqrt (d:ℝ) - Real.sqrt ((d-1:ℕ):ℝ) * 2
      = 2 * (Real.sqrt (d:ℝ) - Real.sqrt ((d-1:ℕ):ℝ)) by ring, hkey]
  rw [le_div_iff₀ hden]
  have hx : (0:ℝ) < Real.sqrt (d:ℝ) + Real.sqrt ((d-1:ℕ):ℝ) := by positivity
  have h6 : 2 * (1 / (Real.sqrt (d:ℝ) + Real.sqrt ((d-1:ℕ):ℝ)))
      = 2 / (Real.sqrt (d:ℝ) + Real.sqrt ((d-1:ℕ):ℝ)) := by ring
  rw [h6, le_div_iff₀ hx]
  have h7 : 1 / ((d:ℝ)*Real.sqrt d) * (Real.sqrt ((d-1:ℕ):ℝ) * Real.sqrt (d:ℝ))
        * (Real.sqrt (d:ℝ) + Real.sqrt ((d-1:ℕ):ℝ))
      = Real.sqrt ((d-1:ℕ):ℝ) * (Real.sqrt (d:ℝ) + Real.sqrt ((d-1:ℕ):ℝ)) / (d:ℝ) := by
    field_simp
  rw [h7, div_le_iff₀ hdp]
  linarith [h2]

/-- The telescoping estimate `Σ_{d≤T} 1/(d√d) ≤ 3`. -/
lemma s3Tsum_inv_pow (T : ℕ) : (∑ d ∈ Finset.Icc 1 T, 1/((d:ℝ)*Real.sqrt d)) ≤ 3 := by
  rcases T with _ | T
  · simp
  · have hsplit : (∑ d ∈ Finset.Icc 1 (T+1), 1/((d:ℝ)*Real.sqrt d))
        = 1 + ∑ d ∈ Finset.Icc 2 (T+1), 1/((d:ℝ)*Real.sqrt d) := by
      have hset : Finset.Icc 1 (T+1) = insert 1 (Finset.Icc 2 (T+1)) := by
        ext x
        constructor
        · intro hx
          rw [Finset.mem_Icc] at hx
          rcases eq_or_lt_of_le hx.1 with h | h
          · exact Finset.mem_insert.mpr (Or.inl h.symm)
          · exact Finset.mem_insert.mpr (Or.inr (Finset.mem_Icc.mpr ⟨by omega, hx.2⟩))
        · intro hx
          rw [Finset.mem_insert] at hx
          rw [Finset.mem_Icc]
          rcases hx with h | h
          · rw [h]; omega
          · rw [Finset.mem_Icc] at h; omega
      rw [hset, Finset.sum_insert (by simp [Finset.mem_Icc])]
      norm_num
    rw [hsplit]
    have hstep : (∑ d ∈ Finset.Icc 2 (T+1), 1/((d:ℝ)*Real.sqrt d))
        ≤ ∑ d ∈ Finset.Icc 2 (T+1), (2/Real.sqrt ((d-1:ℕ):ℝ) - 2/Real.sqrt (d:ℝ)) :=
      Finset.sum_le_sum (fun d hd => s3Tsum_rpow d (Finset.mem_Icc.mp hd).1)
    have htel : (∑ d ∈ Finset.Icc 2 (T+1), (2/Real.sqrt ((d-1:ℕ):ℝ) - 2/Real.sqrt (d:ℝ)))
        = 2 - 2/Real.sqrt ((T+1:ℕ):ℝ) := by
      rw [show (∑ d ∈ Finset.Icc 2 (T+1), (2/Real.sqrt ((d-1:ℕ):ℝ) - 2/Real.sqrt (d:ℝ)))
          = ∑ i ∈ Finset.Icc 1 T, (2/Real.sqrt (i:ℝ) - 2/Real.sqrt ((i+1:ℕ):ℝ)) from by
            apply Finset.sum_bij (fun d _ => d - 1)
            · intro d hd; rw [Finset.mem_Icc] at hd ⊢; omega
            · intro d1 hd1 d2 hd2 heq
              rw [Finset.mem_Icc] at hd1 hd2; omega
            · intro i hi
              exact ⟨i+1, by rw [Finset.mem_Icc] at hi ⊢; omega, by omega⟩
            · intro d hd
              rw [Finset.mem_Icc] at hd
              show 2/Real.sqrt ((d-1:ℕ):ℝ) - 2/Real.sqrt (d:ℝ)
                = 2/Real.sqrt ((d-1:ℕ):ℝ) - 2/Real.sqrt (((d-1)+1:ℕ):ℝ)
              rw [show d - 1 + 1 = d from by omega]]
      rw [show (∑ i ∈ Finset.Icc 1 T, (2/Real.sqrt (i:ℝ) - 2/Real.sqrt ((i+1:ℕ):ℝ)))
          = - ∑ i ∈ Finset.Icc 1 T, (2/Real.sqrt ((i+1:ℕ):ℝ) - 2/Real.sqrt (i:ℝ)) from by
            rw [← Finset.sum_neg_distrib]; apply Finset.sum_congr rfl; intro i _; ring]
      rcases Nat.eq_zero_or_pos T with hT | hT
      · subst hT; simp
      · rw [Finset.sum_Icc_sub hT (fun i : ℕ => 2/Real.sqrt (i:ℝ))]
        ring
    have h2 : (0:ℝ) ≤ 2/Real.sqrt ((T+1:ℕ):ℝ) := by positivity
    linarith [hstep, htel, h2]

theorem S3TsumBounds2 :
    (∃ C : ℝ, 0 < C ∧ ∀ T : ℕ,
        (∑ t ∈ Finset.Icc 1 T, |(ArithmeticFunction.moebius t : ℝ)|
            * ((t : ℝ) / Work.ZeroDensity.Jutila.kap t)
            * (∑ d ∈ t.divisors, 1 / Real.sqrt (d : ℝ))) ≤ C * (T : ℝ))
    ∧ (∃ C : ℝ, 0 < C ∧ ∀ T : ℕ,
        (∑ t ∈ Finset.Icc 1 T, |(ArithmeticFunction.moebius t : ℝ)|
            * (∑ d ∈ t.divisors, 1 / Real.sqrt (d : ℝ)) / Work.ZeroDensity.Jutila.kap t)
          ≤ C * Real.log ((T : ℝ) + 2)) := by
  constructor
  · refine ⟨4, by norm_num, ?_⟩
    intro T
    calc (∑ t ∈ Finset.Icc 1 T, |(ArithmeticFunction.moebius t : ℝ)|
            * ((t : ℝ) / Work.ZeroDensity.Jutila.kap t)
            * (∑ d ∈ t.divisors, 1 / Real.sqrt (d : ℝ)))
        ≤ ∑ t ∈ Finset.Icc 1 T, |(ArithmeticFunction.moebius t : ℝ)|
            * (∑ d ∈ t.divisors, 1 / Real.sqrt (d : ℝ)) :=
          Finset.sum_le_sum (fun t _ => s3Tsum_pointwise t)
      _ = ∑ t ∈ Finset.Icc 1 T, ∑ d ∈ t.divisors,
            |(ArithmeticFunction.moebius t : ℝ)| * (1 / Real.sqrt (d : ℝ)) := by
          apply Finset.sum_congr rfl; intro t ht; rw [Finset.mul_sum]
      _ ≤ ∑ t ∈ Finset.Icc 1 T, ∑ d ∈ Finset.Icc 1 T,
            (if d ∣ t then |(ArithmeticFunction.moebius t : ℝ)| * (1 / Real.sqrt (d : ℝ)) else 0) := by
          apply Finset.sum_le_sum; intro t ht
          rw [Finset.mem_Icc] at ht
          rw [show (∑ d ∈ t.divisors, |(ArithmeticFunction.moebius t : ℝ)| * (1 / Real.sqrt (d : ℝ)))
              = ∑ d ∈ t.divisors,
                  (if d ∣ t then |(ArithmeticFunction.moebius t : ℝ)| * (1 / Real.sqrt (d : ℝ)) else 0) from
              Finset.sum_congr rfl (fun d hd => by rw [if_pos (Nat.dvd_of_mem_divisors hd)])]
          refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
          · intro d hd
            rw [Finset.mem_Icc]
            exact ⟨Nat.pos_of_mem_divisors hd, le_trans (Nat.divisor_le hd) ht.2⟩
          · intro d hd hnd
            by_cases h : d ∣ t
            · rw [if_pos h]; positivity
            · rw [if_neg h]
      _ = ∑ d ∈ Finset.Icc 1 T, ∑ t ∈ Finset.Icc 1 T,
            (if d ∣ t then |(ArithmeticFunction.moebius t : ℝ)| * (1 / Real.sqrt (d : ℝ)) else 0) :=
          Finset.sum_comm
      _ ≤ ∑ d ∈ Finset.Icc 1 T, (1 / Real.sqrt (d : ℝ)) * ((T / d : ℕ) : ℝ) := by
          apply Finset.sum_le_sum; intro d hd
          have h1 : (∑ t ∈ Finset.Icc 1 T,
                (if d ∣ t then |(ArithmeticFunction.moebius t : ℝ)| * (1 / Real.sqrt (d : ℝ)) else 0))
              ≤ ∑ t ∈ Finset.Icc 1 T, (if d ∣ t then (1 / Real.sqrt (d : ℝ)) else 0) := by
            apply Finset.sum_le_sum; intro t ht
            by_cases h : d ∣ t
            · rw [if_pos h, if_pos h]
              have hm : |(ArithmeticFunction.moebius t : ℝ)| ≤ 1 := by
                have := ArithmeticFunction.abs_moebius_le_one (n := t)
                exact_mod_cast this
              nlinarith [show (0:ℝ) ≤ 1 / Real.sqrt (d : ℝ) by positivity,
                abs_nonneg (ArithmeticFunction.moebius t : ℝ)]
            · rw [if_neg h, if_neg h]
          refine le_trans h1 ?_
          rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
          rw [mul_comm]
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          exact_mod_cast s3Tsum_card_le T d
      _ ≤ ∑ d ∈ Finset.Icc 1 T, (1 / Real.sqrt (d : ℝ)) * ((T : ℝ) / (d : ℝ)) := by
          apply Finset.sum_le_sum; intro d hd
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          simpa [Nat.cast_mul] using Nat.cast_div_le (α := ℝ) (m := T) (n := d)
      _ = (T : ℝ) * (∑ d ∈ Finset.Icc 1 T, 1 / ((d : ℝ) * Real.sqrt (d : ℝ))) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl; intro d hd
          have hd0 : (d : ℝ) ≠ 0 := by
            have : 1 ≤ d := (Finset.mem_Icc.mp hd).1
            positivity
          field_simp
      _ ≤ (T : ℝ) * 3 := mul_le_mul_of_nonneg_left (s3Tsum_inv_pow T) (by positivity)
      _ ≤ 4 * (T : ℝ) := by nlinarith [show (0:ℝ) ≤ (T : ℝ) by positivity]
  · -- second conjunct
    refine ⟨12, by norm_num, ?_⟩
    intro T
    calc (∑ t ∈ Finset.Icc 1 T, |(ArithmeticFunction.moebius t : ℝ)|
            * (∑ d ∈ t.divisors, 1 / Real.sqrt (d : ℝ)) / Work.ZeroDensity.Jutila.kap t)
        ≤ ∑ t ∈ Finset.Icc 1 T, (1/(t:ℝ))
            * (∑ d ∈ t.divisors, 1 / Real.sqrt (d : ℝ)) := by
          apply Finset.sum_le_sum; intro t ht
          rcases Nat.eq_zero_or_pos t with h0 | h0
          · subst h0
            simp [Work.ZeroDensity.Jutila.kap]
          · by_cases hsf : Squarefree t
            · have hk := s3Tsum_div_kap_le_one t hsf
              have hσ : (0:ℝ) ≤ ∑ d ∈ t.divisors, 1 / Real.sqrt (d : ℝ) :=
                Finset.sum_nonneg (fun d _ => by positivity)
              have hkey : (|(ArithmeticFunction.moebius t : ℝ)|
                    * (∑ d ∈ t.divisors, 1 / Real.sqrt (d : ℝ))) / Work.ZeroDensity.Jutila.kap t
                  = |(ArithmeticFunction.moebius t : ℝ)|
                    * ((1/(t:ℝ)) * (((t:ℝ)/Work.ZeroDensity.Jutila.kap t)
                      * (∑ d ∈ t.divisors, 1 / Real.sqrt (d : ℝ)))) := by
                field_simp
              rw [hkey]
              have h3 : ((t:ℝ)/Work.ZeroDensity.Jutila.kap t)
                  * (∑ d ∈ t.divisors, 1 / Real.sqrt (d : ℝ))
                  ≤ 1 * (∑ d ∈ t.divisors, 1 / Real.sqrt (d : ℝ)) :=
                mul_le_mul_of_nonneg_right hk hσ
              calc |(ArithmeticFunction.moebius t : ℝ)|
                    * ((1/(t:ℝ)) * (((t:ℝ)/Work.ZeroDensity.Jutila.kap t)
                      * (∑ d ∈ t.divisors, 1 / Real.sqrt (d : ℝ))))
                  ≤ |(ArithmeticFunction.moebius t : ℝ)|
                    * ((1/(t:ℝ)) * (1 * (∑ d ∈ t.divisors, 1 / Real.sqrt (d : ℝ)))) := by
                    apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
                    exact mul_le_mul_of_nonneg_left h3 (by positivity)
                _ ≤ 1 * ((1/(t:ℝ)) * (1 * (∑ d ∈ t.divisors, 1 / Real.sqrt (d : ℝ)))) := by
                    apply mul_le_mul_of_nonneg_right _ (by positivity)
                    have := ArithmeticFunction.abs_moebius_le_one (n := t)
                    exact_mod_cast this
                _ = (1/(t:ℝ)) * (∑ d ∈ t.divisors, 1 / Real.sqrt (d : ℝ)) := by ring
            · have hm : (ArithmeticFunction.moebius t : ℝ) = 0 := by
                rw [ArithmeticFunction.moebius_eq_zero_of_not_squarefree hsf]; simp
              rw [hm]
              simp only [abs_zero, zero_mul, zero_div]
              positivity
      _ = ∑ t ∈ Finset.Icc 1 T, ∑ d ∈ t.divisors,
            (1/(t:ℝ)) * (1 / Real.sqrt (d : ℝ)) := by
          apply Finset.sum_congr rfl; intro t ht
          rw [Finset.mul_sum]
      _ ≤ ∑ t ∈ Finset.Icc 1 T, ∑ d ∈ Finset.Icc 1 T,
            (if d ∣ t then (1/(t:ℝ)) * (1 / Real.sqrt (d : ℝ)) else 0) := by
          apply Finset.sum_le_sum; intro t ht
          rw [Finset.mem_Icc] at ht
          rw [show (∑ d ∈ t.divisors, (1/(t:ℝ)) * (1 / Real.sqrt (d : ℝ)))
              = ∑ d ∈ t.divisors,
                  (if d ∣ t then (1/(t:ℝ)) * (1 / Real.sqrt (d : ℝ)) else 0) from
              Finset.sum_congr rfl (fun d hd => by rw [if_pos (Nat.dvd_of_mem_divisors hd)])]
          refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
          · intro d hd
            rw [Finset.mem_Icc]
            exact ⟨Nat.pos_of_mem_divisors hd, le_trans (Nat.divisor_le hd) ht.2⟩
          · intro d hd hnd
            by_cases h : d ∣ t
            · rw [if_pos h]; positivity
            · rw [if_neg h]
      _ = ∑ d ∈ Finset.Icc 1 T, ∑ t ∈ Finset.Icc 1 T,
            (if d ∣ t then (1/(t:ℝ)) * (1 / Real.sqrt (d : ℝ)) else 0) :=
          Finset.sum_comm
      _ ≤ ∑ d ∈ Finset.Icc 1 T, (1 / Real.sqrt (d : ℝ))
            * ((1/(d:ℝ)) * (1 + Real.log ((T:ℝ) + 2))) := by
          apply Finset.sum_le_sum; intro d hd
          have hdT : 1 ≤ d := (Finset.mem_Icc.mp hd).1
          have hd0 : (0:ℝ) < (d:ℝ) := by positivity
          rw [← Finset.sum_filter]
          rw [← Finset.sum_mul, mul_comm]
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          have hreindex : (∑ t ∈ (Finset.Icc 1 T).filter (fun t => d ∣ t), (1:ℝ)/(t:ℝ))
              ≤ (1/(d:ℝ)) * (∑ m ∈ Finset.Icc 1 (T/d), (1:ℝ)/(m:ℝ)) := by
            have h1 : (∑ t ∈ (Finset.Icc 1 T).filter (fun t => d ∣ t), (1:ℝ)/(t:ℝ))
                = ∑ t ∈ (Finset.Icc 1 T).filter (fun t => d ∣ t),
                    (1/(d:ℝ)) * (1/((t/d:ℕ):ℝ)) := by
              apply Finset.sum_congr rfl; intro t ht
              rw [Finset.mem_filter, Finset.mem_Icc] at ht
              have h2 : d * (t/d) = t := Nat.mul_div_cancel' ht.2
              have h3 : (t:ℝ) = (d:ℝ) * ((t/d:ℕ):ℝ) := by
                rw [← Nat.cast_mul, h2]
              have h5 : ((t/d:ℕ):ℝ) ≠ 0 := by
                have h6 : 0 < t/d := Nat.div_pos (Nat.le_of_dvd (by omega) ht.2) (by omega)
                positivity
              rw [h3]
              field_simp
            rw [h1, ← Finset.mul_sum]
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            have hinj : ∀ a ∈ (Finset.Icc 1 T).filter (fun t => d ∣ t),
                ∀ b ∈ (Finset.Icc 1 T).filter (fun t => d ∣ t), a/d = b/d → a = b := by
              intro a ha b hb hab
              rw [Finset.mem_filter] at ha hb
              have h2 : d * (a/d) = a := Nat.mul_div_cancel' ha.2
              have h3 : d * (b/d) = b := Nat.mul_div_cancel' hb.2
              rw [hab, h3] at h2
              exact h2.symm
            have himg : (∑ t ∈ (Finset.Icc 1 T).filter (fun t => d ∣ t), (1:ℝ)/((t/d:ℕ):ℝ))
                = ∑ m ∈ ((Finset.Icc 1 T).filter (fun t => d ∣ t)).image (fun t => t/d),
                    (1:ℝ)/(m:ℝ) := by
              refine Finset.sum_bij (fun t _ => t/d) ?_ ?_ ?_ ?_
              · intro t ht
                exact Finset.mem_image.mpr ⟨t, ht, rfl⟩
              · intro a ha b hb hab
                exact hinj a ha b hb hab
              · intro m hm
                rw [Finset.mem_image] at hm
                obtain ⟨t, ht, htm⟩ := hm
                exact ⟨t, ht, htm⟩
              · intro t ht
                rfl
            rw [himg]
            apply Finset.sum_le_sum_of_subset_of_nonneg
            · intro m hm
              rw [Finset.mem_image] at hm
              obtain ⟨t, ht, htm⟩ := hm
              rw [← htm]
              rw [Finset.mem_filter, Finset.mem_Icc] at ht
              rw [Finset.mem_Icc]
              exact ⟨Nat.div_pos (Nat.le_of_dvd (by omega) ht.2) (by omega),
                Nat.div_le_div_right ht.1.2⟩
            · intro m hm _
              positivity
          refine le_trans hreindex ?_
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          refine le_trans (HarmonicLogBound (T/d)) ?_
          have h2 : Real.log (((T/d:ℕ)):ℝ) ≤ Real.log ((T:ℝ)+2) := by
            rcases Nat.eq_zero_or_pos (T/d) with h | h
            · rw [h]
              simp only [Nat.cast_zero, Real.log_zero]
              exact Real.log_nonneg (by linarith [show (0:ℝ) ≤ (T:ℝ) by positivity])
            · apply Real.log_le_log
              · positivity
              · have h3 : T/d ≤ T := Nat.div_le_self T d
                push_cast
                linarith [show ((T/d:ℕ):ℝ) ≤ (T:ℝ) by exact_mod_cast h3]
          linarith
      _ = (1 + Real.log ((T:ℝ) + 2)) * (∑ d ∈ Finset.Icc 1 T, 1/((d:ℝ) * Real.sqrt (d:ℝ))) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl; intro d hd
          have hd0 : (d:ℝ) ≠ 0 := by
            have : 1 ≤ d := (Finset.mem_Icc.mp hd).1
            positivity
          have h1 : 1 / Real.sqrt (d:ℝ) * (1/(d:ℝ)) = 1/((d:ℝ) * Real.sqrt (d:ℝ)) := by
            field_simp
          rw [← h1]; ring
      _ ≤ (1 + Real.log ((T:ℝ) + 2)) * 3 := by
          apply mul_le_mul_of_nonneg_left (s3Tsum_inv_pow T)
          have h1 : (0:ℝ) ≤ (T:ℝ) := by positivity
          have h2 : (1:ℝ) ≤ (T:ℝ)+2 := by linarith
          have h3 : (0:ℝ) ≤ Real.log ((T:ℝ)+2) := Real.log_nonneg h2
          linarith
      _ ≤ 12 * Real.log ((T:ℝ) + 2) := by
          have h1 : (0:ℝ) ≤ (T:ℝ) := by positivity
          have h2 : (1:ℝ) ≤ (T:ℝ)+2 := by linarith
          have h3 : (0:ℝ) ≤ Real.log ((T:ℝ)+2) := Real.log_nonneg h2
          have h4 : (1:ℝ)/3 ≤ Real.log ((T:ℝ)+2) := by
            have h5 : Real.log (2:ℝ) ≤ Real.log ((T:ℝ)+2) := Real.log_le_log (by norm_num) (by linarith)
            have h6 : (1:ℝ)/3 ≤ Real.log 2 := by
              have h7 := Real.one_sub_inv_le_log_of_pos (show (0:ℝ) < 2 by norm_num)
              norm_num at h7
              linarith
            linarith
          nlinarith [h3, h4]

end Work.LinnikAreas.JutilaPieces
