import Mathlib
import Submission.Commons.NumberTheory.BombieriVinogradov.bilinear_char_large_sieve_twisted

namespace Commons.NumberTheory.BombieriVinogradov

open scoped BigOperators

noncomputable section

open Classical

/-- Splitting the complex power `m ^ (-(c + i t))` as the real weight `m ^ (-c)` times the
unitary twist `exp (-i t log m)`, for `m ≥ 1`. -/
lemma twist_cpow_neg_add_mul_I (m : ℕ) (hm : 1 ≤ m) (c t : ℝ) :
    (m : ℂ) ^ (-((c : ℂ) + (t : ℂ) * Complex.I))
      = (m : ℂ) ^ (-(c : ℂ)) * Complex.exp ((Real.log (m : ℝ) * (-t)) * Complex.I) := by
  have hmpos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hm0 : (m : ℂ) ≠ 0 := by
    rw [← Complex.ofReal_natCast m]
    exact Complex.ofReal_ne_zero.mpr (ne_of_gt hmpos)
  have hsplit : -((c : ℂ) + (t : ℂ) * Complex.I) = -(c : ℂ) + (-(t : ℂ) * Complex.I) := by ring
  rw [hsplit, Complex.cpow_add (-(c : ℂ)) (-(t : ℂ) * Complex.I) hm0]
  congr 1
  rw [Complex.cpow_def_of_ne_zero hm0, ← Complex.ofReal_natCast m,
    ← Complex.ofReal_log (le_of_lt hmpos)]
  congr 1
  push_cast
  ring

/-- The real weight `m ^ (-c)` has modulus at most `1` for `m ≥ 1` and `c ≥ 0`. -/
lemma norm_cpow_neg_le_one_nat (m : ℕ) (hm : 1 ≤ m) (c : ℝ) (hc : 0 ≤ c) :
    ‖(m : ℂ) ^ (-(c : ℂ))‖ ≤ 1 := by
  have hmpos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hnorm : ‖(m : ℂ) ^ (-(c : ℂ))‖ = (m : ℝ) ^ (-c) := by
    rw [← Complex.ofReal_natCast m,
      Complex.norm_cpow_eq_rpow_re_of_pos (x := (m : ℝ)) hmpos (-(c : ℂ))]
    have : (-(c : ℂ)).re = -c := by simp
    rw [this]
  rw [hnorm]
  exact Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast hm) (by linarith)

theorem char_large_sieve_twisted_rpow (Q M N : ℕ) (hQ : 1 ≤ Q) (c : ℝ) (hc : 0 < c)
    (a b : ℕ → ℂ) (t : ℝ) :
    (∑ q ∈ Finset.Icc 1 Q, ((q : ℝ) / (q.totient : ℝ)) *
        ∑ χ ∈ (@Finset.filter (DirichletCharacter ℂ q) (fun χ => χ.IsPrimitive)
                (Classical.decPred _) Finset.univ),
          ‖(∑ m ∈ Finset.Icc 1 M, a m * χ (m : ZMod q) * ((m : ℂ)) ^ (-((c : ℂ) + (t : ℂ) * Complex.I))) *
           (∑ n ∈ Finset.Icc 1 N, b n * χ (n : ZMod q) * ((n : ℂ)) ^ (-((c : ℂ) + (t : ℂ) * Complex.I)))‖)
      ≤ Real.sqrt (((M : ℝ) + (Q : ℝ) ^ 2) * ∑ m ∈ Finset.Icc 1 M, ‖a m‖ ^ 2) *
        Real.sqrt (((N : ℝ) + (Q : ℝ) ^ 2) * ∑ n ∈ Finset.Icc 1 N, ‖b n‖ ^ 2) := by
  classical
  set A : ℕ → ℂ := fun m => a m * (m : ℂ) ^ (-(c : ℂ)) with hA
  set B : ℕ → ℂ := fun n => b n * (n : ℂ) ^ (-(c : ℂ)) with hB
  -- Norm bounds on the twisted coefficients.
  have hsumA : (∑ m ∈ Finset.Icc 1 M, ‖A m‖ ^ 2) ≤ ∑ m ∈ Finset.Icc 1 M, ‖a m‖ ^ 2 := by
    refine Finset.sum_le_sum (fun m hm => ?_)
    have hm1 : 1 ≤ m := (Finset.mem_Icc.mp hm).1
    have hle : ‖A m‖ ≤ ‖a m‖ := by
      rw [hA, norm_mul]
      calc ‖a m‖ * ‖(m : ℂ) ^ (-(c : ℂ))‖ ≤ ‖a m‖ * 1 :=
            mul_le_mul_of_nonneg_left
              (norm_cpow_neg_le_one_nat m hm1 c (le_of_lt hc)) (norm_nonneg _)
        _ = ‖a m‖ := mul_one _
    exact pow_le_pow_left₀ (norm_nonneg _) hle 2
  have hsumB : (∑ n ∈ Finset.Icc 1 N, ‖B n‖ ^ 2) ≤ ∑ n ∈ Finset.Icc 1 N, ‖b n‖ ^ 2 := by
    refine Finset.sum_le_sum (fun n hn => ?_)
    have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
    have hle : ‖B n‖ ≤ ‖b n‖ := by
      rw [hB, norm_mul]
      calc ‖b n‖ * ‖(n : ℂ) ^ (-(c : ℂ))‖ ≤ ‖b n‖ * 1 :=
            mul_le_mul_of_nonneg_left
              (norm_cpow_neg_le_one_nat n hn1 c (le_of_lt hc)) (norm_nonneg _)
        _ = ‖b n‖ := mul_one _
    exact pow_le_pow_left₀ (norm_nonneg _) hle 2
  -- The twisted bilinear large sieve, applied to `A`, `B`.
  have hmain := bilinear_char_large_sieve_twisted Q M N hQ A B t
  have hmain' : (∑ q ∈ Finset.Icc 1 Q, ((q : ℝ) / (q.totient : ℝ)) *
        ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ q)).filter (fun χ => χ.IsPrimitive),
          ‖(∑ m ∈ Finset.Icc 1 M, A m * Complex.exp ((Real.log (m : ℝ) * (-t)) * Complex.I) *
              χ ((m : ℕ) : ZMod q)) *
           (∑ n ∈ Finset.Icc 1 N, B n * Complex.exp ((Real.log (n : ℝ) * (-t)) * Complex.I) *
              χ ((n : ℕ) : ZMod q))‖)
      ≤ Real.sqrt (((M : ℝ) + (Q : ℝ) ^ 2) * ∑ m ∈ Finset.Icc 1 M, ‖A m‖ ^ 2) *
        Real.sqrt (((N : ℝ) + (Q : ℝ) ^ 2) * ∑ n ∈ Finset.Icc 1 N, ‖B n‖ ^ 2) := by
    exact hmain
  -- Rewrite the left-hand side into the twisted form.
  have hLHS : (∑ q ∈ Finset.Icc 1 Q, ((q : ℝ) / (q.totient : ℝ)) *
        ∑ χ ∈ (@Finset.filter (DirichletCharacter ℂ q) (fun χ => χ.IsPrimitive)
                (Classical.decPred _) Finset.univ),
          ‖(∑ m ∈ Finset.Icc 1 M, a m * χ (m : ZMod q) *
              ((m : ℂ)) ^ (-((c : ℂ) + (t : ℂ) * Complex.I))) *
           (∑ n ∈ Finset.Icc 1 N, b n * χ (n : ZMod q) *
              ((n : ℂ)) ^ (-((c : ℂ) + (t : ℂ) * Complex.I)))‖)
      = (∑ q ∈ Finset.Icc 1 Q, ((q : ℝ) / (q.totient : ℝ)) *
        ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ q)).filter (fun χ => χ.IsPrimitive),
          ‖(∑ m ∈ Finset.Icc 1 M, A m * Complex.exp ((Real.log (m : ℝ) * (-t)) * Complex.I) *
              χ ((m : ℕ) : ZMod q)) *
           (∑ n ∈ Finset.Icc 1 N, B n * Complex.exp ((Real.log (n : ℝ) * (-t)) * Complex.I) *
              χ ((n : ℕ) : ZMod q))‖) := by
    refine Finset.sum_congr rfl (fun q hq => ?_)
    congr 1
    refine Finset.sum_congr ?_ (fun χ hχ => ?_)
    · exact Finset.filter_congr_decidable _ _ _
    · have hsum1 : (∑ m ∈ Finset.Icc 1 M, a m * χ (m : ZMod q) *
              ((m : ℂ)) ^ (-((c : ℂ) + (t : ℂ) * Complex.I)))
          = ∑ m ∈ Finset.Icc 1 M, A m * Complex.exp ((Real.log (m : ℝ) * (-t)) * Complex.I) *
              χ (m : ZMod q) := by
        refine Finset.sum_congr rfl (fun m hm => ?_)
        have hm1 : 1 ≤ m := (Finset.mem_Icc.mp hm).1
        rw [hA, twist_cpow_neg_add_mul_I m hm1 c t]
        ring
      have hsum2 : (∑ n ∈ Finset.Icc 1 N, b n * χ (n : ZMod q) *
              ((n : ℂ)) ^ (-((c : ℂ) + (t : ℂ) * Complex.I)))
          = ∑ n ∈ Finset.Icc 1 N, B n * Complex.exp ((Real.log (n : ℝ) * (-t)) * Complex.I) *
              χ (n : ZMod q) := by
        refine Finset.sum_congr rfl (fun n hn => ?_)
        have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
        rw [hB, twist_cpow_neg_add_mul_I n hn1 c t]
        ring
      rw [hsum1, hsum2]
  -- Final comparison of the two right-hand sides.
  have hfinal : Real.sqrt (((M : ℝ) + (Q : ℝ) ^ 2) * ∑ m ∈ Finset.Icc 1 M, ‖A m‖ ^ 2) *
        Real.sqrt (((N : ℝ) + (Q : ℝ) ^ 2) * ∑ n ∈ Finset.Icc 1 N, ‖B n‖ ^ 2)
      ≤ Real.sqrt (((M : ℝ) + (Q : ℝ) ^ 2) * ∑ m ∈ Finset.Icc 1 M, ‖a m‖ ^ 2) *
        Real.sqrt (((N : ℝ) + (Q : ℝ) ^ 2) * ∑ n ∈ Finset.Icc 1 N, ‖b n‖ ^ 2) := by
    apply mul_le_mul
    · apply Real.sqrt_le_sqrt
      exact mul_le_mul_of_nonneg_left hsumA (by positivity)
    · apply Real.sqrt_le_sqrt
      exact mul_le_mul_of_nonneg_left hsumB (by positivity)
    · positivity
    · positivity
  rw [hLHS]
  exact le_trans hmain' hfinal

end

end Commons.NumberTheory.BombieriVinogradov
