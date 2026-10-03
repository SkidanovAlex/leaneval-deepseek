import Mathlib
import Submission.Work.KMTAreas.A7.LargeInterface
import Submission.Work.A7.Pev.PevalR_deriv_bounds

namespace Work.KMTAreas.A7

/-- The evaluation of an integer polynomial at `N * t` (`|t| ≤ 1`) is bounded by the `ℓ¹`-norm of
its coefficients times `(1 + N) ^ natDegree`.  `PevalR P x = (P.map (Int.castRingHom ℝ)).eval x`, so
the already-proved `Work.A7.Pev.abs_eval_le_coeff_sum_mul_max` applied to
`Q = P.map (Int.castRingHom ℝ)` and `x = N * t` gives
`|PevalR P (N*t)| ≤ (∑ i, |Q.coeff i|) * (max 1 |N*t|)^Q.natDegree`
(`Polynomial.coeff_map`, so `Q.coeff i = (P.coeff i : ℝ)`), and `max 1 |N*t| ≤ 1 + N` because
`|N*t| = N * |t| ≤ N` under `|t| ≤ 1`; finally `Q.natDegree ≤ P.natDegree`
(`Polynomial.natDegree_map_le`) enlarges the range `range (Q.natDegree + 1) ⊆ range (P.natDegree + 1)`
and the exponent. -/
theorem abs_PevalR_mul_le (P : Polynomial ℤ) (N : ℕ) {t : ℝ} (ht : |t| ≤ 1) :
    |Work.KMTAreas.A7.PevalR P ((N : ℝ) * t)|
      ≤ (∑ i ∈ Finset.range (P.natDegree + 1), |(P.coeff i : ℝ)|) *
          (1 + (N : ℝ)) ^ P.natDegree := by
  classical
  set Q : Polynomial ℝ := P.map (Int.castRingHom ℝ) with hQ
  have hcoeff : ∀ i, Q.coeff i = (P.coeff i : ℝ) := by
    intro i
    rw [hQ, Polynomial.coeff_map]
    rfl
  have heval : Work.KMTAreas.A7.PevalR P ((N : ℝ) * t) = Q.eval ((N : ℝ) * t) := by
    rw [hQ]; rfl
  rw [heval]
  have hmain := Work.A7.Pev.abs_eval_le_coeff_sum_mul_max Q ((N : ℝ) * t)
  have hdeg : Q.natDegree ≤ P.natDegree := by
    rw [hQ]; exact Polynomial.natDegree_map_le
  have hsum : (∑ i ∈ Finset.range (Q.natDegree + 1), |Q.coeff i|)
      ≤ ∑ i ∈ Finset.range (P.natDegree + 1), |(P.coeff i : ℝ)| := by
    calc (∑ i ∈ Finset.range (Q.natDegree + 1), |Q.coeff i|)
        = ∑ i ∈ Finset.range (Q.natDegree + 1), |(P.coeff i : ℝ)| :=
          Finset.sum_congr rfl (fun i _ => by rw [hcoeff])
      _ ≤ ∑ i ∈ Finset.range (P.natDegree + 1), |(P.coeff i : ℝ)| :=
          Finset.sum_le_sum_of_subset_of_nonneg
            (Finset.range_subset.mpr
              (fun i hi => Finset.mem_range.mpr
                (lt_of_lt_of_le hi (Nat.succ_le_succ hdeg))))
            (fun i _ _ => abs_nonneg _)
  have hx : |(N : ℝ) * t| ≤ 1 + (N : ℝ) := by
    have h1 : |(N : ℝ) * t| ≤ (N : ℝ) := by
      rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg N)]
      calc (N : ℝ) * |t| ≤ (N : ℝ) * 1 := mul_le_mul_of_nonneg_left ht (Nat.cast_nonneg N)
        _ = (N : ℝ) := mul_one _
    have h2 : (1 : ℝ) ≤ 1 + (N : ℝ) := le_add_of_nonneg_right (Nat.cast_nonneg N)
    linarith
  have hpow : (max 1 |(N : ℝ) * t|) ^ Q.natDegree ≤ (1 + (N : ℝ)) ^ P.natDegree := by
    have hmax : max 1 |(N : ℝ) * t| ≤ 1 + (N : ℝ) := max_le (by linarith) hx
    refine (pow_le_pow_left₀ (by positivity) hmax Q.natDegree).trans ?_
    exact pow_le_pow_right₀ (le_add_of_nonneg_right (Nat.cast_nonneg N)) hdeg
  calc |Q.eval ((N : ℝ) * t)|
      ≤ (∑ i ∈ Finset.range (Q.natDegree + 1), |Q.coeff i|) *
          (max 1 |(N : ℝ) * t|) ^ Q.natDegree := hmain
    _ ≤ (∑ i ∈ Finset.range (P.natDegree + 1), |(P.coeff i : ℝ)|) *
          (1 + (N : ℝ)) ^ P.natDegree :=
          mul_le_mul hsum hpow (by positivity) (Finset.sum_nonneg (fun i _ => abs_nonneg _))

end Work.KMTAreas.A7
