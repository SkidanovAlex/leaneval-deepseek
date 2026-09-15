import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.MeanInequalities

namespace Commons.Analysis.Inequalities

open scoped BigOperators

/-- Auxiliary `Fin k`-indexed AM-GM inequality: for nonnegative reals `a j` and `1 ≤ k`,
`∏ j, a j ≤ k⁻¹ * ∑ j, (a j)^k`. -/
lemma prod_le_inv_mul_sum_pow {k : ℕ} (hk : 1 ≤ k) (a : Fin k → ℝ) (ha : ∀ j, 0 ≤ a j) :
    ∏ j : Fin k, a j ≤ ((k : ℝ)⁻¹) * ∑ j : Fin k, (a j) ^ k := by
  have hk0 : (k : ℝ) ≠ 0 := by exact_mod_cast (by omega : k ≠ 0)
  have hw : ∀ j ∈ (Finset.univ : Finset (Fin k)), 0 ≤ ((k : ℝ)⁻¹) := fun _ _ => by positivity
  have hw' : ∑ j : Fin k, ((k : ℝ)⁻¹) = 1 := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
    simp only [nsmul_eq_mul]
    field_simp
  have hz : ∀ j ∈ (Finset.univ : Finset (Fin k)), 0 ≤ (a j) ^ k :=
    fun j _ => pow_nonneg (ha j) k
  have h := Real.geom_mean_le_arith_mean_weighted (Finset.univ : Finset (Fin k))
      (fun _ => (k : ℝ)⁻¹) (fun j => (a j) ^ k) hw hw' hz
  calc ∏ j : Fin k, a j
      = ∏ j : Fin k, ((a j) ^ k) ^ ((k : ℝ)⁻¹) := by
        refine Finset.prod_congr rfl fun j _ => ?_
        rw [← Real.rpow_natCast, ← Real.rpow_mul (ha j), mul_inv_cancel₀ hk0, Real.rpow_one]
    _ ≤ ∑ j : Fin k, ((k : ℝ)⁻¹) * (a j) ^ k := h
    _ = ((k : ℝ)⁻¹) * ∑ j : Fin k, (a j) ^ k := by rw [Finset.mul_sum]

/-- Generalized Hölder inequality for a finite product of `k` nonnegative real functions with
exponent `k`: `∑_i ∏_j g_j(i) ≤ ∏_j (∑_i g_j(i)^k)^(1/k)`. -/
theorem holder_prod {k : ℕ} (hk : 1 ≤ k) {ι : Type*} (s : Finset ι) (g : Fin k → ι → ℝ)
    (hg : ∀ j i, 0 ≤ g j i) :
    ∑ i ∈ s, ∏ j : Fin k, g j i ≤ ∏ j : Fin k, (∑ i ∈ s, (g j i) ^ k) ^ (1 / ((k : ℕ) : ℝ)) := by
  have hk0 : (k : ℝ) ≠ 0 := by exact_mod_cast (by omega : k ≠ 0)
  have hkn : k ≠ 0 := by omega
  by_cases hne : ∀ j : Fin k, (∑ i ∈ s, (g j i) ^ k) ≠ 0
  · set A : Fin k → ℝ := fun j => (∑ i ∈ s, (g j i) ^ k) ^ (1 / ((k : ℕ) : ℝ)) with hA
    have hApos : ∀ j, 0 < A j := by
      intro j
      rw [hA]
      exact Real.rpow_pos_of_pos
        (lt_of_le_of_ne' (Finset.sum_nonneg fun i _ => pow_nonneg (hg j i) k) (hne j)) _
    have hAne : ∀ j, A j ≠ 0 := fun j => ne_of_gt (hApos j)
    have hAj : ∀ j, A j ^ k = ∑ i ∈ s, (g j i) ^ k := by
      intro j
      rw [hA, one_div]
      exact Real.rpow_inv_natCast_pow (Finset.sum_nonneg fun i _ => pow_nonneg (hg j i) k) hkn
    have hb_sum : ∑ i ∈ s, ∏ j : Fin k, (g j i / A j) ≤ 1 := by
      have hpt : ∀ i ∈ s, ∏ j : Fin k, (g j i / A j)
          ≤ (1 / ((k : ℕ) : ℝ)) * ∑ j : Fin k, (g j i / A j) ^ k := by
        intro i _
        have h := prod_le_inv_mul_sum_pow hk (fun j => g j i / A j)
          (fun j => div_nonneg (hg j i) (le_of_lt (hApos j)))
        calc ∏ j : Fin k, g j i / A j
            ≤ ((k : ℝ)⁻¹) * ∑ j : Fin k, (g j i / A j) ^ k := h
          _ = (1 / ((k : ℕ) : ℝ)) * ∑ j : Fin k, (g j i / A j) ^ k := by rw [one_div]
      calc ∑ i ∈ s, ∏ j : Fin k, (g j i / A j)
          ≤ ∑ i ∈ s, (1 / ((k : ℕ) : ℝ)) * ∑ j : Fin k, (g j i / A j) ^ k :=
            Finset.sum_le_sum hpt
        _ = (1 / ((k : ℕ) : ℝ)) * ∑ i ∈ s, ∑ j : Fin k, (g j i / A j) ^ k := by
            rw [Finset.mul_sum]
        _ = (1 / ((k : ℕ) : ℝ)) * ∑ j : Fin k, ∑ i ∈ s, (g j i / A j) ^ k := by
            rw [Finset.sum_comm]
        _ = (1 / ((k : ℕ) : ℝ)) * ∑ _j : Fin k, (1 : ℝ) := by
            congr 1
            refine Finset.sum_congr rfl fun j _ => ?_
            calc ∑ i ∈ s, (g j i / A j) ^ k
                = ∑ i ∈ s, (g j i) ^ k / A j ^ k := by
                  refine Finset.sum_congr rfl fun i _ => ?_
                  rw [div_pow]
              _ = (∑ i ∈ s, (g j i) ^ k) / A j ^ k := by rw [Finset.sum_div]
              _ = (∑ i ∈ s, (g j i) ^ k) / (∑ i ∈ s, (g j i) ^ k) := by rw [hAj j]
              _ = 1 := div_self (hne j)
        _ = 1 := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
            rw [one_div]
            field_simp
    calc ∑ i ∈ s, ∏ j : Fin k, g j i
        = (∏ j : Fin k, A j) * ∑ i ∈ s, ∏ j : Fin k, (g j i / A j) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [← Finset.prod_mul_distrib]
          refine Finset.prod_congr rfl fun j _ => ?_
          exact (mul_div_cancel₀ (g j i) (hAne j)).symm
      _ ≤ (∏ j : Fin k, A j) * 1 :=
          mul_le_mul_of_nonneg_left hb_sum (Finset.prod_nonneg fun j _ => le_of_lt (hApos j))
      _ = ∏ j : Fin k, A j := mul_one _
  · push Not at hne
    obtain ⟨j0, hj0⟩ := hne
    have hzero : ∀ i ∈ s, g j0 i = 0 := by
      intro i hi
      have hmem : (g j0 i) ^ k = 0 :=
        (Finset.sum_eq_zero_iff_of_nonneg fun i _ => pow_nonneg (hg j0 i) k).mp hj0 i hi
      exact eq_zero_of_pow_eq_zero hmem
    have hLHS : ∑ i ∈ s, ∏ j : Fin k, g j i = 0 := by
      refine Finset.sum_eq_zero fun i hi => ?_
      exact Finset.prod_eq_zero (Finset.mem_univ j0) (hzero i hi)
    rw [hLHS]
    exact Finset.prod_nonneg fun j _ =>
      Real.rpow_nonneg (Finset.sum_nonneg fun i _ => pow_nonneg (hg j i) k) _

end Commons.Analysis.Inequalities