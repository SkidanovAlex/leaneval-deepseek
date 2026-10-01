import Submission.Commons.NumberTheory.Zeta.chebyshev_psi_sub_id_exp

namespace Work.LinnikAreas.A5

/-- PNT with the classical (de la Vallée Poussin) error term, in the shape needed for
Heath-Brown's §13–15: `|ψ(t) − t| ≤ K·t·exp(−c√(log t))` for **all** `t ≥ 1`.

The analytic content is the already-proved commons lemma
`Commons.NumberTheory.Zeta.chebyshev_psi_sub_id_exp_uniform`, valid for `x ≥ 2`
with constants `(c, C)`.  Extending the range down to `t ≥ 1` is elementary:
on the bounded window `[1,2]` the crude Chebyshev bound `ψ(t) ≤ (log 4 + 4)·t`
together with `0 ≤ ψ(t)` gives `|ψ(t) − t| ≤ (log 4 + 5)·t`, and since
`exp(−c√(log t)) ≥ exp(−c√(log 2))` there, the enlarged constant
`K = max C ((log 4 + 5)·exp(c√(log 2)))` absorbs the window. -/
theorem psi_sub_id_exp_bound :
    ∃ K c : ℝ, 0 < K ∧ 0 < c ∧ ∀ t : ℝ, 1 ≤ t →
      |Chebyshev.psi t - t| ≤ K * t * Real.exp (-c * Real.sqrt (Real.log t)) := by
  obtain ⟨c, C, hc, hCpos, hbound⟩ :=
    Commons.NumberTheory.Zeta.chebyshev_psi_sub_id_exp_uniform
  have hlog4pos : 0 < Real.log 4 := Real.log_pos (by norm_num)
  have hApos : 0 < Real.log 4 + 5 := by linarith
  have hEpos : 0 < (Real.log 4 + 5) * Real.exp (c * Real.sqrt (Real.log 2)) :=
    mul_pos hApos (Real.exp_pos _)
  refine ⟨max C ((Real.log 4 + 5) * Real.exp (c * Real.sqrt (Real.log 2))), c,
    lt_of_lt_of_le hCpos (le_max_left _ _), hc, ?_⟩
  intro t ht
  have htpos : 0 < t := lt_of_lt_of_le zero_lt_one ht
  have hexpnn : 0 ≤ Real.exp (-c * Real.sqrt (Real.log t)) := Real.exp_nonneg _
  by_cases ht2 : 2 ≤ t
  · have h1 := hbound t ht2
    have hCle : C ≤ max C ((Real.log 4 + 5) * Real.exp (c * Real.sqrt (Real.log 2))) :=
      le_max_left _ _
    calc |Chebyshev.psi t - t|
        ≤ C * t * Real.exp (-c * Real.sqrt (Real.log t)) := h1
      _ ≤ (max C ((Real.log 4 + 5) * Real.exp (c * Real.sqrt (Real.log 2)))) * t *
            Real.exp (-c * Real.sqrt (Real.log t)) := by
          have hstep : C * t ≤
              (max C ((Real.log 4 + 5) * Real.exp (c * Real.sqrt (Real.log 2)))) * t :=
            mul_le_mul_of_nonneg_right hCle (le_of_lt htpos)
          exact mul_le_mul_of_nonneg_right hstep hexpnn
  · have ht2lt : t < 2 := lt_of_not_ge ht2
    have hpsi : Chebyshev.psi t ≤ (Real.log 4 + 4) * t :=
      Chebyshev.psi_le_const_mul_self (by linarith)
    have hpsinonneg : 0 ≤ Chebyshev.psi t := Chebyshev.psi_nonneg t
    have habs : |Chebyshev.psi t - t| ≤ (Real.log 4 + 5) * t := by
      rw [abs_le]
      constructor <;> nlinarith
    have hlogt_le : Real.log t ≤ Real.log 2 := Real.log_le_log htpos (le_of_lt ht2lt)
    have hsqrtle : Real.sqrt (Real.log t) ≤ Real.sqrt (Real.log 2) :=
      Real.sqrt_le_sqrt hlogt_le
    have hmono : c * Real.sqrt (Real.log t) ≤ c * Real.sqrt (Real.log 2) :=
      mul_le_mul_of_nonneg_left hsqrtle (le_of_lt hc)
    have hexpge : Real.exp (-c * Real.sqrt (Real.log 2)) ≤
        Real.exp (-c * Real.sqrt (Real.log t)) :=
      Real.exp_le_exp.mpr (by linarith)
    have hKey : (Real.log 4 + 5) ≤
        (max C ((Real.log 4 + 5) * Real.exp (c * Real.sqrt (Real.log 2)))) *
          Real.exp (-c * Real.sqrt (Real.log t)) := by
      have hbase : ((Real.log 4 + 5) * Real.exp (c * Real.sqrt (Real.log 2))) *
            Real.exp (-c * Real.sqrt (Real.log 2)) = (Real.log 4 + 5) := by
        rw [mul_assoc, ← Real.exp_add]
        have hzero : c * Real.sqrt (Real.log 2) + -c * Real.sqrt (Real.log 2) = 0 := by ring
        rw [hzero, Real.exp_zero, mul_one]
      calc (Real.log 4 + 5)
          = ((Real.log 4 + 5) * Real.exp (c * Real.sqrt (Real.log 2))) *
              Real.exp (-c * Real.sqrt (Real.log 2)) := hbase.symm
        _ ≤ ((Real.log 4 + 5) * Real.exp (c * Real.sqrt (Real.log 2))) *
              Real.exp (-c * Real.sqrt (Real.log t)) :=
            mul_le_mul_of_nonneg_left hexpge (le_of_lt hEpos)
        _ ≤ (max C ((Real.log 4 + 5) * Real.exp (c * Real.sqrt (Real.log 2)))) *
              Real.exp (-c * Real.sqrt (Real.log t)) :=
            mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.exp_nonneg _)
    calc |Chebyshev.psi t - t| ≤ (Real.log 4 + 5) * t := habs
      _ ≤ ((max C ((Real.log 4 + 5) * Real.exp (c * Real.sqrt (Real.log 2)))) *
              Real.exp (-c * Real.sqrt (Real.log t))) * t :=
            mul_le_mul_of_nonneg_right hKey (le_of_lt htpos)
      _ = (max C ((Real.log 4 + 5) * Real.exp (c * Real.sqrt (Real.log 2)))) * t *
              Real.exp (-c * Real.sqrt (Real.log t)) := by ring

end Work.LinnikAreas.A5
