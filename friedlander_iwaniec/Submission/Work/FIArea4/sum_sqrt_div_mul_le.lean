import Mathlib

namespace Work.FIArea4

/-- For `R, R' ≥ 1`,
`∑_{d ≤ min R R'} √(R/d) √(R'/d) ≤ √(R R') (log(min R R') + 1)`.
Proof: each term equals `√(R R') / d` (via `Real.sqrt_div`, `Real.sqrt_mul`), the sum factors as
`√(R R') · ∑_{d ≤ M} 1/d` with `M = min R R' ≥ 1`, and `∑_{d ≤ M} 1/d ≤ 1 + log M`
(`harmonic_eq_sum_Icc` and `harmonic_le_one_add_log` in `Mathlib/NumberTheory/Harmonic/Bounds.lean`,
or the ready-made real version `Commons.Analysis.ExpLog.harmonic_le_one_add_log` in
`Submission/Commons/Analysis/ExpLog/harmonic_le_one_add_log.lean`).  Finally
`Real.log (min (R:ℝ) (R':ℝ)) = Real.log ((min R R' : ℕ) : ℝ)` by `Nat.cast_min`. -/
theorem sum_sqrt_div_mul_le (R R' : ℕ) (hR : 1 ≤ R) (hR' : 1 ≤ R') :
    ∑ d ∈ Finset.Icc 1 (min R R'),
        Real.sqrt ((R : ℝ) / (d : ℝ)) * Real.sqrt ((R' : ℝ) / (d : ℝ))
      ≤ Real.sqrt ((R : ℝ) * (R' : ℝ)) * (Real.log (min (R : ℝ) (R' : ℝ)) + 1) := by
  have hlog : Real.log (min (R : ℝ) (R' : ℝ)) = Real.log (((min R R' : ℕ)) : ℝ) := by
    rw [Nat.cast_min]
  rw [hlog]
  -- each summand equals `√(R R') · (1/d)`
  have hterm : ∀ d ∈ Finset.Icc 1 (min R R'),
      Real.sqrt ((R : ℝ) / (d : ℝ)) * Real.sqrt ((R' : ℝ) / (d : ℝ))
        = Real.sqrt ((R : ℝ) * (R' : ℝ)) * ((1:ℝ)/(d:ℝ)) := by
    intro d hd
    have hd1 : 1 ≤ d := (Finset.mem_Icc.mp hd).1
    have hd0 : (0:ℝ) < (d:ℝ) := by exact_mod_cast hd1
    have hR0 : (0:ℝ) ≤ (R:ℝ) := Nat.cast_nonneg R
    have hR'0 : (0:ℝ) ≤ (R':ℝ) := Nat.cast_nonneg R'
    rw [Real.sqrt_div hR0 (d:ℝ), Real.sqrt_div hR'0 (d:ℝ)]
    rw [div_mul_div_comm]
    rw [← Real.sqrt_mul hR0 (R':ℝ)]
    have hsq : Real.sqrt (d:ℝ) * Real.sqrt (d:ℝ) = (d:ℝ) := by
      rw [← sq, Real.sq_sqrt (le_of_lt hd0)]
    rw [hsq, div_eq_mul_inv]
    rw [one_div]
  have hsum : ∑ d ∈ Finset.Icc 1 (min R R'),
        Real.sqrt ((R : ℝ) / (d : ℝ)) * Real.sqrt ((R' : ℝ) / (d : ℝ))
      = Real.sqrt ((R : ℝ) * (R' : ℝ)) * ∑ d ∈ Finset.Icc 1 (min R R'), (1:ℝ)/(d:ℝ) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl hterm
  rw [hsum]
  -- the real harmonic bound `∑_{d ≤ M} 1/d ≤ 1 + log M`
  have hharm : (∑ d ∈ Finset.Icc 1 (min R R'), (1:ℝ)/(d:ℝ))
      ≤ 1 + Real.log (((min R R' : ℕ)) : ℝ) := by
    have h_eq : (∑ k ∈ Finset.Icc 1 (min R R'), (1:ℝ)/(k:ℝ)) = (harmonic (min R R') : ℝ) := by
      rw [harmonic_eq_sum_Icc, Rat.cast_sum]
      apply Finset.sum_congr rfl
      intro k hk
      rw [Rat.cast_inv]
      simp
    rw [h_eq]
    exact harmonic_le_one_add_log (min R R')
  calc Real.sqrt ((R : ℝ) * (R' : ℝ)) * ∑ d ∈ Finset.Icc 1 (min R R'), (1:ℝ)/(d:ℝ)
      ≤ Real.sqrt ((R : ℝ) * (R' : ℝ)) * (1 + Real.log (((min R R' : ℕ)) : ℝ)) :=
        mul_le_mul_of_nonneg_left hharm (Real.sqrt_nonneg _)
    _ = Real.sqrt ((R : ℝ) * (R' : ℝ)) * (Real.log (((min R R' : ℕ)) : ℝ) + 1) := by ring

end Work.FIArea4
