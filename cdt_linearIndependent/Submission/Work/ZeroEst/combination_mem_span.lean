import Mathlib

namespace Work.ZeroEst

/-- Multiplying the basis expansion of `P i` (degree at most `d`) by `f i` puts
`(P i : PowerSeries ℚ) * f i` into the span of the `X^j * f i` (`j ≤ d`). -/
theorem combination_mem_span (m : ℕ) (f : Fin m → PowerSeries ℚ) (d : ℕ)
    (P : Fin m → Polynomial ℚ) (h : ∀ i, (P i).degree ≤ (d : WithBot ℕ)) :
    (∑ i, (P i : PowerSeries ℚ) * f i) ∈
      Submodule.span ℚ (Set.range (fun (ij : Fin m × Fin (d + 1)) =>
        (PowerSeries.X : PowerSeries ℚ) ^ (ij.2 : ℕ) * f ij.1)) := by
  classical
  set S : Submodule ℚ (PowerSeries ℚ) :=
    Submodule.span ℚ (Set.range (fun (ij : Fin m × Fin (d + 1)) =>
      (PowerSeries.X : PowerSeries ℚ) ^ (ij.2 : ℕ) * f ij.1)) with hS
  have gen : ∀ j : ℕ, j < d + 1 → ∀ i : Fin m,
      (PowerSeries.X : PowerSeries ℚ) ^ j * f i ∈ S := by
    intro j hj i
    rw [hS]
    exact Submodule.subset_span ⟨(i, ⟨j, hj⟩), rfl⟩
  apply Submodule.sum_mem
  intro i _
  have hdeg : (P i).natDegree < d + 1 :=
    Nat.lt_succ_iff.mpr (Polynomial.natDegree_le_iff_degree_le.mpr (h i))
  have hPi : (↑(P i) : PowerSeries ℚ) =
      ∑ j ∈ Finset.range (d + 1), PowerSeries.C ((P i).coeff j) * PowerSeries.X ^ j := by
    conv_lhs => rw [Polynomial.as_sum_range_C_mul_X_pow' (P i) hdeg]
    rw [show ((∑ j ∈ Finset.range (d + 1),
            Polynomial.C ((P i).coeff j) * Polynomial.X ^ j : Polynomial ℚ) : PowerSeries ℚ)
        = Polynomial.coeToPowerSeries.ringHom
            (∑ j ∈ Finset.range (d + 1),
              Polynomial.C ((P i).coeff j) * Polynomial.X ^ j) from rfl,
      map_sum]
    simp [Polynomial.coe_C, Polynomial.coe_mul, Polynomial.coe_pow, Polynomial.coe_X]
  rw [hPi, Finset.sum_mul]
  apply Submodule.sum_mem
  intro j hj
  have hjd : j < d + 1 := Finset.mem_range.mp hj
  have hterm : (PowerSeries.C ((P i).coeff j) * PowerSeries.X ^ j) * f i
      = ((P i).coeff j) • (PowerSeries.X ^ j * f i) := by
    rw [mul_assoc, ← PowerSeries.smul_eq_C_mul]
  rw [hterm]
  exact Submodule.smul_mem _ _ (gen j hjd i)

end Work.ZeroEst
