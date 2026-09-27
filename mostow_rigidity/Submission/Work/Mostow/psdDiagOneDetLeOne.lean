import Mathlib

namespace Work.Mostow

open Matrix

/-- A positive semidefinite real matrix all of whose diagonal entries equal `1` has
determinant at most `1` (a Hadamard-type bound, proved here via the spectral theorem:
the eigenvalues are nonnegative and sum to the trace `n`, so their product is at most
`(n/n)^n = 1` by AM–GM). -/
theorem psdDiagOneDetLeOne {n : Type*} [Fintype n] [DecidableEq n] (B : Matrix n n ℝ)
    (hB : B.PosSemidef) (hdiag : ∀ i, B i i = 1) : B.det ≤ 1 := by
  classical
  set lam : n → ℝ := hB.isHermitian.eigenvalues with hlam
  have hdet : B.det = ∏ i, lam i := hB.isHermitian.det_eq_prod_eigenvalues
  have htrace : B.trace = ∑ i, lam i := hB.isHermitian.trace_eq_sum_eigenvalues
  have hnonneg : ∀ i, 0 ≤ lam i := fun i => hB.eigenvalues_nonneg i
  have htr : (∑ i, lam i) = (Fintype.card n : ℝ) := by
    rw [← htrace]
    simp [Matrix.trace, hdiag]
  by_cases hc : Fintype.card n = 0
  · have : IsEmpty n := Fintype.card_eq_zero_iff.mp hc
    rw [hdet]
    simp
  · have hcpos : 0 < (Fintype.card n : ℝ) := by
      exact_mod_cast Nat.pos_of_ne_zero hc
    have hcne : (Fintype.card n : ℝ) ≠ 0 := ne_of_gt hcpos
    have hP : 0 ≤ ∏ i, lam i := Finset.prod_nonneg (fun i _ => hnonneg i)
    have hgm := Real.geom_mean_le_arith_mean_weighted (Finset.univ : Finset n)
        (fun _ => ((Fintype.card n : ℝ))⁻¹) lam
        (fun _ _ => by positivity) ?_ (fun i _ => hnonneg i)
    · rw [Real.finsetProd_rpow _ _ (fun i _ => hnonneg i) _] at hgm
      rw [← Finset.mul_sum] at hgm
      rw [htr] at hgm
      rw [inv_mul_cancel₀ hcne] at hgm
      have h1 : (∏ i, lam i) = ((∏ i, lam i) ^ ((Fintype.card n : ℝ))⁻¹) ^ (Fintype.card n : ℝ) := by
        rw [← Real.rpow_mul hP, inv_mul_cancel₀ hcne, Real.rpow_one]
      rw [hdet, h1]
      calc ((∏ i, lam i) ^ ((Fintype.card n : ℝ))⁻¹) ^ (Fintype.card n : ℝ)
          ≤ 1 ^ (Fintype.card n : ℝ) :=
            Real.rpow_le_rpow (Real.rpow_nonneg hP _) hgm (le_of_lt hcpos)
        _ = 1 := Real.one_rpow _
    · rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      exact mul_inv_cancel₀ hcne

end Work.Mostow
