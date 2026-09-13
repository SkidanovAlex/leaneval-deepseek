import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.Order.Archimedean.Real.Basic

namespace Commons.Analysis.Sigma2

open scoped BigOperators in
theorem jacobi_log_algebra {n : ℕ} (lam d Lu D1 D2 : Fin n → ℝ) (S eps δ : ℝ)
    (hS : S = ∑ t : Fin n, lam t) (hδ : δ = 1 + eps) (hSpos : 0 < S)
    (hD1 : ∀ i : Fin n, D1 i = Lu i / S)
    (hD2 : ∀ i : Fin n, D2 i = d i / S - (Lu i / S) ^ 2)
    (hineq : 0 ≤ (∑ i : Fin n, (S - lam i) * d i)
      - (δ / S) * (∑ i : Fin n, (S - lam i) * (Lu i) ^ 2)) :
    eps * (∑ i : Fin n, (S - lam i) * (D1 i) ^ 2)
      ≤ ∑ i : Fin n, (S - lam i) * (D2 i) := by
  have hSne : S ≠ 0 := ne_of_gt hSpos
  have hS2 : (0:ℝ) < S ^ 2 := by positivity
  simp only [hD1, hD2]
  -- Sum identity for the left
  have hL : (∑ i : Fin n, (S - lam i) * (Lu i / S) ^ 2)
      = (∑ i : Fin n, (S - lam i) * (Lu i) ^ 2) / S ^ 2 := by
    simp_rw [div_pow, ← mul_div_assoc]
    rw [← Finset.sum_div]
  -- Sum identity for the right
  have hR : (∑ i : Fin n, (S - lam i) * (d i / S - (Lu i / S) ^ 2))
      = (∑ i : Fin n, (S - lam i) * d i) / S
        - (∑ i : Fin n, (S - lam i) * (Lu i) ^ 2) / S ^ 2 := by
    simp only [div_pow]
    have hterm : ∀ i : Fin n, (S - lam i) * (d i / S - (Lu i) ^ 2 / S ^ 2)
        = (S - lam i) * d i / S - (S - lam i) * (Lu i) ^ 2 / S ^ 2 := by
      intro i; ring
    simp_rw [hterm]
    rw [Finset.sum_sub_distrib, ← Finset.sum_div, ← Finset.sum_div]
  -- Key inequality obtained from hineq
  have hkey : δ * (∑ i : Fin n, (S - lam i) * (Lu i) ^ 2)
      ≤ S * (∑ i : Fin n, (S - lam i) * d i) := by
    have hfac : S * ((δ / S) * (∑ i : Fin n, (S - lam i) * (Lu i) ^ 2))
        = δ * (∑ i : Fin n, (S - lam i) * (Lu i) ^ 2) := by
      rw [← mul_assoc, mul_div_cancel₀ δ hSne]
    have h2 : 0 ≤ S * ((∑ i : Fin n, (S - lam i) * d i)
        - (δ / S) * (∑ i : Fin n, (S - lam i) * (Lu i) ^ 2)) :=
      mul_nonneg (le_of_lt hSpos) hineq
    rw [mul_sub, hfac] at h2
    linarith [h2]
  rw [hL, hR]
  have h2 : eps * ((∑ i : Fin n, (S - lam i) * (Lu i) ^ 2) / S ^ 2)
      = (eps * (∑ i : Fin n, (S - lam i) * (Lu i) ^ 2)) / S ^ 2 := by
    rw [← mul_div_assoc]
  have h3 : (∑ i : Fin n, (S - lam i) * d i) / S
        - (∑ i : Fin n, (S - lam i) * (Lu i) ^ 2) / S ^ 2
      = (S * (∑ i : Fin n, (S - lam i) * d i)
          - (∑ i : Fin n, (S - lam i) * (Lu i) ^ 2)) / S ^ 2 := by
    field_simp
  rw [hδ] at hkey
  rw [h2, h3, div_le_div_iff_of_pos_right hS2]
  nlinarith [hkey]

end Commons.Analysis.Sigma2