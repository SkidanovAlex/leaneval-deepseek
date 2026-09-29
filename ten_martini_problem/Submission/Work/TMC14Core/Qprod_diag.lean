import Mathlib
import Submission.Work.TMC14Core.InvSumAux

/-!
# `Work.TMC14Core.Qprod_diag`

Diagonal values of
`Qprod ω a b = ∏_{k=1}^{a} (1 - ω^{b+k})` at `a = b = m`, for `ω` a `(2m+1)`-st root
of unity:

  `Qprod ω m m = (-1)^m * (ω^(m(m+1)/2))⁻¹ * Dprod ω m`.

The proof pairs the factor `1 - ω^{m+k}` (`1 ≤ k ≤ m`) with the factor `1 - ω^{m+1-k}`:
because `ω^(2m+1) = 1` one has `ω^(m+1-k) * (1 - ω^(m+k)) = -(1 - ω^(m+1-k))`.  Hence

  `ω^(m(m+1)/2) * Qprod ω m m = (-1)^m * ∏_{k=1}^{m} (1 - ω^{m+1-k})`,

and the remaining product is `Dprod ω m` after the substitution `k ↦ m+1-k` on the
index set `Icc 1 m`.
-/

noncomputable section

namespace Work.TMC14Core

open Finset

/-- Gauss' summation formula in the reflected form used below: the exponents `m+1-k`
summed over `1 ≤ k ≤ m` add up to `m(m+1)/2`. -/
theorem sum_Icc_sub_id (m : ℕ) :
    (∑ k ∈ Finset.Icc 1 m, (m + 1 - k)) = m * (m + 1) / 2 := by
  have hS : (∑ k ∈ Finset.Icc 1 m, (m + 1 - k)) = (∑ k ∈ Finset.range m, k) + m := by
    rw [← Finset.Ico_add_one_right_eq_Icc (1 : ℕ) m, Finset.sum_Ico_eq_sum_range]
    rw [show (m + 1) - 1 = m by omega]
    have hpt : ∀ k ∈ Finset.range m, m + 1 - (1 + k) = (m - 1 - k) + 1 := by
      intro k hk
      have hk' : k < m := Finset.mem_range.mp hk
      omega
    rw [Finset.sum_congr rfl hpt]
    have hreflect : (∑ k ∈ Finset.range m, ((m - 1 - k) + 1))
        = ∑ k ∈ Finset.range m, (k + 1) :=
      Finset.sum_range_reflect (fun x : ℕ => x + 1) m
    have hc : (∑ k ∈ Finset.range m, (1 : ℕ)) = m := by
      rw [Finset.sum_const, Finset.card_range]
      simp
    rw [hreflect, Finset.sum_add_distrib, hc]
  have hsum : (∑ k ∈ Finset.range m, k) + m = ∑ k ∈ Finset.range (m + 1), k :=
    (Finset.sum_range_succ (fun j : ℕ => j) m).symm
  have hcalc : (∑ k ∈ Finset.range (m + 1), k) = m * (m + 1) / 2 := by
    rw [Finset.sum_range_id]
    have h2 : (m + 1) * ((m + 1) - 1) = m * (m + 1) := by
      rw [show (m + 1) - 1 = m by omega]
      ring
    rw [h2]
  rw [hS, hsum, hcalc]

/-- The substitution `k ↦ m+1-k` on `Icc 1 m` turns the product of the factors
`1 - ω^{m+1-k}` into `Dprod ω m`. -/
theorem prod_Icc_reflect_sub (ω : ℂ) (m : ℕ) :
    (∏ k ∈ Finset.Icc 1 m, (1 - ω ^ (m + 1 - k))) = Dprod ω m := by
  simp only [Dprod]
  rw [← Finset.Ico_add_one_right_eq_Icc (1 : ℕ) m]
  have hreflect :
      (∏ k ∈ Finset.Ico 1 (m + 1), (1 - ω ^ (m + 1 - k)))
        = ∏ k ∈ Finset.Ico ((m + 1) + 1 - (m + 1)) ((m + 1) + 1 - 1), (1 - ω ^ k) :=
    Finset.prod_Ico_reflect (fun j : ℕ => 1 - ω ^ j) 1 (by omega : m + 1 ≤ m + 1 + 1)
  rw [hreflect, show (m + 1) + 1 - (m + 1) = (1 : ℕ) by omega,
    show (m + 1) + 1 - 1 = m + 1 by omega]

/-- **The diagonal value of `Qprod`.**  For `ω^(2m+1) = 1`,
`Qprod ω m m = (-1)^m * (ω^(m(m+1)/2))⁻¹ * Dprod ω m`. -/
theorem Qprod_diag (ω : ℂ) (m : ℕ) (hω1 : ω ^ (2 * m + 1) = 1) :
    Qprod ω m m = (-1) ^ m * (ω ^ (m * (m + 1) / 2))⁻¹ * Dprod ω m := by
  have hω : ω ≠ 0 := by
    intro h0
    rw [h0, zero_pow (by omega : 2 * m + 1 ≠ 0)] at hω1
    exact zero_ne_one hω1
  have hX : ω ^ (m * (m + 1) / 2) ≠ 0 := pow_ne_zero _ hω
  have hX1 : ω ^ (m * (m + 1) / 2) = ∏ k ∈ Finset.Icc 1 m, ω ^ (m + 1 - k) := by
    rw [Finset.prod_pow_eq_pow_sum, sum_Icc_sub_id]
  have hD : (∏ k ∈ Finset.Icc 1 m, (1 - ω ^ (m + 1 - k))) = Dprod ω m :=
    prod_Icc_reflect_sub ω m
  have hterm : ∀ k ∈ Finset.Icc 1 m,
      ω ^ (m + 1 - k) * (1 - ω ^ (m + k)) = -(1 - ω ^ (m + 1 - k)) := by
    intro k hk
    have hk2 : k ≤ m := (Finset.mem_Icc.mp hk).2
    have hp : ω ^ (m + 1 - k) * ω ^ (m + k) = 1 := by
      rw [← pow_add, show m + 1 - k + (m + k) = 2 * m + 1 by omega, hω1]
    rw [mul_sub, mul_one, hp]
    ring
  have key : ω ^ (m * (m + 1) / 2) * Qprod ω m m = (-1) ^ m * Dprod ω m := by
    calc ω ^ (m * (m + 1) / 2) * Qprod ω m m
        = (∏ k ∈ Finset.Icc 1 m, ω ^ (m + 1 - k))
            * ∏ k ∈ Finset.Icc 1 m, (1 - ω ^ (m + k)) := by
          rw [hX1]
          simp only [Qprod]
      _ = ∏ k ∈ Finset.Icc 1 m, (ω ^ (m + 1 - k) * (1 - ω ^ (m + k))) := by
          rw [Finset.prod_mul_distrib]
      _ = ∏ k ∈ Finset.Icc 1 m, (-(1 - ω ^ (m + 1 - k))) :=
          Finset.prod_congr rfl hterm
      _ = (-1) ^ m * ∏ k ∈ Finset.Icc 1 m, (1 - ω ^ (m + 1 - k)) := by
          rw [Finset.prod_neg]
          simp
      _ = (-1) ^ m * Dprod ω m := by rw [hD]
  calc Qprod ω m m
      = (ω ^ (m * (m + 1) / 2))⁻¹ * (ω ^ (m * (m + 1) / 2) * Qprod ω m m) := by
        rw [← mul_assoc, inv_mul_cancel₀ hX, one_mul]
    _ = (ω ^ (m * (m + 1) / 2))⁻¹ * ((-1) ^ m * Dprod ω m) := by rw [key]
    _ = (-1) ^ m * (ω ^ (m * (m + 1) / 2))⁻¹ * Dprod ω m := by
        rw [← mul_assoc, mul_comm ((ω ^ (m * (m + 1) / 2))⁻¹) ((-1) ^ m)]

end Work.TMC14Core
