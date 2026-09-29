import Mathlib

namespace Work.C17adj

theorem deriv2_mul_le (p q : Polynomial ℂ) (hq : q.natDegree ≤ 27) :
    (p.derivative.derivative * q).natDegree ≤ p.natDegree + 25 ∧
      (p.derivative.derivative * q).coeff (p.natDegree + 25)
        = (p.natDegree : ℂ) * ((p.natDegree : ℂ) - 1) * p.leadingCoeff * q.coeff 27 := by
  -- Second derivative of a polynomial over a field of characteristic zero has
  -- `natDegree` exactly `natDegree p - 2`.
  have hd2 : p.derivative.derivative.natDegree = p.natDegree - 2 := by
    rw [Polynomial.natDegree_derivative, Polynomial.natDegree_derivative]
    omega
  rcases lt_or_ge p.natDegree 2 with hd | hd
  · -- `natDegree p ≤ 1`: the second derivative vanishes.
    have hz : p.derivative.derivative = 0 := by
      have h := Polynomial.iterate_derivative_eq_zero (p := p) (x := 2) hd
      simpa using h
    constructor
    · rw [hz, zero_mul, Polynomial.natDegree_zero]
      omega
    · rw [hz, zero_mul, Polynomial.coeff_zero]
      interval_cases p.natDegree <;> simp
  · constructor
    · -- Degree bound: `deg (p'' * q) ≤ (deg p - 2) + deg q ≤ deg p + 25`.
      calc (p.derivative.derivative * q).natDegree
          ≤ p.derivative.derivative.natDegree + q.natDegree := Polynomial.natDegree_mul_le
        _ = (p.natDegree - 2) + q.natDegree := by rw [hd2]
        _ ≤ (p.natDegree - 2) + 27 := by gcongr
        _ = p.natDegree + 25 := by omega
    · -- Only the pair `(deg p - 2, 27)` can contribute to the coefficient of
      -- `X ^ (deg p + 25)`.
      have key : (p.derivative.derivative * q).coeff (p.natDegree + 25)
            = p.derivative.derivative.coeff (p.natDegree - 2) * q.coeff 27 := by
        rw [Polynomial.coeff_mul]
        refine Finset.sum_eq_single_of_mem (p.natDegree - 2, 27) ?_ ?_
        · rw [Finset.HasAntidiagonal.mem_antidiagonal]
          omega
        · intro x hx hne
          rw [Finset.HasAntidiagonal.mem_antidiagonal] at hx
          by_cases h2 : x.2 ≤ 27
          · -- then `x.1 = deg p + 25 - x.2 ≥ deg p - 2`, so `x.1` exceeds `deg p''`
            -- unless `x = (deg p - 2, 27)`.
            have hx1 : p.derivative.derivative.natDegree < x.1 := by
              rw [hd2]
              have hle : p.natDegree - 2 ≤ x.1 := by omega
              have hne' : x.1 ≠ p.natDegree - 2 := by
                intro h
                have hx2 : x.2 = 27 := by omega
                exact hne (Prod.ext h hx2)
              exact lt_of_le_of_ne hle (Ne.symm hne')
            rw [Polynomial.coeff_eq_zero_of_natDegree_lt hx1, zero_mul]
          · rw [Polynomial.coeff_eq_zero_of_natDegree_lt
              (lt_of_le_of_lt hq (not_le.mp h2)), mul_zero]
      rw [key]
      -- The leading coefficient of `p''`: differentiating twice multiplies the
      -- leading coefficient by `deg p * (deg p - 1)`.
      have hc : p.derivative.derivative.coeff (p.natDegree - 2)
          = (p.natDegree : ℂ) * ((p.natDegree : ℂ) - 1) * p.leadingCoeff := by
        rw [Polynomial.coeff_derivative, Polynomial.coeff_derivative]
        rw [show (p.natDegree - 2) + 1 + 1 = p.natDegree from by omega,
            show (p.natDegree - 2) + 1 = p.natDegree - 1 from by omega]
        rw [show p.coeff p.natDegree = p.leadingCoeff from rfl]
        rw [Nat.cast_pred (by omega : 0 < p.natDegree),
            Nat.cast_sub (by omega : 2 ≤ p.natDegree)]
        ring
      rw [hc]

end Work.C17adj
