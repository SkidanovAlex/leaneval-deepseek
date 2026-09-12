import Mathlib.Analysis.Polynomial.Norm

namespace Commons.NumberTheory.DiophantineApproximation.BoundedDegree

/-- The sup norm of a nonzero integer polynomial (mapped to the reals) is at least one. -/
theorem int_poly_supNorm_one_le (P : Polynomial ℤ) (h : P ≠ 0) :
    1 ≤ (P.map (Int.castRingHom ℝ)).supNorm := by
  let Q : Polynomial ℝ := P.map (Int.castRingHom ℝ)
  -- `P` is nonzero, so some coefficient is nonzero
  have hPsup : P.support.Nonempty := Polynomial.support_nonempty.2 h
  obtain ⟨i, hiP⟩ := hPsup
  have hzi : P.coeff i ≠ 0 := Polynomial.mem_support_iff.mp hiP
  -- coefficient maps to a nonzero integer in ℝ, whose norm is at least one
  have hnorm : 1 ≤ ‖((P.coeff i : ℤ) : ℝ)‖ := by
    rw [Real.norm_eq_abs, ← Int.cast_abs]
    have hle : (1 : ℤ) ≤ |P.coeff i| := by
      have hzpos : 0 < |P.coeff i| := abs_pos.mpr hzi
      omega
    exact_mod_cast hle
  -- and the coefficient norm is bounded above by the sup norm
  have hQi : Q.coeff i = ((P.coeff i : ℤ) : ℝ) := by
    dsimp [Q]
    rw [Polynomial.coeff_map]
    rfl
  rw [← hQi] at hnorm
  exact le_trans hnorm (Q.le_supNorm i)

end Commons.NumberTheory.DiophantineApproximation.BoundedDegree