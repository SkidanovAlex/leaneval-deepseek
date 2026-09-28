import Mathlib
import Submission.Work.Q44Geom.MaxDeg

namespace Work.Q44Geom

/-- If a product `A * B` of nonzero rational polynomials in 5 variables is homogeneous of degree
`n`, then the minimal degrees of `A` and `B` exist and add up to `n`. -/
theorem exists_minDeg_add_of_mul_eq {n : ℕ} {P A B : MvPolynomial (Fin 5) ℚ}
    (hP : P.IsHomogeneous n) (hAB : P = A * B) (hA : A ≠ 0) (hB : B ≠ 0) :
    ∃ i j : ℕ, IsMinDeg i A ∧ IsMinDeg j B ∧ i + j = n := by
  obtain ⟨i, hi⟩ := exists_isMinDeg A hA
  obtain ⟨j, hj⟩ := exists_isMinDeg B hB
  refine ⟨i, j, hi, hj, ?_⟩
  by_contra h
  have hne : MvPolynomial.homogeneousComponent (i + j) (A * B) ≠ 0 := by
    rw [homogeneousComponent_mul_of_minDeg hi hj]
    exact mul_ne_zero (IsMinDeg.coeff_ne_zero hi) (IsMinDeg.coeff_ne_zero hj)
  rw [← hAB] at hne
  have hmem : P ∈ MvPolynomial.homogeneousSubmodule (Fin 5) ℚ n :=
    MvPolynomial.mem_homogeneousSubmodule n P |>.mpr hP
  have hz : MvPolynomial.homogeneousComponent (i + j) P = 0 := by
    rw [MvPolynomial.homogeneousComponent_of_mem hmem]
    simp [h]
  exact hne hz

end Work.Q44Geom
