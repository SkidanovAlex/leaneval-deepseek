import Mathlib

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.MotAS

/-- A nonzero affine linear form in two variables over a field is irreducible. -/
theorem ASZB0LinearIrred (L : Type) [Field L] (a b c : L) (h : a ≠ 0 ∨ b ≠ 0) :
    Irreducible (MvPolynomial.C a * MvPolynomial.X 0 + MvPolynomial.C b * MvPolynomial.X 1
      + MvPolynomial.C c : MvPolynomial (Fin 2) L) := by
  -- the two monomials on which the linear part lives
  have hne : ∀ i j : Fin 2, i ≠ j → (Finsupp.single i 1 : Fin 2 →₀ ℕ) ≠ Finsupp.single j 1 := by
    intro i j hij hh
    exact hij ((Finsupp.single_left_inj (by norm_num : (1:ℕ) ≠ 0)).mp hh)
  have hz : ∀ i : Fin 2, (0 : Fin 2 →₀ ℕ) ≠ Finsupp.single i 1 := by
    intro i hh
    exact one_ne_zero (Finsupp.single_eq_zero.mp hh.symm)
  -- the two relevant coefficients
  have hcoeff0 : (MvPolynomial.C a * MvPolynomial.X (0:Fin 2) + MvPolynomial.C b * MvPolynomial.X 1
      + MvPolynomial.C c : MvPolynomial (Fin 2) L).coeff (Finsupp.single 0 1) = a := by
    rw [MvPolynomial.coeff_add, MvPolynomial.coeff_add, MvPolynomial.coeff_C_mul,
      MvPolynomial.coeff_C_mul]
    simp only [MvPolynomial.coeff_X, MvPolynomial.coeff_C,
      hne 1 0 (by decide), hz 0, ite_false, mul_zero, add_zero]
    simp
  have hcoeff1 : (MvPolynomial.C a * MvPolynomial.X (0:Fin 2) + MvPolynomial.C b * MvPolynomial.X 1
      + MvPolynomial.C c : MvPolynomial (Fin 2) L).coeff (Finsupp.single 1 1) = b := by
    rw [MvPolynomial.coeff_add, MvPolynomial.coeff_add, MvPolynomial.coeff_C_mul,
      MvPolynomial.coeff_C_mul]
    simp only [MvPolynomial.coeff_X, MvPolynomial.coeff_C,
      hne 0 1 (by decide), hz 1, ite_false, mul_zero, add_zero]
    simp
  -- degree bounds
  have hu : (MvPolynomial.C a * MvPolynomial.X (0:Fin 2) : MvPolynomial (Fin 2) L).totalDegree ≤ 1 := by
    simpa using MvPolynomial.totalDegree_mul (MvPolynomial.C a) (MvPolynomial.X (0:Fin 2))
  have hv : (MvPolynomial.C b * MvPolynomial.X (1:Fin 2) : MvPolynomial (Fin 2) L).totalDegree ≤ 1 := by
    simpa using MvPolynomial.totalDegree_mul (MvPolynomial.C b) (MvPolynomial.X (1:Fin 2))
  have hw : (MvPolynomial.C c : MvPolynomial (Fin 2) L).totalDegree ≤ 1 := by
    rw [MvPolynomial.totalDegree_C]; exact Nat.zero_le 1
  have hle : (MvPolynomial.C a * MvPolynomial.X (0:Fin 2) + MvPolynomial.C b * MvPolynomial.X (1:Fin 2)
      + MvPolynomial.C c : MvPolynomial (Fin 2) L).totalDegree ≤ 1 := by
    have h1 : (MvPolynomial.C a * MvPolynomial.X (0:Fin 2) + MvPolynomial.C b * MvPolynomial.X (1:Fin 2)
        : MvPolynomial (Fin 2) L).totalDegree ≤ 1 :=
      le_trans (MvPolynomial.totalDegree_add _ _) (max_le hu hv)
    exact le_trans (MvPolynomial.totalDegree_add _ _) (max_le h1 hw)
  have hge : 1 ≤ (MvPolynomial.C a * MvPolynomial.X (0:Fin 2) + MvPolynomial.C b * MvPolynomial.X (1:Fin 2)
      + MvPolynomial.C c : MvPolynomial (Fin 2) L).totalDegree := by
    rcases h with ha | hb
    · have hmem : Finsupp.single (0:Fin 2) 1 ∈ (MvPolynomial.C a * MvPolynomial.X (0:Fin 2)
          + MvPolynomial.C b * MvPolynomial.X (1:Fin 2) + MvPolynomial.C c
            : MvPolynomial (Fin 2) L).support := by
        rw [MvPolynomial.mem_support_iff, hcoeff0]; exact ha
      simpa using MvPolynomial.le_totalDegree hmem
    · have hmem : Finsupp.single (1:Fin 2) 1 ∈ (MvPolynomial.C a * MvPolynomial.X (0:Fin 2)
          + MvPolynomial.C b * MvPolynomial.X (1:Fin 2) + MvPolynomial.C c
            : MvPolynomial (Fin 2) L).support := by
        rw [MvPolynomial.mem_support_iff, hcoeff1]; exact hb
      simpa using MvPolynomial.le_totalDegree hmem
  refine MvPolynomial.irreducible_of_totalDegree_eq_one ?_ ?_
  · exact le_antisymm hle hge
  · -- every common divisor of all coefficients is a unit
    intro x hx
    rcases h with ha | hb
    · have hxa : x ∣ a := by
        have hh := hx (Finsupp.single (0:Fin 2) 1)
        rwa [hcoeff0] at hh
      exact isUnit_iff_ne_zero.mpr fun hx0 => by
        rcases hxa with ⟨y, hy⟩
        exact ha (by rw [hx0, zero_mul] at hy; exact hy)
    · have hxa : x ∣ b := by
        have hh := hx (Finsupp.single (1:Fin 2) 1)
        rwa [hcoeff1] at hh
      exact isUnit_iff_ne_zero.mpr fun hx0 => by
        rcases hxa with ⟨y, hy⟩
        exact hb (by rw [hx0, zero_mul] at hy; exact hy)

end Work.MotAS
