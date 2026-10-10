import Mathlib

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.MotK.TGen

/-- **A cubic with a unit leading coefficient and no root in the coefficient ring is irreducible.**  For a domain `R` and `f ∈ R[X]` with `natDegree f = 3`, `f.coeff 3` a unit of `R` and `f` having no root in `R`, `f` is irreducible.

Route.  `¬ IsUnit f`: otherwise `Polynomial.natDegree_eq_zero_of_isUnit` gives `natDegree f = 0 ≠ 3`.  Suppose `f = a * b` with `a`, `b` nonunits; then `a`, `b ≠ 0` (as `f ≠ 0`), so `a.natDegree + b.natDegree = 3` (`Polynomial.natDegree_mul`) and, after exchanging `a` and `b` if necessary, `a.natDegree ≤ 1`.  Now `f.coeff 3 = a.leadingCoeff * b.leadingCoeff` (`Polynomial.coeff_natDegree`, `Polynomial.leadingCoeff_mul`), which is a unit, so `a.leadingCoeff` is a unit of `R` (a divisor of a unit is a unit: `IsUnit.dvd` plus `isUnit_of_dvd_one`).  If `a.natDegree = 0`, then `a = C a.leadingCoeff` (`Polynomial.eq_C_of_natDegree_eq_zero`) is a unit of `R[X]` (`Polynomial.isUnit_C`), contradiction.  If `a.natDegree = 1`, then `a = C (a.coeff 1) * X + C (a.coeff 0)` (`Polynomial.eq_X_add_C_of_natDegree_le_one`) and `r = -(↑u⁻¹ * a.coeff 0)`, where `u` is a unit with `↑u = a.coeff 1 = a.leadingCoeff`, satisfies `a.eval r = 0`; hence `f.eval r = 0` (`Polynomial.eval_mul`), contradicting `hno r`. -/
theorem CubTCubicIrred {R : Type*} [CommRing R] [IsDomain R] {f : Polynomial R}
    (hdeg : f.natDegree = 3) (hunit : IsUnit (f.coeff 3)) (hno : ∀ r : R, f.eval r ≠ 0) :
    Irreducible f := by
  have hf0 : f ≠ 0 := by
    rintro rfl
    simp at hdeg
  have hcoeff3 : f.coeff 3 = f.leadingCoeff := by
    rw [← hdeg, Polynomial.coeff_natDegree]
  have huniunit : IsUnit f.leadingCoeff := hcoeff3 ▸ hunit
  refine ⟨?_, ?_⟩
  · intro hu
    have h0 := Polynomial.natDegree_eq_zero_of_isUnit hu
    omega
  · intro a b hab
    by_contra hcon
    rw [not_or] at hcon
    obtain ⟨ha, hb⟩ := hcon
    have ha0 : a ≠ 0 := by
      rintro rfl; rw [zero_mul] at hab; exact hf0 hab
    have hb0 : b ≠ 0 := by
      rintro rfl; rw [mul_zero] at hab; exact hf0 hab
    have key : ∀ (a b : Polynomial R), a ≠ 0 → b ≠ 0 → f = a * b →
        a.natDegree ≤ 1 → IsUnit a := by
      intro a b ha0 hb0 hab ha1
      have hleadeq : f.leadingCoeff = a.leadingCoeff * b.leadingCoeff := by
        rw [hab, Polynomial.leadingCoeff_mul]
      have hprod : IsUnit (a.leadingCoeff * b.leadingCoeff) := hleadeq ▸ huniunit
      have hprod1 : (a.leadingCoeff * b.leadingCoeff) ∣ (1 : R) := hprod.dvd
      have halc : IsUnit a.leadingCoeff :=
        isUnit_of_dvd_one (dvd_trans ⟨b.leadingCoeff, rfl⟩ hprod1)
      have hcase : a.natDegree = 0 ∨ a.natDegree = 1 := by omega
      rcases hcase with h0 | h1
      · have h0lead : a.coeff 0 = a.leadingCoeff := by
          rw [← h0, Polynomial.coeff_natDegree]
        rw [Polynomial.eq_C_of_natDegree_eq_zero h0, Polynomial.isUnit_C]
        rwa [h0lead]
      · have h1lead : a.coeff 1 = a.leadingCoeff := by
          rw [← h1, Polynomial.coeff_natDegree]
        have haeq : a = Polynomial.C (a.coeff 1) * Polynomial.X + Polynomial.C (a.coeff 0) :=
          Polynomial.eq_X_add_C_of_natDegree_le_one ha1
        have h1unit : IsUnit (a.coeff 1) := h1lead ▸ halc
        obtain ⟨u, hu⟩ := h1unit
        set r : R := -(↑(u⁻¹) * a.coeff 0) with hr
        have haroot : a.eval r = 0 := by
          rw [haeq, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
            Polynomial.eval_X, Polynomial.eval_C, ← hu, hr, mul_neg, ← mul_assoc,
            Units.mul_inv, one_mul, neg_add_cancel]
        exact absurd (show f.eval r = 0 by
          rw [hab, Polynomial.eval_mul, haroot, zero_mul]) (hno r)
    have hd : a.natDegree + b.natDegree = 3 := by
      rw [← Polynomial.natDegree_mul ha0 hb0, ← hab, hdeg]
    have hcase : a.natDegree ≤ 1 ∨ b.natDegree ≤ 1 := by omega
    rcases hcase with ha1 | hb1
    · exact ha (key a b ha0 hb0 hab ha1)
    · rw [mul_comm] at hab
      exact hb (key b a hb0 ha0 hab hb1)

end Work.MotK.TGen
