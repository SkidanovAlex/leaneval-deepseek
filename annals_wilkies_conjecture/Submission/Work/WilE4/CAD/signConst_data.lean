import Mathlib
import Submission.Work.WilE4.CAD.Proj
import Submission.Work.WilE4.CAD.resultant_spec
import Submission.Work.WilE4.Poly.spec_pderiv
import Submission.Work.WilE4.Ana.jet_separation
import Submission.Work.WilE4.CAD.type_local

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section

open Classical
open MvPolynomial Polynomial
open Work.WilE4 (rot spec)

namespace Work.WilE4.CAD

variable {m k : ℕ}

/-! ## The coefficient/resultant data

The hypotheses of `realized_const_of_signConst_bdd`, packaged as predicates on the family `P` and
the set `C`. -/

/-- The sign of every coefficient of index at most `degreeOf (last m)` is constant on `C`. -/
def CoeffConst (P : Fin k → MvPolynomial (Fin (m + 1)) ℝ) (C : Set (Fin m → ℝ)) : Prop :=
  ∀ i : Fin k, ∀ j : ℕ, j ≤ (P i).degreeOf (Fin.last m) → ∀ x ∈ C, ∀ x' ∈ C,
    SignType.sign ((spec (P i) x).coeff j) = SignType.sign ((spec (P i) x').coeff j)

/-- The sign of every resultant (with the degree pairs bounded by `degreeOf (last m)`) is constant
on `C`. -/
def ResConst (P : Fin k → MvPolynomial (Fin (m + 1)) ℝ) (C : Set (Fin m → ℝ)) : Prop :=
  ∀ i j : Fin k, ∀ a b : ℕ, a ≤ (P i).degreeOf (Fin.last m) →
    b ≤ (P j).degreeOf (Fin.last m) → ∀ x ∈ C, ∀ x' ∈ C,
    SignType.sign (Polynomial.resultant (spec (P i) x) (spec (P j) x) a b)
      = SignType.sign (Polynomial.resultant (spec (P i) x') (spec (P j) x') a b)

/-- The degree in the last variable bounds the `natDegree` of the specialisation: coefficients of
index `> degreeOf (last m)` vanish identically. -/
theorem coeff_spec_eq_zero_of_degreeOf_lt (P : MvPolynomial (Fin (m + 1)) ℝ)
    (x : Fin m → ℝ) {j : ℕ} (h : P.degreeOf (Fin.last m) < j) : (spec P x).coeff j = 0 := by
  rw [Work.WilE4.CAD.coeff_spec]
  have hF : (Work.WilE4.CAD.F P).coeff j = 0 := by
    rw [Work.WilE4.CAD.F]
    ext s
    rw [MvPolynomial.finSuccEquiv_coeff_coeff]
    have hdeg : (MvPolynomial.rename (rot m) P).degreeOf 0 = P.degreeOf (Fin.last m) := by
      have h2 := MvPolynomial.degreeOf_rename_of_injective (R := ℝ) (rot m).injective (Fin.last m)
        (p := P)
      rwa [Work.WilE4.rot_last] at h2
    have hlt : (MvPolynomial.rename (rot m) P).degreeOf (0 : Fin (m+1)) < (Finsupp.cons j s) 0 := by
      rw [hdeg, Finsupp.cons_zero]
      exact h
    exact MvPolynomial.notMem_support_iff.mp
      (MvPolynomial.notMem_support_of_degreeOf_lt (0 : Fin (m+1))
        (p := MvPolynomial.rename (rot m) P) (s := Finsupp.cons j s) hlt)
  rw [hF, map_zero]

/-- On `C`, a coefficient of index `≤ degreeOf (last m)` vanishes at `x` exactly when it vanishes
at `x'`. -/
theorem coeff_spec_eq_zero_iff {P : Fin k → MvPolynomial (Fin (m + 1)) ℝ} {C : Set (Fin m → ℝ)}
    (hcoeff : CoeffConst P C) {i : Fin k} {j : ℕ} (hj : j ≤ (P i).degreeOf (Fin.last m))
    {x x' : Fin m → ℝ} (hx : x ∈ C) (hx' : x' ∈ C) :
    (spec (P i) x).coeff j = 0 ↔ (spec (P i) x').coeff j = 0 := by
  have h := hcoeff i j hj x hx x' hx'
  rw [← sign_eq_zero_iff, h, sign_eq_zero_iff]

/-- The `natDegree` of the specialisation is constant on `C`. -/
theorem natDegree_spec_const {P : Fin k → MvPolynomial (Fin (m + 1)) ℝ} {C : Set (Fin m → ℝ)}
    (hcoeff : CoeffConst P C) {i : Fin k} {x x' : Fin m → ℝ} (hx : x ∈ C) (hx' : x' ∈ C) :
    (spec (P i) x).natDegree = (spec (P i) x').natDegree := by
  refine le_antisymm ?_ ?_
  · rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
    intro j hj
    by_cases hjd : j ≤ (P i).degreeOf (Fin.last m)
    · rw [(coeff_spec_eq_zero_iff hcoeff hjd hx hx').mpr]
      exact Polynomial.coeff_eq_zero_of_natDegree_lt hj
    · exact coeff_spec_eq_zero_of_degreeOf_lt (P i) x (not_le.mp hjd)
  · rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
    intro j hj
    by_cases hjd : j ≤ (P i).degreeOf (Fin.last m)
    · rw [(coeff_spec_eq_zero_iff hcoeff hjd hx hx').mp]
      exact Polynomial.coeff_eq_zero_of_natDegree_lt hj
    · exact coeff_spec_eq_zero_of_degreeOf_lt (P i) x' (not_le.mp hjd)

/-- The coefficients of the specialisation are continuous in the parameter. -/
theorem continuous_spec_coeff (P : MvPolynomial (Fin (m + 1)) ℝ) (j : ℕ) :
    Continuous fun x : Fin m → ℝ => (spec P x).coeff j := by
  simp only [Work.WilE4.CAD.coeff_spec]
  exact MvPolynomial.continuous_eval _

end Work.WilE4.CAD
