import Mathlib.NumberTheory.NumberField.House
import Submission.Dictionary
import Submission.Conjugates

/-!
# The minimal polynomial over ℤ of an algebraic integer

If `α` is integral over `ℤ` in a number field `K`, then
`minpoly ℤ α ∈ ℤ[X]` is monic, irreducible, has `α` as a root, and its
complex roots are exactly the conjugates of `α` (the values `σ α`).
-/

noncomputable section

open scoped Complex Polynomial
open Polynomial
open Submission.Conjugates

namespace Submission.Minpoly

variable {K : Type*} [Field K] [NumberField K]

/-- `minpoly ℚ α` is obtained from `minpoly ℤ α` by extending scalars to ℚ. -/
theorem minpoly_rat_eq_map_int (α : K) (hα : IsIntegral ℤ α) :
    minpoly ℚ α = (minpoly ℤ α).map (algebraMap ℤ ℚ) := by
  exact minpoly.isIntegrallyClosed_eq_field_fractions' (R := ℤ) (K := ℚ) hα

/-- `minpoly ℤ α` is monic. -/
theorem minpoly_int_monic (α : K) (hα : IsIntegral ℤ α) : (minpoly ℤ α).Monic :=
  minpoly.monic hα

/-- `minpoly ℤ α` is irreducible. -/
theorem minpoly_int_irreducible (α : K) (hα : IsIntegral ℤ α) : Irreducible (minpoly ℤ α) :=
  minpoly.irreducible hα

/-- `minpoly ℤ α` has `α` as a root. -/
theorem minpoly_int_aeval (α : K) : aeval α (minpoly ℤ α) = 0 := by
  exact minpoly.aeval ℤ α

/-- Roots of the ℤ-minimal polynomial are exactly the roots of the ℚ-minimal
polynomial (extension of scalars does not change roots in ℂ). -/
lemma rootSet_int_eq_rootSet_rat (α : K) (hα : IsIntegral ℤ α) :
    (minpoly ℤ α).rootSet ℂ = (minpoly ℚ α).rootSet ℂ := by
  classical
  rw [minpoly_rat_eq_map_int α hα]
  rw [rootSet_def, rootSet_def]
  apply congrArg (fun s : Multiset ℂ => (s.toFinset : Set ℂ))
  exact (aroots_map (T := ℤ) (S := ℚ) (R := ℂ) (minpoly ℤ α)).symm

/-- The complex roots of `minpoly ℤ α` are exactly the conjugates of `α`. -/
theorem rootSet_int_minpoly_eq_conjugateValues (α : K) (hα : IsIntegral ℤ α) :
    (minpoly ℤ α).rootSet ℂ = (conjugateValues α : Set ℂ) := by
  classical
  rw [rootSet_int_eq_rootSet_rat α hα]
  exact (Submission.Dictionary.conjugateValues_eq_rootSet α).symm

/-- The constant term of `minpoly ℤ α` is nonzero when `α` is integral and
nonzero. -/
theorem minpoly_int_eval_zero_ne_zero (α : K) (hα : IsIntegral ℤ α) (hα0 : α ≠ 0) :
    eval 0 (minpoly ℤ α) ≠ 0 := by
  classical
  intro he
  let p : ℤ[X] := minpoly ℤ α
  have hp0 : p.coeff 0 = 0 := by
    rw [Polynomial.coeff_zero_eq_eval_zero]
    exact he
  have hX : X ∣ p := Polynomial.X_dvd_iff.mpr hp0
  have hp_irr : Irreducible p := by
    simpa [p] using minpoly_int_irreducible α hα
  rcases hX with ⟨q, hpq⟩
  have hdisj : IsUnit (X : ℤ[X]) ∨ IsUnit q := hp_irr.isUnit_or_isUnit hpq
  rcases hdisj with hXunit | hqunit
  · exact False.elim (Polynomial.not_isUnit_X hXunit)
  · rcases (Polynomial.isUnit_iff.mp hqunit) with ⟨r, hr, hCq⟩
    have hp_eq : p = X * C r := by
      rw [hpq, ← hCq]
    have haeval : aeval α p = 0 := by
      simp [p]
    have hαmul : α * (algebraMap ℤ K r) = 0 := by
      have htmp : aeval α (X * C r) = 0 := by
        simpa [hp_eq] using haeval
      simpa [aeval_mul, aeval_X, aeval_C] using htmp
    have hmap_unit : IsUnit (algebraMap ℤ K r) := IsUnit.map (algebraMap ℤ K) hr
    have hmap_ne : algebraMap ℤ K r ≠ 0 := isUnit_iff_ne_zero.mp hmap_unit
    have hα0' : α = 0 := (mul_eq_zero.mp hαmul).resolve_right hmap_ne
    exact hα0 hα0'

end Submission.Minpoly

end
