import Mathlib
import Submission.Work.DSG4b.Defs

/-!
# DSG4b — lifting residue-field coefficients (EGA 0_III 10.3.1, step 2)

We build the residue-field enlargement of a regular local ring `R` without Cohen's structure
theorem.  The only thing one has to choose is a *set-theoretic* section of the residue map
`R → k = R/𝔪` (no ring section exists in general, e.g. there is no ring map `𝔽_p → ℤ_p`).

This file provides that section `Work.DSG4b.coeffLift`, normalised so that it fixes `0` and `1`,
together with the induced coefficientwise lift `Work.DSG4b.polyLift` of polynomials
`k[X] → R[X]`, which is again monic on monic input and whose coefficients map back to the
original ones.  These are the coefficients out of which the "root presentations"
`R[T] / (f)` of the extension steps are built (see `Submission/Work/DSG4b/Root.lean`).
-/

namespace Work.DSG4b

open Polynomial

universe u

noncomputable section

variable {R : Type u} [CommRing R] [IsLocalRing R]

/-- A set-theoretic section of the residue map `R → ResidueField R`, normalised so that it sends
`0` to `0` and `1` to `1`. -/
noncomputable def coeffLift (a : IsLocalRing.ResidueField R) : R := by
  classical
  exact if a = 0 then 0 else if a = 1 then 1
    else Classical.choose (IsLocalRing.residue_surjective a)

@[simp]
lemma coeffLift_zero : coeffLift (0 : IsLocalRing.ResidueField R) = 0 := by
  rw [coeffLift]; simp

@[simp]
lemma coeffLift_one : coeffLift (1 : IsLocalRing.ResidueField R) = 1 := by
  rw [coeffLift]; simp

lemma residue_coeffLift (a : IsLocalRing.ResidueField R) :
    IsLocalRing.residue R (coeffLift a) = a := by
  rw [coeffLift]
  split_ifs with h0 h1
  · rw [h0, map_zero]
  · rw [h1, map_one]
  · exact Classical.choose_spec (IsLocalRing.residue_surjective a)

lemma coeffLift_ne_zero {a : IsLocalRing.ResidueField R} (ha : a ≠ 0) : coeffLift a ≠ 0 := by
  intro h
  exact ha (by rw [← residue_coeffLift a, h, map_zero])

lemma coeffLift_injective : Function.Injective (coeffLift (R := R)) := by
  intro a b hab
  have h := congrArg (IsLocalRing.residue R) hab
  rwa [residue_coeffLift, residue_coeffLift] at h

/-- Coefficientwise lift of a polynomial along `coeffLift`. -/
noncomputable def polyLift (f : Polynomial (IsLocalRing.ResidueField R)) : Polynomial R :=
  Polynomial.ofFinsupp (AddMonoidAlgebra.ofCoeff
    (Finsupp.mapRange (coeffLift (R := R)) (coeffLift_zero (R := R))
      (Polynomial.toFinsupp f).coeff))

@[simp]
lemma polyLift_zero : polyLift (0 : Polynomial (IsLocalRing.ResidueField R)) = 0 := by
  rw [polyLift]
  simp

lemma coeff_polyLift (f : Polynomial (IsLocalRing.ResidueField R)) (n : ℕ) :
    (polyLift f).coeff n = coeffLift (f.coeff n) := by
  rw [polyLift, Polynomial.coeff_ofFinsupp, AddMonoidAlgebra.coeff_ofCoeff, Finsupp.mapRange_apply]
  rfl

lemma map_polyLift (f : Polynomial (IsLocalRing.ResidueField R)) :
    (polyLift f).map (IsLocalRing.residue R) = f := by
  ext n
  rw [Polynomial.coeff_map, coeff_polyLift, residue_coeffLift]

lemma polyLift_natDegree_le (f : Polynomial (IsLocalRing.ResidueField R)) :
    (polyLift f).natDegree ≤ f.natDegree := by
  refine Polynomial.natDegree_le_iff_coeff_eq_zero.mpr fun n hn => ?_
  rw [coeff_polyLift, Polynomial.coeff_eq_zero_of_natDegree_lt hn, coeffLift_zero]

lemma natDegree_polyLift {f : Polynomial (IsLocalRing.ResidueField R)} (hf : f ≠ 0) :
    (polyLift f).natDegree = f.natDegree := by
  refine le_antisymm (polyLift_natDegree_le f) ?_
  refine Polynomial.le_natDegree_of_ne_zero ?_
  rw [coeff_polyLift]
  exact coeffLift_ne_zero (Polynomial.leadingCoeff_ne_zero.mpr hf)

lemma leadingCoeff_polyLift {f : Polynomial (IsLocalRing.ResidueField R)} (hf : f ≠ 0) :
    (polyLift f).leadingCoeff = coeffLift f.leadingCoeff := by
  rw [Polynomial.leadingCoeff, natDegree_polyLift hf, ← Polynomial.coeff_natDegree,
    coeff_polyLift]

/-- The lifted polynomial is monic whenever the original is. -/
lemma polyLift_monic {f : Polynomial (IsLocalRing.ResidueField R)} (hf : f.Monic) :
    (polyLift f).Monic := by
  rcases eq_or_ne f 0 with rfl | hf0
  · rw [Polynomial.Monic, Polynomial.leadingCoeff] at hf
    exact absurd hf (by simp)
  · rw [Polynomial.Monic, leadingCoeff_polyLift hf0, hf.leadingCoeff, coeffLift_one]

end

end Work.DSG4b
