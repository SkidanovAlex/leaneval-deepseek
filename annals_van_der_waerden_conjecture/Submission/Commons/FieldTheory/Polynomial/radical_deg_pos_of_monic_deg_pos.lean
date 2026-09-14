import Mathlib
import Submission.Commons.FieldTheory.Polynomial.monic_index_ge_card_le

open Polynomial

namespace Commons.FieldTheory.Polynomial

noncomputable section

/-- The radical of a nonconstant monic polynomial over a field is again
nonconstant. -/
theorem radical_deg_pos_of_monic_deg_pos {F : Type*} [Field F] [DecidableEq F] (f : F[X])
    (hf : f.Monic) (hdeg : 1 ≤ f.natDegree) :
    1 ≤ (UniqueFactorizationMonoid.radical f).natDegree := by
  let r := UniqueFactorizationMonoid.radical f
  have hmonic_r : r.Monic := radical_monic f hf
  have hr0 : r ≠ 0 := UniqueFactorizationMonoid.radical_ne_zero (a := f)
  have hr_ne_one : r ≠ 1 := by
    intro h1
    have hfac : f = 0 ∨ IsUnit f :=
      (UniqueFactorizationMonoid.radical_eq_one_iff (a := f)).mp h1
    rcases hfac with hf0 | hu
    · exact hf.ne_zero hf0
    · have hf1 : f = 1 := (Polynomial.Monic.isUnit_iff hf).mp hu
      have hd : f.natDegree = 0 := by
        rw [hf1]
        simp
      omega
  by_contra hdeg'
  have hn0 : r.natDegree = 0 := by
    have hlt : r.natDegree < 1 := not_le.mp hdeg'
    omega
  have hdeg0 : r.degree = 0 := by
    rw [degree_eq_natDegree hr0]
    simp [hn0]
  have h1 : r = 1 := (Polynomial.Monic.degree_le_zero_iff_eq_one hmonic_r).mp (by
    rw [hdeg0])
  exact hr_ne_one h1

end

end Commons.FieldTheory.Polynomial
