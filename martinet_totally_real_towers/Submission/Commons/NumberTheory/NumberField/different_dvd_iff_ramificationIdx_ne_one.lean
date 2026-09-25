import Mathlib.Algebra.AffineMonoid.Basic
import Mathlib.RingTheory.DedekindDomain.Different
import Mathlib.NumberTheory.NumberField.Basic

open scoped Classical NumberField

noncomputable section

namespace Commons.NumberTheory.NumberField

/-- A prime of the ring of integers divides the different ideal iff it is
ramified (i.e. has ramification index different from one). -/
theorem different_dvd_iff_ramificationIdx_ne_one (K : Type*) [Field K] [NumberField K]
    (P : Ideal (𝓞 K)) [P.IsPrime] :
    P ∣ differentIdeal ℤ (𝓞 K) ↔ P.ramificationIdx ℤ ≠ 1 := by
  rw [dvd_differentIdeal_iff (A := ℤ) (B := 𝓞 K) (P := P)]
  exact (not_iff_not.mpr (Ideal.ramificationIdx_eq_one_iff (q := P) (R := ℤ))).symm

end Commons.NumberTheory.NumberField