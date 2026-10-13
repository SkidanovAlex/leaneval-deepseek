import Mathlib
import Submission.Work.WilkiesH.Tarski.definable_iff_polynomialSignSet
import Submission.Work.WilLibTS.TS.PolynomialEmptyInterior

namespace Work.WilkiesH.Omega

/-- **A semialgebraic set with empty interior lies in a nonzero polynomial's zero locus.**

By Tarski–Seidenberg (`definable_iff_polynomialSignSet`) a semialgebraic set is a finite Boolean
combination of polynomial sign conditions, and for such a set the "regular polynomial" of
`PolynomialSignSet.polynomial_of_empty_interior` vanishes on all of `S` as soon as `S` has empty
interior. -/
theorem semialg_subset_zeroLocus_of_interior_empty {n : ℕ} {S : Set (Fin n → ℝ)} (hS : WilkiesConjecture.IsSemialgebraic S) (hempty : interior S = ∅) : ∃ P : MvPolynomial (Fin n) ℝ, P ≠ 0 ∧ ∀ x ∈ S, MvPolynomial.eval x P = 0 := by
  have hPSS : Work.WilLibTS.TS.PolynomialSignSet (fun x : Fin n → ℝ => x) S :=
    Work.WilkiesH.Tarski.definable_iff_polynomialSignSet.mp hS
  exact Work.WilLibTS.TS.PolynomialSignSet.polynomial_of_empty_interior continuous_id hPSS hempty

end Work.WilkiesH.Omega
