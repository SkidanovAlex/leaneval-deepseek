import Mathlib
import Submission.Work.DSCOH.Chart
import Submission.Work.DSCOH.shift_gradedSMul
import Submission.Work.DSCOH.dsMonBasis
import Submission.Work.DSCOH.shiftVanishingCrux
import Submission.Work.DSCOH.chartCech_exact_isZero_homology

namespace Work.DSCOH

/-- **Vanishing of the middle cohomology of the chart Čech complex of `S(-d)`.**

The chart Čech complex of the shifted free module `S(-d) = shift d` over `A[X₀,…,X_{n-1}]` is
exact in the degrees `0 < q` with `q + 1 < n`: this is Serre's/Bott's vanishing of the
intermediate cohomology of `O(-d)` on `ℙ^{n-1}`.  The range is sharp: the top cohomology
`H^{n-1}` is nonzero for `d ≥ n`.

The proof decomposes the complex, in the monomial coordinates of the chart localizations
(`locAt_monomial_basis`), into the simplex complexes attached to the Laurent exponents `β` with
`Σβ = -d` (`simplex_cech_lift_level`), and glues the local solutions
(`exists_boundary_of_coeffs`) using the cycle conditions in coordinates
(`cycle_piece_conditions`). -/
theorem chartCech_shift_vanishing {A : Type*} [CommRing A] {n : ℕ} (d q : ℕ)
    [SetLike.GradedSMul (homSub A n) (shift (A := A) (n := n) d)]
    (hq : 0 < q) (hqn : q + 1 < n) :
    CategoryTheory.Limits.IsZero ((chartCech (A := A) (n := n) (M := Poly A n)
      (shift (A := A) (n := n) d)).homology q) := by
  obtain ⟨B, _, hB2, hB3⟩ := dsMonBasis (A := A) (n := n)
  have hex : LinearMap.range (cechDiff (A := A) (n := n) (M := Poly A n)
        (shift (A := A) (n := n) d) (q - 1)) =
      LinearMap.ker (cechDiff (A := A) (n := n) (M := Poly A n)
        (shift (A := A) (n := n) d) ((q - 1) + 1)) :=
    chartCechShift_exact (d := d) (q - 1) (by omega) B hB2 (fun S => hB3 S d)
  have hgoal : CategoryTheory.Limits.IsZero ((chartCech (A := A) (n := n) (M := Poly A n)
      (shift (A := A) (n := n) d)).homology ((q - 1) + 1)) :=
    chartCech_exact_isZero_homology (A := A) (n := n) (M := Poly A n)
      (shift (A := A) (n := n) d) (q - 1) hex
  rwa [show (q - 1) + 1 = q from by omega] at hgoal

end Work.DSCOH
