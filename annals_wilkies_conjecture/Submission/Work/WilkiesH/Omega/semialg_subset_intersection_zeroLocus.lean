import Mathlib
import Submission.Work.WilkiesH.Omega.semialg_subset_zeroLocus_of_interior_empty
import Submission.Work.WilkiesH.Dim.dimLE_mono
import Submission.Work.WilkiesI.Basic

namespace Work.WilkiesH.Omega

/-- For a semialgebraic set `V` of dimension `≤ μ`, every projection of `V` to `μ + 1`
coordinates is a semialgebraic set with empty interior (this is exactly `DimLE`), hence lies
in the zero locus of a nonzero polynomial in `μ + 1` variables.  Choosing such a polynomial
for each embedding `e : Fin (μ + 1) ↪ Fin n` gives the required family `Q`. -/
theorem semialg_subset_intersection_zeroLocus {n μ : ℕ} {V : Set (Fin n → ℝ)} (hV : WilkiesConjecture.IsSemialgebraic V) (hdim : WilkiesDesign.DimLE V μ) : ∃ Q : (Fin (μ + 1) ↪ Fin n) → MvPolynomial (Fin (μ + 1)) ℝ, (∀ e, Q e ≠ 0) ∧ ∀ x ∈ V, ∀ e : Fin (μ + 1) ↪ Fin n, MvPolynomial.eval (fun i => x (e i)) (Q e) = 0 := by
  have h : ∀ e : Fin (μ + 1) ↪ Fin n, ∃ P : MvPolynomial (Fin (μ + 1)) ℝ,
      P ≠ 0 ∧ ∀ z ∈ (fun x : Fin n → ℝ => x ∘ e) '' V, MvPolynomial.eval z P = 0 :=
    fun e => semialg_subset_zeroLocus_of_interior_empty
      (Work.WilkiesI.definable_image_comp hV e) (hdim e)
  choose Q hQ using h
  exact ⟨Q, fun e => (hQ e).1, fun x hx e => (hQ e).2 (x ∘ e) ⟨x, hx, rfl⟩⟩

end Work.WilkiesH.Omega
