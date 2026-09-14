import Submission.Commons.Lattice.Counting.finite_sublattices_int_count

set_option autoImplicit false

noncomputable section

namespace Commons.Lattice.Counting

theorem finite_sublattices_int {n r : ℕ} (B : ℝ) :
    {M : Submodule ℤ (Fin n → ℤ) | Module.finrank ℤ M = r ∧
      (∃ A : Matrix (Fin n) (Fin r) ℤ,
        (∀ j : Fin r, (fun i => A i j) ∈ M) ∧
        (∀ ⦃x⦄, x ∈ M → x ∈ Submodule.span ℤ (Set.range (fun j : Fin r => (fun i => A i j)))) ∧
        (((A.map (fun z : ℤ => (z : ℝ))).transpose *
            (A.map (fun z : ℤ => (z : ℝ)))).det ≤ B))}.Finite := by
  exact finite_sublattices_int_count (n := n) (r := r) (B := B)

end Commons.Lattice.Counting

end
