import Mathlib.Algebra.Module.ZLattice.Basic
import Submission.Commons.Lattice.Counting.finite_sublattices_gram_le

open Module
open scoped BigOperators

set_option autoImplicit false

/-!
# Finitely many sublattices with bounded Gram determinant

The set of `ℤ`-sublattices `M ≤ L` of `ℤ`-rank `r` that carry a generating family
`w : Fin r → E` (contained in `M`, spanning `M` over `ℤ`) whose Gram-matrix determinant
is at most `C ^ 2` is finite.

This is the finiteness fact used in the minimisation arguments of the reverse Minkowski
theorem: once the Gram determinant is bounded, only finitely many sublattices can occur,
so infima over sublattices are attained.

The counting core is `Commons.Lattice.Counting.finite_sublattices_gram_le`; we only have to
instantiate its bound parameter with `C ^ 2`.
-/

namespace Commons.Lattice.Minimizer

theorem finite_sublattices_det_le
    {n r : ℕ} (L : Submodule ℤ (EuclideanSpace ℝ (Fin n)))
    [DiscreteTopology L] [IsZLattice ℝ L] (C : ℝ) :
    {M : Submodule ℤ (EuclideanSpace ℝ (Fin n)) | M ≤ L ∧
      Module.finrank ℤ M = r ∧
      (∃ w : Fin r → EuclideanSpace ℝ (Fin n),
        (∀ i : Fin r, w i ∈ M) ∧
        (∀ ⦃x⦄, x ∈ M → x ∈ Submodule.span ℤ (Set.range w)) ∧
        (Matrix.gram ℝ w).det ≤ C ^ 2)}.Finite := by
  simpa using
    (Commons.Lattice.Counting.finite_sublattices_gram_le (n := n) (r := r) (L := L) (X := C ^ 2))

end Commons.Lattice.Minimizer
