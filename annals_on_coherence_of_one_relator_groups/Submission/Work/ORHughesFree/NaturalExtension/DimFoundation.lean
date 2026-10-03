/-
# Foundational dimension theory for the duality `σ + τ ≥ 1`

This file collects the rank-theoretic facts that the proof of `supConstMain` needs.  The
mathematical content is developed in the *row convention*: for a matrix `A : Matrix (Fin n) (Fin m) R`
we regard `rk A` as the dimension of the left `R`-submodule of `R^m` spanned by the rows of `A`
(equivalently, the dimension of the image of the linear map `x ↦ x ᵥ* A`; this is the convention
of `Work.ORHughesFree.DivisionRank.exists_sylvesterRank_divisionRing`).

Main statements here:

* `rk_add_rk_one_sub_mul` — rank–nullity: for a matrix `A : n × m` with a weak (von Neumann)
  inverse `U` (`A * U * A = A`) over any ring with a Sylvester rank function,
  `rk A + rk (1 - A * U) = n`;
  the idempotent `1 - A * U` is the projection whose range is the row-kernel
  `{x | x ᵥ* A = 0}` of `A`.

The remaining ingredients are delegated / available elsewhere:

* `Work.ORHughesFree.NaturalExtension.dimOf_rows_eq_rk` : the bridge
  `dimOf rk (rows of A) = rk A`;
* `Work.ORHughesFree.NaturalExtension.dimOf_comp_le` : `dim (φ W) ≤ dim W`;
* `Work.ORHughesFree.NaturalExtension.dimOf_congr_span` : `dimOf` depends only on the span;
* `Work.ORHughesFree.NaturalExtension.dimOf_append_le` : subadditivity
  `dim (W + W') ≤ dim W + dim W'`;
* `Work.ORHughesFree.NaturalExtension.dimOf_mono` : monotonicity (proved);
* `Work.ORHughesFree.NaturalExtension.dimOf_bot_top` : `dim R^n = n` (proved);
* `Work.ORHughesFree.NaturalExtension.dimOf_principal` : `dim (R a) = rk a`;
* `Work.ORHughesFree.NaturalExtension.naturalExtension_trunc` : the natural extension is the
  ultralimit of the ranks of the truncations.
-/
import Mathlib
import Submission.Work.ORHughesFree.SylvesterRank
import Submission.Work.ORHughesFree.DivisionRank.rk_idempotent_add_compl

set_option autoImplicit false

universe u

namespace Work.ORHughesFree.NaturalExtension

open Matrix Work.ORHughesFree

/-- **Rank–nullity in the row convention.**  If `U` is a weak (von Neumann) inverse of `A`,
i.e. `A * U * A = A`, then `rk A + rk (1 - A * U) = n`.  The idempotent `1 - A * U` projects
onto the row-kernel `{x : Fin n → R | x ᵥ* A = 0}` of `A`. -/
theorem rk_add_rk_one_sub_mul {R : Type*} [Ring R] (rk : SylvesterRank R) {n m : ℕ}
    (A : Matrix (Fin n) (Fin m) R) (U : Matrix (Fin m) (Fin n) R) (hA : A * U * A = A) :
    rk.rk n m A + rk.rk n n (1 - A * U) = n := by
  have hidem : (A * U) * (A * U) = A * U := by
    rw [← Matrix.mul_assoc (A * U) A U, hA]
  have h1 : rk.rk n m A = rk.rk n n (A * U) := by
    refine le_antisymm ?_ ?_
    · calc rk.rk n m A = rk.rk n m (A * U * A) := by rw [hA]
        _ ≤ rk.rk n n (A * U) := rk.rk_mul_le_left (A * U) A
    · exact rk.rk_mul_le_left A U
  have h2 := Work.ORHughesFree.DivisionRank.rk_idempotent_add_compl rk (A * U) hidem
  rw [h1]
  exact h2

end Work.ORHughesFree.NaturalExtension
