import Mathlib
import Submission.Work.EKLContract.Defs

/-!
# `SL₃(ℝ)` is a standard Borel space, with second countable topology

The ambient space of the Einsiedler–Katok–Lindenstrauss argument is `G = SL₃(ℝ)`, realized in
`Work.EKLContract.Defs` as `Matrix.SpecialLinearGroup (Fin 3) ℝ`, i.e. the subtype
`{A : Matrix (Fin 3) (Fin 3) ℝ // A.det = 1}` of the space of `3 × 3` real matrices, with the
subspace topology and the Borel σ-algebra (the `MeasurableSpace` instance of `Defs.lean`).

Two topological facts are needed downstream (in particular for the standard-Borel/Pólya
machinery of `P_X3`, where one needs a Polish space in order to use measurable selectors,
disintegration, and Borel isomorphisms):

* `G` is second countable;
* `G` is a standard Borel space.

Both are instances of the general fact that a matrix space is the product of its entries (so a
countable product of second countable spaces) and that `SL_n` is a closed subspace of it
(`det = 1`).  Mathlib has all the ingredients, but type class search cannot find the instance
for `Matrix m n R`: `Matrix` is a plain `def` (equal to `m → n → R`) which instance search does
not unfold, so `SecondCountableTopology (Matrix m n R)` and `PolishSpace (Matrix m n R)` are not
synthesised.  The two helper lemmas below supply them by unfolding the definition explicitly.

Mathlib's `PolishSpace` class extends `SecondCountableTopology`, so `PolishSpace G` alone already
yields the second conjunct of the statement.
-/

open Matrix

namespace Work.EKLContract.Lemmas

/-- The (product) topology on `Matrix m n R` is second countable whenever the index types are
countable and `R` is second countable.

Mathlib proves this for the *product* `m → n → R`, and `Matrix m n R` is definitionally that
product, but instance search does not unfold the `def Matrix`, so the instance has to be
transported by hand. -/
lemma secondCountableTopology_matrix {m n R : Type*} [TopologicalSpace R]
    [SecondCountableTopology R] [Countable m] [Countable n] :
    SecondCountableTopology (Matrix m n R) :=
  inferInstanceAs (SecondCountableTopology (m → n → R))

/-- `Matrix m n R` is Polish when `m`, `n` are countable and `R` is Polish, being a countable
product of Polish spaces.  Again Mathlib only has this for the product `m → n → R`. -/
lemma polishSpace_matrix {m n R : Type*} [TopologicalSpace R] [PolishSpace R] [Countable m]
    [Countable n] : PolishSpace (Matrix m n R) :=
  inferInstanceAs (PolishSpace (m → n → R))

/-- `SL_n(R)` is a closed subspace of the matrix space (it is the locus `det = 1`), hence Polish
as soon as the matrix space is. -/
lemma polishSpace_specialLinearGroup {n R : Type*} [Fintype n] [DecidableEq n] [CommRing R]
    [TopologicalSpace R] [IsTopologicalRing R] [Countable n] [PolishSpace R] :
    PolishSpace (Matrix.SpecialLinearGroup n R) := by
  have : PolishSpace (Matrix n n R) := polishSpace_matrix
  exact (isClosed_eq (continuous_id.matrix_det (n := n) (R := R)) continuous_const).polishSpace

/-- `SL₃(ℝ)` is a standard Borel space (with its Borel σ-algebra) and has second countable
topology. -/
theorem SL3Topology :
    StandardBorelSpace Work.EKLContract.SL3 ∧
    SecondCountableTopology Work.EKLContract.SL3 := by
  have : PolishSpace (Matrix.SpecialLinearGroup (Fin 3) ℝ) :=
    polishSpace_specialLinearGroup
  exact ⟨inferInstance, inferInstance⟩

end Work.EKLContract.Lemmas
