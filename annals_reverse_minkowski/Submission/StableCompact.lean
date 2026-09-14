import Mathlib
import Submission.LatticeParam
import Submission.DetQuot
import Submission.StableLattices
import Submission.Uncrossing
import Submission.MainStable
import Submission.StablePrecompact
import Submission.Commons.Lattice.Minkowski.bounded_basis_covolume_one
import Submission.Commons.LinearAlgebra.Matrix.isCompact_det_one_bounded_cols

open Module Real Matrix
open Submission.LatticeParam
open scoped Real BigOperators
set_option autoImplicit false
set_option maxHeartbeats 800000

/-!
# (P2) bounded-representative compactness: determinant bridge

P2 turns the [B-ii] bounded-basis datum (L88, via `StablePrecompact`) into a statement
over a COMPACT family of basis matrices.  The bridge proved here: for a full-rank lattice
`ℒ` with `ℤ`-basis `b`, the basis matrix satisfies `|det (basisMatrix b)| = det ℒ`
(so a stable lattice, `det ℒ = 1`, has `|det| = 1` representatives, and the whole stable
family maps into the compact set `{A : ‖columns A‖ ≤ C ∧ |det A| = 1}`).  The steps are
the Gram-matrix identification `(basisMatrix b)ᵀ • basisMatrix b = gram (values)`
(columns of the basis matrix are the coordinate vectors, whose inner products are the
inner products of the values), `det(gram) = (det ℒ)²` (from
`DetQuot.determinant_eq_sqrt_gram` reindexed to the actual basis), and the square-root
comparison.
-/

noncomputable section
namespace Submission.StableCompact

variable {m : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin m)

/-- The columns of a matrix, as vectors of `E` (column `i` has coordinates `A j i`). -/
def cols (A : Matrix (Fin m) (Fin m) ℝ) : Fin m → E :=
  fun i => WithLp.toLp 2 (fun j : Fin m => A j i)

/-- The matrix whose columns are the coordinate vectors `v i`. -/
def matrixOfCols (v : Fin m → E) : Matrix (Fin m) (Fin m) ℝ :=
  fun j i => (v i) j

/-- The columns of the basis matrix are the basis values themselves. -/
lemma cols_basisMatrix {ℒ : Submodule ℤ E} (b : Module.Basis (Fin m) ℤ ℒ) (i : Fin m) :
    cols (basisMatrix b) i = ((b i : ℒ) : E) := by
  ext j
  simp [cols, Submission.LatticeParam.basisMatrix]

/-- Reconstructing a lattice from its columns: `latticeOfMatrix (matrixOfCols (cols A)) =
latticeOfMatrix A`, and the column representation is left-inverse on matrices. -/
lemma matrixOfCols_cols (A : Matrix (Fin m) (Fin m) ℝ) : matrixOfCols (cols A) = A := by
  ext j i
  simp [matrixOfCols, cols]

/-- The squared-transpose product of the basis matrix is the Gram matrix of the basis
values: the columns of `basisMatrix b` are the coordinate vectors of the (orthonormal-
coordinate) values, and `E`-inner products equal coordinate dot products. -/
lemma basisMatrix_transpose_mul_eq_gram {ℒ : Submodule ℤ E} (b : Module.Basis (Fin m) ℤ ℒ) :
    (basisMatrix b).transpose * basisMatrix b =
      Matrix.gram ℝ (fun i : Fin m => ((b i : ℒ) : E)) := by
  ext i j
  simp [Matrix.mul_apply, Submission.LatticeParam.basisMatrix, PiLp.inner_apply, mul_comm,
    mul_left_comm, mul_assoc]

/-- `det(gram (values)) = (det (basisMatrix b))²`. -/
lemma det_gram_eq_det_basisMatrix_sq {ℒ : Submodule ℤ E} (b : Module.Basis (Fin m) ℤ ℒ) :
    (Matrix.gram ℝ (fun i : Fin m => ((b i : ℒ) : E))).det =
      ((basisMatrix b).det) ^ 2 := by
  have h := congrArg Matrix.det (basisMatrix_transpose_mul_eq_gram b)
  rw [Matrix.det_mul, Matrix.det_transpose] at h
  simpa [pow_two, mul_comm] using h.symm

/-- `det ℒ = √(det (gram of the values of any ℤ-basis b))` (full rank). -/
lemma determinant_eq_sqrt_gram_of_basis {ℒ : Submodule ℤ E} [DiscreteTopology ℒ]
    (hℒ : IsZLattice ℝ ℒ) (b : Module.Basis (Fin m) ℤ ℒ) :
    ReverseMinkowski.determinant ℒ =
      Real.sqrt ((Matrix.gram ℝ (fun i : Fin m => ((b i : ℒ) : E))).det) := by
  classical
  haveI : Module.Free ℤ ℒ := instModuleFree_of_discrete_submodule ℒ
  haveI : Module.Finite ℤ ℒ := instModuleFinite_of_discrete_submodule ℒ
  exact Submission.Uncrossing.det_eq_sqrt_gram_any_basis (L := ℒ) b

/-- **Determinant bridge**: `|det (basisMatrix b)| = det ℒ` for any `ℤ`-basis of a
full-rank lattice. -/
theorem abs_det_basisMatrix_eq_det {ℒ : Submodule ℤ E} [DiscreteTopology ℒ]
    (hℒ : IsZLattice ℝ ℒ) (b : Module.Basis (Fin m) ℤ ℒ) :
    |(basisMatrix b).det| = ReverseMinkowski.determinant ℒ := by
  classical
  have hdet : ReverseMinkowski.determinant ℒ =
      Real.sqrt ((Matrix.gram ℝ (fun i : Fin m => ((b i : ℒ) : E))).det) :=
    determinant_eq_sqrt_gram_of_basis hℒ b
  have hg0 : 0 ≤ (Matrix.gram ℝ (fun i : Fin m => ((b i : ℒ) : E))).det := by
    exact (Matrix.posSemidef_gram ℝ (fun i : Fin m => ((b i : ℒ) : E))).det_nonneg
  have hsq : (basisMatrix b).det ^ 2 = ReverseMinkowski.determinant ℒ ^ 2 := by
    calc
      (basisMatrix b).det ^ 2
          = (Matrix.gram ℝ (fun i : Fin m => ((b i : ℒ) : E))).det :=
            (det_gram_eq_det_basisMatrix_sq b).symm
      _ = (Real.sqrt ((Matrix.gram ℝ (fun i : Fin m => ((b i : ℒ) : E))).det)) ^ 2 :=
            (Real.sq_sqrt hg0).symm
      _ = ReverseMinkowski.determinant ℒ ^ 2 := by rw [hdet]
  have hpos : 0 < ReverseMinkowski.determinant ℒ := Submission.Uncrossing.det_pos (L := ℒ)
  have habs : |(basisMatrix b).det| = |ReverseMinkowski.determinant ℒ| :=
    (sq_eq_sq_iff_abs_eq_abs ((basisMatrix b).det) (ReverseMinkowski.determinant ℒ)).mp hsq
  rwa [abs_of_pos hpos] at habs

/-- For a stable lattice, the basis matrix of any `ℤ`-basis has determinant `±1`. -/
theorem det_basisMatrix_eq_one_or_neg_one_of_stable {ℒ : Submodule ℤ E} [DiscreteTopology ℒ]
    (hℒ : IsZLattice ℝ ℒ) (hSt : Submission.StableLattices.Stable ℒ)
    (b : Module.Basis (Fin m) ℤ ℒ) :
    (basisMatrix b).det = 1 ∨ (basisMatrix b).det = -1 := by
  classical
  have habs : |(basisMatrix b).det| = ReverseMinkowski.determinant ℒ :=
    abs_det_basisMatrix_eq_det hℒ b
  have h1 : |(basisMatrix b).det| = 1 := by
    rwa [Submission.StableLattices.det_eq_one_of_stable hSt] at habs
  rcases (abs_eq (by norm_num : (0 : ℝ) ≤ 1)).mp h1 with h | h
  · exact Or.inl h
  · exact Or.inr h

/-! ## (P2) bounded det-one representative datum -/

/-- **P2 core (bounded-representative half)**: under the L88 bounded-basis hypothesis, every
stable full-rank rank-`m` lattice is `latticeOfMatrix A` for a matrix `A` with `|det A| = 1`
and all column norms `≤ C` (the columns are a bounded `ℤ`-basis whose matrix determinant is
`±1` by stability).  Together with the compactness of
`{A : |det A| = 1 ∧ ∀ i, ‖cols A i‖ ≤ C}` (delegated to the commons:
`Commons.LinearAlgebra.Matrix.isCompact_det_one_bounded_cols`) this is the [B-ii] datum. -/
theorem stable_bounded_detOne_representative (C : ℝ)
    (hbasis : ∀ (ℒ : Submodule ℤ E) [DiscreteTopology ℒ],
      Submission.StableLattices.Stable ℒ → Module.finrank ℤ ℒ = m →
      ∃ b : Module.Basis (Fin m) ℤ ℒ,
        ∀ i : Fin m, ‖((b i : ℒ) : E)‖ ≤ C) :
    ∀ (ℒ : Submodule ℤ E) [DiscreteTopology ℒ],
      Submission.StableLattices.Stable ℒ → Module.finrank ℤ ℒ = m →
      ∃ A : Matrix (Fin m) (Fin m) ℝ,
        |A.det| = 1 ∧ (∀ i : Fin m, ‖cols A i‖ ≤ C) ∧
        latticeOfMatrix A = ℒ := by
  classical
  intro ℒ _hDT hSt hfin
  rcases hbasis ℒ hSt hfin with ⟨b, hbnd⟩
  refine ⟨basisMatrix b, ?_⟩
  constructor
  · have hℒ : IsZLattice ℝ ℒ := Submission.MainStable.isZLattice_of_finrank (n := m) ℒ hfin
    rcases det_basisMatrix_eq_one_or_neg_one_of_stable (ℒ := ℒ) hℒ hSt b with h1 | h2
    · rw [h1]; norm_num
    · rw [h2]; norm_num
  · constructor
    · intro i
      have hcol : cols (basisMatrix b) i = ((b i : ℒ) : E) := cols_basisMatrix b i
      rw [hcol]
      exact hbnd i
    · exact latticeOfMatrix_basisMatrix b

/-- **P2 closed: the stable family is contained in one compact matrix set.**  For every
ambient dimension there is a compact set `K` of matrices such that every stable full-rank
rank-`m` lattice is `latticeOfMatrix A` for some `A ∈ K` — the compactness datum that, with
the P3 continuity of `ℒ ↦ γ_{1/t}(V(ℒ))`, yields the global-minimizer machinery. -/
theorem stable_lattices_in_compact_set :
    ∃ (K : Set (Matrix (Fin m) (Fin m) ℝ)), IsCompact K ∧
      ∀ (ℒ : Submodule ℤ E) [DiscreteTopology ℒ],
        Submission.StableLattices.Stable ℒ → Module.finrank ℤ ℒ = m →
        ∃ A : Matrix (Fin m) (Fin m) ℝ, A ∈ K ∧ latticeOfMatrix A = ℒ := by
  classical
  rcases Commons.Lattice.Minkowski.bounded_basis_covolume_one m with ⟨C, hCprop⟩
  let K : Set (Matrix (Fin m) (Fin m) ℝ) :=
    {A | |A.det| = 1 ∧ ∀ i : Fin m, ‖cols A i‖ ≤ C}
  refine ⟨K, ?_, ?_⟩
  · -- compactness of K (L90)
    simpa [K, cols] using (Commons.LinearAlgebra.Matrix.isCompact_det_one_bounded_cols (m := m) (C := C))
  · -- every stable lattice is generated by a matrix in K (L88 + the determinant bridge)
    have hbasis : ∀ (ℒ : Submodule ℤ E) [DiscreteTopology ℒ],
        Submission.StableLattices.Stable ℒ → Module.finrank ℤ ℒ = m →
        ∃ b : Module.Basis (Fin m) ℤ ℒ,
          ∀ i : Fin m, ‖((b i : ℒ) : E)‖ ≤ C := by
      intro ℒ _hDT hSt hfin
      have hℒ : IsZLattice ℝ ℒ := Submission.MainStable.isZLattice_of_finrank (n := m) ℒ hfin
      exact hCprop ℒ hℒ (Submission.StablePrecompact.stable_meets_delegation_hypotheses (m := m) ℒ hfin hSt).1
        (Submission.StablePrecompact.stable_meets_delegation_hypotheses (m := m) ℒ hfin hSt).2
    intro ℒ _hDT hSt hfin
    rcases stable_bounded_detOne_representative (C := C) hbasis ℒ hSt hfin with ⟨A, hdet, hcol, hL⟩
    refine ⟨A, ?_, hL⟩
    exact ⟨hdet, hcol⟩

end Submission.StableCompact