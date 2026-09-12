import Mathlib
import Submission.GeoBridge
import Submission.UnitNormal

set_option autoImplicit false
set_option linter.style.haveILetI false
open MeasureTheory Matrix
open scoped BigOperators

noncomputable section

/-!
# The measurable unit normal of a matrix

Tikhomirov 2020, proof of Theorem A (item (1) of the incompressible-side
roadmap): for an `n × n` random matrix `A` with measurable entries, the
columns lifted to `E n := EuclideanSpace ℝ (Fin n)` are measurable, so the
Gram–Schmidt unit normal (`Submission.UnitNormal`) built from the first `n−1`
columns together with the standard orthonormal basis is a measurable random
vector, unit, and orthogonal to every one of the first `n−1` columns.

## Target statements

1. `colVec M j` is the `j`-th column of `M` as a vector of `E n`; measurable
   when the entries are measurable (`measurable_colVec`).
2. `stdBasisOrth n : OrthonormalBasis (Fin n) ℝ (E n)` is the standard basis
   (`EuclideanSpace.single j 1`), and `stdBasis (n) j := stdBasisOrth n j`.
3. `matrixUnitNormal A ω` is the unit normal of the first `n−1` columns of
   `A ω`; it is measurable (`measurable_matrixUnitNormal`), unit
   (`matrixUnitNormal_unit`), and orthogonal to those columns
   (`matrixUnitNormal_orthogonal_col`).
-/

namespace Submission.NormalVectorMatrix

open Submission.GeoBridge (E)
open Submission.UnitNormal.GramSchmidtExtension

/-- Column `j` of a matrix `M`, lifted to `E n`. -/
def colVec {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) (j : Fin n) : E n :=
  WithLp.toLp 2 (fun i : Fin n => M i j)

/-- Coefficient of a column vector. -/
lemma colVec_coeff {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) (j i : Fin n) :
    (colVec M j).ofLp i = M i j := by
  rfl

/-- The standard orthonormal basis of `E n` (the `single` family). -/
def stdBasisOrth (n : ℕ) : OrthonormalBasis (Fin n) ℝ (E n) :=
  OrthonormalBasis.ofRepr (LinearIsometryEquiv.refl ℝ (E n))

/-- The standard basis vectors. -/
def stdBasis (n : ℕ) (j : Fin n) : E n :=
  (stdBasisOrth n) j

/-- The standard basis vectors are the `single` vectors. -/
lemma stdBasis_apply {n : ℕ} (j : Fin n) :
    stdBasis n j = EuclideanSpace.single (𝕜 := ℝ) (i := j) (1 : ℝ) := by
  dsimp [stdBasis, stdBasisOrth]
  rw [OrthonormalBasis.coe_ofRepr]
  exact LinearIsometryEquiv.symm_apply_apply (LinearIsometryEquiv.refl ℝ (E n))
    (EuclideanSpace.single (𝕜 := ℝ) (i := j) (1 : ℝ))

/-- Column `j` of `A ω` is measurable when the entries are measurable. -/
lemma measurable_colVec {n : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (A : Ω → Matrix (Fin n) (Fin n) ℝ)
    (hA : ∀ i j : Fin n, Measurable (fun ω => A ω i j)) (j : Fin n) :
    Measurable (fun ω => colVec (A ω) j) := by
  dsimp [colVec]
  fun_prop

/-- The first `n−1` columns of `A ω` (as a family for the UnitNormal
construction; `emb : Fin (n−1) → Fin n` is the standard embedding). -/
def firstCols {n : ℕ} {Ω : Type*} (A : Ω → Matrix (Fin n) (Fin n) ℝ) :
    Fin (n - 1) → Ω → E n :=
  fun k ω => colVec (A ω) (Submission.GeoBridge.emb k)

/-- The measurable unit normal of the first `n−1` columns of `A ω`. -/
def matrixUnitNormal {n : ℕ} {Ω : Type*} (A : Ω → Matrix (Fin n) (Fin n) ℝ) :
    Ω → E n :=
  fun ω => unitNormal (E n) (stdBasis n) (fun k => firstCols A k ω)

/-- The matrix unit normal is measurable. -/
lemma measurable_matrixUnitNormal {n : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (A : Ω → Matrix (Fin n) (Fin n) ℝ)
    (hA : ∀ i j : Fin n, Measurable (fun ω => A ω i j)) :
    Measurable (matrixUnitNormal A) := by
  have hcol : ∀ k : Fin (n - 1), Measurable (fun ω => firstCols A k ω) := by
    intro k
    dsimp [firstCols]
    exact measurable_colVec A hA (Submission.GeoBridge.emb k)
  change Measurable (fun ω => unitNormal (E n) (stdBasis n) (fun k => firstCols A k ω))
  exact measurable_unitNormal (E n) (stdBasis n) hcol

/-- The matrix unit normal is a unit vector (for `n ≥ 1`). -/
lemma matrixUnitNormal_unit {n : ℕ} {Ω : Type*} (hn : 1 ≤ n)
    (A : Ω → Matrix (Fin n) (Fin n) ℝ) (ω : Ω) :
    ‖matrixUnitNormal A ω‖ = 1 := by
  dsimp [matrixUnitNormal, stdBasis]
  exact unitNormal_unit hn (E n) (stdBasisOrth n) (fun k => firstCols A k ω)

/-- The matrix unit normal is orthogonal to every one of the first `n−1`
columns. -/
lemma matrixUnitNormal_orthogonal_col {n : ℕ} {Ω : Type*} (k : Fin (n - 1))
    (A : Ω → Matrix (Fin n) (Fin n) ℝ) (ω : Ω) :
    inner ℝ (matrixUnitNormal A ω) (colVec (A ω) (Submission.GeoBridge.emb k)) = 0 := by
  dsimp [matrixUnitNormal, firstCols]
  exact unitNormal_orthogonal_col (E n) (stdBasis n) (fun k => colVec (A ω) (Submission.GeoBridge.emb k)) k

end Submission.NormalVectorMatrix
