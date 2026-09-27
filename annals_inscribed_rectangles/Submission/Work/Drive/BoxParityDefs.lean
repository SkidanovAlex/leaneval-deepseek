import Mathlib
import Submission.Work.Drive.Interfaces

/-!
# Definitions for `boxParity`

Setup for the mod-2 boundary parity statement `Submission.Drive.ParityProp`.

* `Amb m = ℝ^{m+1}` is the ambient space, `Tgt m = ℝ^m` the target of the cutting function `F`;
* `cofactorVec T` is the "cross product" (cofactor) vector of a linear map `T : ℝ^{m+1} → ℝ^m`:
  it spans `ker T` when `T` is surjective, and vanishes exactly when `T` is not surjective.  Its
  `j`-th component is the signed maximal minor of the matrix of `T` with the `j`-th row deleted.
* `cofactorVectorF F x = cofactorVec (fderiv ℝ F x)` is the tangential line field along `F⁻¹(0)`.
* `boxBump m` is a smooth bump function which equals `1` on the unit box `[0,1]^{m+1}` (in fact on a
  neighbourhood of it) and has compact support; `flowField F` is the bounded, compactly supported
  tangential field `boxBump m · cofactorVectorF F / √(1 + ‖cofactorVectorF F‖²)`.  Its flow lines
  preserve the level sets of `F` (and hence the zero set), and on the unit box it is a positive
  multiple of the cofactor field.
* `zeroSet F` and `bdyZeros F` are the zero set of `F` in the box and on its boundary.
-/

namespace Work.Drive

open scoped ContDiff Topology
open Set

open Submission.Drive

noncomputable section

/-- The ambient space `ℝ^{m+1}`. -/
abbrev Amb (m : ℕ) := EuclideanSpace ℝ (Fin (m + 1))

/-- The target space `ℝ^m`. -/
abbrev Tgt (m : ℕ) := EuclideanSpace ℝ (Fin m)

/-- The matrix of `T` in the standard basis (rows indexed by the target coordinates). -/
def cofactorMatrix {m : ℕ} (T : Amb m →L[ℝ] Tgt m) : Matrix (Fin (m + 1)) (Fin m) ℝ :=
  fun j i => T (EuclideanSpace.single j 1) i

/-- The **cofactor vector** of a linear map `T : ℝ^{m+1} → ℝ^m`: the vector whose `j`-th component
is the signed maximal minor of the matrix of `T` with the `j`-th row deleted.  It spans `ker T`
when `T` is surjective and is zero otherwise. -/
def cofactorVec {m : ℕ} (T : Amb m →L[ℝ] Tgt m) : Amb m :=
  WithLp.toLp 2 fun j : Fin (m + 1) =>
    (-1 : ℝ) ^ (j : ℕ) * ((cofactorMatrix T).submatrix (Fin.succAbove j) id).det

/-- The tangential line field along the zero set of `F`: the cofactor vector of the derivative. -/
def cofactorVectorF {m : ℕ} (F : Amb m → Tgt m) (x : Amb m) : Amb m :=
  cofactorVec (fderiv ℝ F x)

/-- A smooth bump function which equals `1` on the unit box `[0,1]^{m+1}` (indeed on the closed ball
of radius `√(m+1) + 1` around the origin) and has compact support. -/
def boxBump (m : ℕ) : Amb m → ℝ :=
  (⟨Real.sqrt (m + 1) + 1, Real.sqrt (m + 1) + 2, by positivity, by linarith⟩ :
    ContDiffBump (0 : Amb m))

/-- The bounded, compactly supported tangential field whose flow lines preserve the level sets of
`F`, and which is a positive multiple of `cofactorVectorF F` on the unit box. -/
def flowField {m : ℕ} (F : Amb m → Tgt m) : Amb m → Amb m :=
  fun x => boxBump m x • ((Real.sqrt (1 + ‖cofactorVectorF F x‖ ^ 2))⁻¹ • cofactorVectorF F x)

/-- The zero set of `F` in the unit box. -/
def zeroSet {m : ℕ} (F : Amb m → Tgt m) : Set (Amb m) := {x | x ∈ unitBox m ∧ F x = 0}

/-- The zeros of `F` on the boundary of the unit box. -/
def bdyZeros {m : ℕ} (F : Amb m → Tgt m) : Set (Amb m) :=
  {x | x ∈ unitBoxBdry m ∧ F x = 0}

@[simp] theorem mem_zeroSet {m : ℕ} {F : Amb m → Tgt m} {x : Amb m} :
    x ∈ zeroSet F ↔ x ∈ unitBox m ∧ F x = 0 := Iff.rfl

@[simp] theorem mem_bdyZeros {m : ℕ} {F : Amb m → Tgt m} {x : Amb m} :
    x ∈ bdyZeros F ↔ x ∈ unitBoxBdry m ∧ F x = 0 := Iff.rfl

/-- The unit box is closed. -/
theorem isClosed_unitBox (m : ℕ) : IsClosed (unitBox m) := by
  have h : unitBox m = ⋂ i : Fin (m + 1), {x : Amb m | x i ∈ Set.Icc (0 : ℝ) 1} := by
    ext x
    simp [unitBox, Set.mem_iInter]
  rw [h]
  exact isClosed_iInter fun i => isClosed_Icc.preimage (by fun_prop)

/-- The unit box is compact: it is the preimage of a product of compact intervals under the
homeomorphism `EuclideanSpace ℝ (Fin n) ≃ₜ (Fin n → ℝ)`. -/
theorem isCompact_unitBox (m : ℕ) : IsCompact (unitBox m) := by
  have h : unitBox m = (PiLp.homeomorph 2 (fun _ : Fin (m + 1) => ℝ)) ⁻¹'
      (Set.univ.pi fun _ : Fin (m + 1) => Set.Icc (0 : ℝ) 1) := by
    ext x
    simp only [Set.mem_preimage, Set.mem_univ_pi, unitBox, Set.mem_ofPred_eq]
    exact Iff.rfl
  rw [h]
  exact (Homeomorph.isCompact_preimage _).mpr (isCompact_univ_pi fun _ => isCompact_Icc)

/-- The boundary of the unit box is closed. -/
theorem isClosed_unitBoxBdry (m : ℕ) : IsClosed (unitBoxBdry m) := by
  have h : unitBoxBdry m =
      unitBox m ∩ (⋃ i : Fin (m + 1), {x : Amb m | x i = 0 ∨ x i = 1}) := by
    ext x
    simp [unitBoxBdry, Set.mem_iUnion]
  rw [h]
  refine (isClosed_unitBox m).inter ?_
  exact isClosed_iUnion_of_finite fun i =>
    (isClosed_eq (by fun_prop) continuous_const).union
      (isClosed_eq (by fun_prop) continuous_const)

/-- The zero set in the box is closed. -/
theorem isClosed_zeroSet {m : ℕ} {F : Amb m → Tgt m} (hF : Continuous F) :
    IsClosed (zeroSet F) := by
  have h : zeroSet F = unitBox m ∩ {y : Amb m | F y = (0 : Tgt m)} := by
    ext x; simp [zeroSet]
  rw [h]
  exact (isClosed_unitBox m).inter (isClosed_eq hF continuous_const)

/-- The zero set in the box is compact. -/
theorem isCompact_zeroSet {m : ℕ} {F : Amb m → Tgt m} (hF : Continuous F) :
    IsCompact (zeroSet F) :=
  (isCompact_unitBox m).of_isClosed_subset (isClosed_zeroSet hF) fun _ hx => hx.1

/-- The zero set in the box is contained in the box. -/
theorem zeroSet_subset_unitBox {m : ℕ} (F : Amb m → Tgt m) :
    zeroSet F ⊆ unitBox m := fun _ hx => hx.1

/-- The boundary zeros are compact (closed subset of the compact box). -/
theorem isCompact_bdyZeros {m : ℕ} {F : Amb m → Tgt m} (hF : Continuous F) :
    IsCompact (bdyZeros F) := by
  have h : bdyZeros F = unitBoxBdry m ∩ {y : Amb m | F y = (0 : Tgt m)} := by
    ext x; simp [bdyZeros]
  rw [h]
  exact (isCompact_unitBox m).of_isClosed_subset
    ((isClosed_unitBoxBdry m).inter (isClosed_eq hF continuous_const))
    fun _ hx => hx.1.1

end

end Work.Drive
