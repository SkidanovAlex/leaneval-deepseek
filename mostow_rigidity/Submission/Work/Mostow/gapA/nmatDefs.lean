import Mathlib
import Submission.Work.Mostow.gapA.axisNormDefs
import Submission.Work.Mostow.gapA.commutingRotation_eq_or_inv
import Submission.Work.Mostow.gapA.rotSetup

/-!
# The matrix of the normal action of an isometry on the axis normal plane

For two distinct boundary points `a ≠ b` of `Sph 3` and an orthonormal basis `B : AxisBasis a b`
of the positive definite normal plane `NormSub a b`, the map `u ↦ emat g *ᵥ u` preserves
`NormSub a b` whenever `emat g` fixes the two null vectors `nvec a`, `nvec b`.  Writing the
action of `emat g` in the basis `(B.E1, B.E2)` gives a `2 × 2` matrix `nmat B g`; this file
provides it together with multiplicativity and orthonormality statements.
-/

namespace Work.Mostow.gapA

open Submission.Mostow LeanEval.Geometry.MostowRigidity
open _root_.Matrix

noncomputable section
variable {a b : E 3}

/-- The `2 × 2` matrix of the action of `emat g` on the normal plane `NormSub a b` in the
orthonormal basis `(B.E1, B.E2)`.  Only meaningful when `emat g` preserves `NormSub a b`. -/
def nmat (B : AxisBasis a b) (g : PO 3 1) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![mink (emat g *ᵥ B.E1) B.E1, mink (emat g *ᵥ B.E2) B.E1;
     mink (emat g *ᵥ B.E1) B.E2, mink (emat g *ᵥ B.E2) B.E2]

@[simp] lemma nmat_zero_zero (B : AxisBasis a b) (g : PO 3 1) :
    nmat B g 0 0 = mink (emat g *ᵥ B.E1) B.E1 := by simp [nmat]

@[simp] lemma nmat_zero_one (B : AxisBasis a b) (g : PO 3 1) :
    nmat B g 0 1 = mink (emat g *ᵥ B.E2) B.E1 := by simp [nmat]

@[simp] lemma nmat_one_zero (B : AxisBasis a b) (g : PO 3 1) :
    nmat B g 1 0 = mink (emat g *ᵥ B.E1) B.E2 := by simp [nmat]

@[simp] lemma nmat_one_one (B : AxisBasis a b) (g : PO 3 1) :
    nmat B g 1 1 = mink (emat g *ᵥ B.E2) B.E2 := by simp [nmat]

/-- Coordinates of a pairing with a vector of the normal plane. -/
lemma mink_coord_axis (B : AxisBasis a b) {Z Z' : Fin 3 ⊕ Fin 1 → ℝ}
    (hZ' : Z' ∈ NormSub a b) :
    mink Z Z' = mink Z B.E1 * mink Z' B.E1 + mink Z B.E2 * mink Z' B.E2 := by
  conv_lhs => rw [coord_of_basis B hZ']
  rw [minkSeg_add_right, mink_smul_right'', mink_smul_right'']
  ring

/-- `mink` of a combination of the basis vectors with `B.E1`. -/
lemma mink_smulE_E1 (B : AxisBasis a b) (X Y : ℝ) :
    mink (X • B.E1 + Y • B.E2) B.E1 = X := by
  rw [minkSeg_add_left, mink_smul_left'', mink_smul_left'', B.n11, mink_E2_E1 (B := B)]
  ring

/-- `mink` of a combination of the basis vectors with `B.E2`. -/
lemma mink_smulE_E2 (B : AxisBasis a b) (X Y : ℝ) :
    mink (X • B.E1 + Y • B.E2) B.E2 = Y := by
  rw [minkSeg_add_left, mink_smul_left'', mink_smul_left'', B.n12, B.n22]
  ring

/-- The first column of `nmat`. -/
lemma nmat_mulVec_E1 (B : AxisBasis a b) (g : PO 3 1)
    (hg : ∀ Z ∈ NormSub a b, emat g *ᵥ Z ∈ NormSub a b) :
    emat g *ᵥ B.E1 = nmat B g 0 0 • B.E1 + nmat B g 1 0 • B.E2 := by
  rw [coord_of_basis B (hg B.E1 B.mem1), nmat_zero_zero, nmat_one_zero]

/-- The second column of `nmat`. -/
lemma nmat_mulVec_E2 (B : AxisBasis a b) (g : PO 3 1)
    (hg : ∀ Z ∈ NormSub a b, emat g *ᵥ Z ∈ NormSub a b) :
    emat g *ᵥ B.E2 = nmat B g 0 1 • B.E1 + nmat B g 1 1 • B.E2 := by
  rw [coord_of_basis B (hg B.E2 B.mem2), nmat_zero_one, nmat_one_one]

/-- The action of `emat g` on a general vector of the normal plane, in coordinates. -/
lemma emat_smul_add (B : AxisBasis a b) (g : PO 3 1)
    (hg : ∀ Z ∈ NormSub a b, emat g *ᵥ Z ∈ NormSub a b) (x y : ℝ) :
    emat g *ᵥ (x • B.E1 + y • B.E2)
      = (x * nmat B g 0 0 + y * nmat B g 0 1) • B.E1
        + (x * nmat B g 1 0 + y * nmat B g 1 1) • B.E2 := by
  rw [Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul,
    nmat_mulVec_E1 B g hg, nmat_mulVec_E2 B g hg]
  module

lemma nmat_entry00 (B : AxisBasis a b) (hA : POActionProp 3) (g h : PO 3 1)
    (hg : ∀ Z ∈ NormSub a b, emat g *ᵥ Z ∈ NormSub a b)
    (hh : ∀ Z ∈ NormSub a b, emat h *ᵥ Z ∈ NormSub a b) :
    nmat B (g * h) 0 0 = nmat B g 0 0 * nmat B h 0 0 + nmat B g 0 1 * nmat B h 1 0 := by
  rw [nmat_zero_zero, emat_mul hA, ← Matrix.mulVec_mulVec, nmat_mulVec_E1 B h hh,
    emat_smul_add B g hg, mink_smulE_E1]
  ring

lemma nmat_entry01 (B : AxisBasis a b) (hA : POActionProp 3) (g h : PO 3 1)
    (hg : ∀ Z ∈ NormSub a b, emat g *ᵥ Z ∈ NormSub a b)
    (hh : ∀ Z ∈ NormSub a b, emat h *ᵥ Z ∈ NormSub a b) :
    nmat B (g * h) 0 1 = nmat B g 0 0 * nmat B h 0 1 + nmat B g 0 1 * nmat B h 1 1 := by
  rw [nmat_zero_one, emat_mul hA, ← Matrix.mulVec_mulVec, nmat_mulVec_E2 B h hh,
    emat_smul_add B g hg, mink_smulE_E1]
  ring

lemma nmat_entry10 (B : AxisBasis a b) (hA : POActionProp 3) (g h : PO 3 1)
    (hg : ∀ Z ∈ NormSub a b, emat g *ᵥ Z ∈ NormSub a b)
    (hh : ∀ Z ∈ NormSub a b, emat h *ᵥ Z ∈ NormSub a b) :
    nmat B (g * h) 1 0 = nmat B g 1 0 * nmat B h 0 0 + nmat B g 1 1 * nmat B h 1 0 := by
  rw [nmat_one_zero, emat_mul hA, ← Matrix.mulVec_mulVec, nmat_mulVec_E1 B h hh,
    emat_smul_add B g hg, mink_smulE_E2]
  ring

lemma nmat_entry11 (B : AxisBasis a b) (hA : POActionProp 3) (g h : PO 3 1)
    (hg : ∀ Z ∈ NormSub a b, emat g *ᵥ Z ∈ NormSub a b)
    (hh : ∀ Z ∈ NormSub a b, emat h *ᵥ Z ∈ NormSub a b) :
    nmat B (g * h) 1 1 = nmat B g 1 0 * nmat B h 0 1 + nmat B g 1 1 * nmat B h 1 1 := by
  rw [nmat_one_one, emat_mul hA, ← Matrix.mulVec_mulVec, nmat_mulVec_E2 B h hh,
    emat_smul_add B g hg, mink_smulE_E2]
  ring

/-- `nmat` is multiplicative. -/
lemma nmat_mul (B : AxisBasis a b) (hA : POActionProp 3) (g h : PO 3 1)
    (hg : ∀ Z ∈ NormSub a b, emat g *ᵥ Z ∈ NormSub a b)
    (hh : ∀ Z ∈ NormSub a b, emat h *ᵥ Z ∈ NormSub a b) :
    nmat B (g * h) = nmat B g * nmat B h := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp only [nmat, Matrix.mul_fin_two]
  · exact nmat_entry00 B hA g h hg hh
  · exact nmat_entry01 B hA g h hg hh
  · exact nmat_entry10 B hA g h hg hh
  · exact nmat_entry11 B hA g h hg hh

/-- `nmat` of the identity. -/
lemma nmat_one (B : AxisBasis a b) (hA : POActionProp 3) :
    nmat B (1 : PO 3 1) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [nmat, emat_one hA, Matrix.one_fin_two, Matrix.one_mulVec, mink_E2_E1 (B := B),
      B.n11, B.n12, B.n22]

/-- Orthonormality of the columns of `nmat`. -/
lemma nmat_orth (B : AxisBasis a b) (g : PO 3 1)
    (hg : ∀ Z ∈ NormSub a b, emat g *ᵥ Z ∈ NormSub a b) :
    (nmat B g 0 0) ^ 2 + (nmat B g 1 0) ^ 2 = 1 ∧
    (nmat B g 0 1) ^ 2 + (nmat B g 1 1) ^ 2 = 1 ∧
    nmat B g 0 0 * nmat B g 0 1 + nmat B g 1 0 * nmat B g 1 1 = 0 := by
  have hE1 : mink (emat g *ᵥ B.E1) (emat g *ᵥ B.E1)
      = (mink (emat g *ᵥ B.E1) B.E1) ^ 2 + (mink (emat g *ᵥ B.E1) B.E2) ^ 2 := by
    rw [mink_coord_axis B (hg B.E1 B.mem1), sq, sq]
  have hE2 : mink (emat g *ᵥ B.E2) (emat g *ᵥ B.E2)
      = (mink (emat g *ᵥ B.E2) B.E1) ^ 2 + (mink (emat g *ᵥ B.E2) B.E2) ^ 2 := by
    rw [mink_coord_axis B (hg B.E2 B.mem2), sq, sq]
  have hEE : mink (emat g *ᵥ B.E1) (emat g *ᵥ B.E2)
      = mink (emat g *ᵥ B.E1) B.E1 * mink (emat g *ᵥ B.E2) B.E1
        + mink (emat g *ᵥ B.E1) B.E2 * mink (emat g *ᵥ B.E2) B.E2 :=
    mink_coord_axis B (hg B.E2 B.mem2)
  refine ⟨?_, ?_, ?_⟩
  · have h := hE1
    rw [mink_emat_emat, B.n11] at h
    simpa only [nmat_zero_zero, nmat_one_zero] using h.symm
  · have h := hE2
    rw [mink_emat_emat, B.n22] at h
    simpa only [nmat_zero_one, nmat_one_one] using h.symm
  · have h := hEE
    rw [mink_emat_emat, B.n12] at h
    simpa only [nmat_zero_zero, nmat_zero_one, nmat_one_zero, nmat_one_one] using h.symm

end

end Work.Mostow.gapA
