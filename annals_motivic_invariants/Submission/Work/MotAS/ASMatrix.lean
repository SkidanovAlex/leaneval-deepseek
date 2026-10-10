import Submission.Work.MotAS.ASData
import Submission.Work.MotAS.asM_det
import Submission.Work.MotAS.asN_det

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The Galois-coordinate matrices `asM`, `asN`: determinant and injectivity

Part of the subproject `Submission/Work/MotAS` (`Work.MotAS`).

`asM w i j = (w+i)^j` and `asN w k j = (w+2k)^j` are Vandermonde matrices in the five *distinct*
nodes `0,1,2,3,4` (resp. `0,2,4,6,8`), so their determinants are the *constants*
`∏_{i<i'}(i'-i) = 288` and `2¹⁰·288 = 294912`.  In a ring of characteristic `5` both constants are
units (`288 ≡ 3`, `294912 ≡ 2`, with inverses `2` and `3`), so the maps `y ↦ asM w · y` and
`z ↦ asN w · z` are injective; this is what lets the transported link identities
(`Work.MotAS.ASLink`) be *cancelled* back to `w`-free form.

`asM` is definitionally `Matrix.vandermonde (fun i => w + i)`, so `asM_det` is
`Matrix.det_vandermonde` followed by the evaluation of the (constant) double product — the
filtered products `∏ j > i, (v j - v i)` have to be unwound by hand.  **Open node.**
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

namespace Work.MotAS

variable {R : Type*} [CommRing R]

/-- In characteristic `5` the constant `288` is a unit (with inverse `2`). -/
theorem isUnit_288 (h5 : (5 : R) = 0) : IsUnit (288 : R) := by
  change IsUnit ((288 : ℕ) : R)
  have h5' : ((5 : ℕ) : R) = 0 := h5
  have h : ((288 : ℕ) : R) = 3 := by
    rw [show (288 : ℕ) = 5 * 57 + 3 from by norm_num, Nat.cast_add, Nat.cast_mul, h5',
      zero_mul, zero_add]
    norm_num
  rw [h]
  refine IsUnit.of_mul_eq_one (2 : R) ?_
  have h6 : ((3 : R) * 2) = 1 := by
    have h' : ((3 : R) * 2) = (6 : R) := by norm_num
    rw [h']
    change ((6 : ℕ) : R) = 1
    rw [show (6 : ℕ) = 5 + 1 from by norm_num, Nat.cast_add, h5', zero_add, Nat.cast_one]
  exact h6

/-- In characteristic `5` the constant `294912` is a unit (with inverse `3`). -/
theorem isUnit_294912 (h5 : (5 : R) = 0) : IsUnit (294912 : R) := by
  change IsUnit ((294912 : ℕ) : R)
  have h5' : ((5 : ℕ) : R) = 0 := h5
  have h : ((294912 : ℕ) : R) = 2 := by
    rw [show (294912 : ℕ) = 5 * 58982 + 2 from by norm_num, Nat.cast_add, Nat.cast_mul, h5',
      zero_mul, zero_add]
    norm_num
  rw [h]
  refine IsUnit.of_mul_eq_one (3 : R) ?_
  have h6 : ((2 : R) * 3) = 1 := by
    have h' : ((2 : R) * 3) = (6 : R) := by norm_num
    rw [h']
    change ((6 : ℕ) : R) = 1
    rw [show (6 : ℕ) = 5 + 1 from by norm_num, Nat.cast_add, h5', zero_add, Nat.cast_one]
  exact h6

/-! ## The Vandermonde determinants

`asM_det` (`(asM w).det = 288`) and `asN_det` (`(asN w).det = 294912`) are open nodes and live in
the sibling modules `Submission.Work.MotAS.asM_det` / `Submission.Work.MotAS.asN_det`.  Both
matrices are Vandermonde matrices in five distinct nodes (`asM` is definitionally
`Matrix.vandermonde (fun i => w + i)`), so the determinant is the constant double product
`∏ i, ∏ j > i, (v j − v i)`, which has to be unwound by hand. -/

/-- **`asM` is injective on coefficient vectors** in characteristic `5`. -/
theorem asM_mulVec_injective (h5 : (5 : R) = 0) (w : R) :
    Function.Injective (asM w).mulVec := by
  intro x y hxy
  have hunit : IsUnit (asM w) :=
    (Matrix.isUnit_iff_isUnit_det _).mpr (by rw [asM_det]; exact isUnit_288 h5)
  obtain ⟨u, hu⟩ := hunit
  have h1 : (↑u⁻¹ : Matrix (Fin 5) (Fin 5) R) * (asM w) = 1 := by
    rw [← hu, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  calc x = (1 : Matrix (Fin 5) (Fin 5) R).mulVec x := (Matrix.one_mulVec x).symm
    _ = ((↑u⁻¹ : Matrix (Fin 5) (Fin 5) R) * (asM w)).mulVec x := by rw [h1]
    _ = (↑u⁻¹ : Matrix (Fin 5) (Fin 5) R).mulVec ((asM w).mulVec x) := by rw [← Matrix.mulVec_mulVec]
    _ = (↑u⁻¹ : Matrix (Fin 5) (Fin 5) R).mulVec ((asM w).mulVec y) := by rw [hxy]
    _ = ((↑u⁻¹ : Matrix (Fin 5) (Fin 5) R) * (asM w)).mulVec y := by rw [Matrix.mulVec_mulVec]
    _ = (1 : Matrix (Fin 5) (Fin 5) R).mulVec y := by rw [h1]
    _ = y := Matrix.one_mulVec y

/-- **`asN` is injective on coefficient vectors** in characteristic `5`. -/
theorem asN_mulVec_injective (h5 : (5 : R) = 0) (w : R) :
    Function.Injective (asN w).mulVec := by
  intro x y hxy
  have hunit : IsUnit (asN w) :=
    (Matrix.isUnit_iff_isUnit_det _).mpr (by rw [asN_det]; exact isUnit_294912 h5)
  obtain ⟨u, hu⟩ := hunit
  have h1 : (↑u⁻¹ : Matrix (Fin 5) (Fin 5) R) * (asN w) = 1 := by
    rw [← hu, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  calc x = (1 : Matrix (Fin 5) (Fin 5) R).mulVec x := (Matrix.one_mulVec x).symm
    _ = ((↑u⁻¹ : Matrix (Fin 5) (Fin 5) R) * (asN w)).mulVec x := by rw [h1]
    _ = (↑u⁻¹ : Matrix (Fin 5) (Fin 5) R).mulVec ((asN w).mulVec x) := by rw [← Matrix.mulVec_mulVec]
    _ = (↑u⁻¹ : Matrix (Fin 5) (Fin 5) R).mulVec ((asN w).mulVec y) := by rw [hxy]
    _ = ((↑u⁻¹ : Matrix (Fin 5) (Fin 5) R) * (asN w)).mulVec y := by rw [Matrix.mulVec_mulVec]
    _ = (1 : Matrix (Fin 5) (Fin 5) R).mulVec y := by rw [h1]
    _ = y := Matrix.one_mulVec y

end Work.MotAS
