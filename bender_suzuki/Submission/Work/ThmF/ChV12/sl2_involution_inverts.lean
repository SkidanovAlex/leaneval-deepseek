import Mathlib
import Submission.Work.ThmF.ChV12.torus_aux

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option maxHeartbeats 800000

namespace Work.ThmF.ChV12

/-- In a field of characteristic `2`, for a `2 × 2` matrix `C` with `C * C + C + 1 = 0`, the
product `(p • 1 + q • C) * (p • 1 + q • (C * C))` is the scalar matrix `(p² + p q + q²) • 1`. -/
theorem cyc_mul_sq {F : Type*} [Field F] [CharP F 2]
    (C : Matrix (Fin 2) (Fin 2) F) (hC : C * C + C + 1 = 0) (p q : F) :
    (p • 1 + q • C) * (p • 1 + q • (C * C)) = (p ^ 2 + p * q + q ^ 2) • 1 := by
  have hCC : C * C = C + 1 := by
    have h1 : C * C + (C + 1) = 0 := by rw [← add_assoc]; exact hC
    have h2 := eq_neg_of_add_eq_zero_left h1
    rw [h2, CharTwo.neg_eq]
  have hCCC : C * C * C = 1 := by
    rw [mul_assoc, hCC, mul_add, mul_one, hCC]
    have h3 : C + 1 + C = 1 := by
      rw [show C + 1 + C = (C + C) + 1 from by abel, CharTwo.add_self_eq_zero, zero_add]
    exact h3
  rw [Matrix.add_mul, Matrix.mul_add, Matrix.mul_add]
  simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one, smul_smul]
  rw [← mul_assoc, hCCC, hCC, smul_add, mul_comm q p]
  have hpqq : p * q + p * q = 0 := CharTwo.add_self_eq_zero (p * q)
  rw [show (p * p) • 1 + ((p * q) • C + (p * q) • 1) + ((p * q) • C + (q * q) • 1)
        = (p * p) • 1 + (p * q) • 1 + (q * q) • 1 + ((p * q) • C + (p * q) • C) from by abel]
  rw [show (p * q) • C + (p * q) • C = 0 from by rw [← add_smul, hpqq, zero_smul], add_zero]
  rw [← add_smul, ← add_smul]
  rw [show p * p + p * q + q * q = p ^ 2 + p * q + q ^ 2 from by ring]

theorem sl2_involution_inverts {F : Type*} [Field F] [Fintype F] [CharP F 2] (n : ℕ)
    (hF : Nat.card F = 2 ^ n) (h3 : 3 ∣ 2 ^ n + 1)
    (a c : Matrix.SpecialLinearGroup (Fin 2) F) (hc : orderOf c = 3) (hac : a * c * a⁻¹ = c⁻¹)
    (x : Matrix.SpecialLinearGroup (Fin 2) F)
    (hx : x ∈ Subgroup.centralizer ({c} : Set (Matrix.SpecialLinearGroup (Fin 2) F))) :
    a * x * a⁻¹ = x⁻¹ := by
  classical
  set A : Matrix (Fin 2) (Fin 2) F := (a : Matrix (Fin 2) (Fin 2) F) with hA
  set C : Matrix (Fin 2) (Fin 2) F := (c : Matrix (Fin 2) (Fin 2) F) with hC
  set X : Matrix (Fin 2) (Fin 2) F := (x : Matrix (Fin 2) (Fin 2) F) with hX
  have hCmat : C * C + C + 1 = 0 := by rw [hC]; exact sl2_order_three_sq c hc
  have h3F : 3 ∣ Nat.card F + 1 := by rw [hF]; exact h3
  have hroot : ∀ t : F, t ^ 2 + t + 1 ≠ 0 := fun t ht => torus_no_root h3F t ht
  have hCdet : C.det = 1 := by rw [hC]; exact Matrix.SpecialLinearGroup.det_coe c
  have hAdet : A.det = 1 := by rw [hA]; exact Matrix.SpecialLinearGroup.det_coe a
  have hXdet : X.det = 1 := by rw [hX]; exact Matrix.SpecialLinearGroup.det_coe x
  have htrC : C.trace = 1 := sl2_trace_eq_one hCdet hCmat
  -- `x` commutes with `c`
  have hxc_grp : x * c = c * x := Subgroup.mem_centralizer_singleton_iff.mp hx
  have hxc : X * C = C * X := by
    have h := congrArg
      (fun z : Matrix.SpecialLinearGroup (Fin 2) F => (z : Matrix (Fin 2) (Fin 2) F)) hxc_grp
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul] at h
    simpa only [← hX, ← hC] using h
  obtain ⟨p, q, hXpq⟩ := (matrix_centralizer_eq_span hCmat hroot X).mp hxc
  -- the scalar identity coming from `det X = 1`
  have hscal : p ^ 2 + p * q + q ^ 2 = 1 := by
    have h := det_smul_one_add_smul p q C
    have h2 : X.det = p ^ 2 + p * q * C.trace + q ^ 2 * C.det := by rw [hXpq]; exact h
    rw [hXdet, htrC, hCdet, mul_one, mul_one] at h2
    exact h2.symm
  -- coerced inverse of `a`
  have hAinv : A⁻¹ = A.adjugate := by
    rw [Matrix.inv_def, hAdet, Ring.inverse_one, one_smul]
  have hAAinv : A * A⁻¹ = 1 := by
    rw [hAinv, Matrix.mul_adjugate, hAdet, one_smul]
  have hcoea : (((a⁻¹ : Matrix.SpecialLinearGroup (Fin 2) F)) : Matrix (Fin 2) (Fin 2) F)
      = A⁻¹ := by
    rw [Matrix.SpecialLinearGroup.coe_inv, hAinv, hA]
  -- coerced inverse of `c`, using `c ^ 3 = 1`
  have hc3 : c ^ 3 = 1 := by rw [← hc]; exact pow_orderOf_eq_one c
  have hcinv : c⁻¹ = c * c := by
    apply inv_eq_of_mul_eq_one_right
    rw [← pow_two, ← pow_succ', hc3]
  have hcoec : (((c⁻¹ : Matrix.SpecialLinearGroup (Fin 2) F)) : Matrix (Fin 2) (Fin 2) F)
      = C * C := by
    have h := congrArg
      (fun z : Matrix.SpecialLinearGroup (Fin 2) F => (z : Matrix (Fin 2) (Fin 2) F)) hcinv
    rw [Matrix.SpecialLinearGroup.coe_mul] at h
    simpa only [← hC] using h
  -- `a` conjugates `c` to `c * c`
  have hAC : A * C * A⁻¹ = C * C := by
    have h := congrArg
      (fun z : Matrix.SpecialLinearGroup (Fin 2) F => (z : Matrix (Fin 2) (Fin 2) F)) hac
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul] at h
    rw [hcoea, hcoec] at h
    simpa only [← hA, ← hC] using h
  -- conjugation acts on `F[C]` by `C ↦ C * C`
  have hAXA : A * X * A⁻¹ = p • 1 + q • (C * C) := by
    rw [hXpq, Matrix.mul_add, Matrix.mul_smul, Matrix.mul_smul, Matrix.mul_one,
        Matrix.add_mul, Matrix.smul_mul, Matrix.smul_mul, hAAinv, hAC]
  have hXmul : X * (p • 1 + q • (C * C)) = 1 := by
    rw [hXpq, cyc_mul_sq C hCmat p q, hscal, one_smul]
  -- assemble: `x * (a * x * a⁻¹) = 1`
  have hmatrix : (((x * (a * x * a⁻¹) : Matrix.SpecialLinearGroup (Fin 2) F))
      : Matrix (Fin 2) (Fin 2) F) = 1 := by
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
        Matrix.SpecialLinearGroup.coe_mul, hcoea]
    rw [← hA, ← hX]
    rw [hAXA, hXmul]
  have hgrp : x * (a * x * a⁻¹) = 1 := by
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_one]
    exact hmatrix
  exact eq_inv_of_mul_eq_one_right hgrp

end Work.ThmF.ChV12
