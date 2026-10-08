import Mathlib
import Submission.Work.BSLit.BenderFacts2.Facts2Defs
import Submission.Work.Models.PSL2.Defs
import Submission.Work.Models.PSL2.B_split_setup

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.BSLit.BenderFacts2.Facts2SL2Aux` — the inversion of the centraliser in `SL(2,F)`

For `x ∈ SL(2,F)` (`F` of characteristic two) whose `(1,0)`-entry is non-zero, every element of
the centraliser `C(x)` is a polynomial in `x` of degree `≤ 1` (`bf2_sl2_mem_centralizer_eq_smul_one_add`).
Hence, if an involution `u` inverts `x`, it inverts the whole centraliser
(`bf2_sl2_conj_eq_inv_of_mem_centralizer`): for `y = α + βx ∈ C(x)` the conjugate `u y u⁻¹` is
`α + β x⁻¹`, and
`(α + βx)(α + βx⁻¹) = α² + αβ tr(x) + β² = det(α + βx) = det(y) = 1`.

The preliminary computations are the trace identity `x⁻¹ + x = (trace x) • 1`
(`bf2_sl2_coe_add_coe_inv`, from the explicit form of the inverse matrix) and the product
identity `bf2_smul_one_add_mul_smul_one_add_inv`.
-/

set_option autoImplicit false

open Matrix

namespace Work.BSLit.BenderFacts2

/-- **The product of `α • 1 + β • M` and `α • 1 + β • M'`** where `M * M' = 1` and
`M + M' = (trace M) • 1` (characteristic two): it is the scalar matrix
`(α ^ 2 + α * β * (trace M) + β ^ 2) • 1`. -/
theorem bf2_smul_one_add_mul_smul_one_add_inv {F : Type*} [Field F] [CharP F 2]
    {M M' : Matrix (Fin 2) (Fin 2) F} (hmul : M * M' = 1) (hadd : M + M' = M.trace • 1)
    (α β : F) :
    (α • 1 + β • M) * (α • 1 + β • M') = (α ^ 2 + α * β * M.trace + β ^ 2) • 1 := by
  have hexp : (α • 1 + β • M) * (α • 1 + β • M')
      = (α * α) • 1 + (β * α) • M' + ((α * β) • M + (β * β) • (M * M')) := by
    rw [add_mul, mul_add, mul_add]
    simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_one, Matrix.one_mul, smul_smul]
  rw [hexp, hmul]
  have h1 : (β * α) • M' + (α * β) • M = (α * β * M.trace) • 1 := by
    rw [mul_comm β α, ← smul_add, add_comm M' M, hadd, smul_smul]
  have h2 : (β * β) • (1 : Matrix (Fin 2) (Fin 2) F) = (β ^ 2) • 1 := by rw [pow_two]
  have h3 : (α * α) • (1 : Matrix (Fin 2) (Fin 2) F) = (α ^ 2) • 1 := by rw [pow_two]
  rw [h2, h3, add_smul, add_smul, ← h1]
  abel

/-- For `M` of determinant one, `det (α • 1 + β • M) = α ^ 2 + α * β * (trace M) + β ^ 2`
(characteristic two). -/
theorem bf2_det_smul_one_add {F : Type*} [Field F] [CharP F 2]
    {M : Matrix (Fin 2) (Fin 2) F} (hM : M.det = 1) (α β : F) :
    (α • 1 + β • M).det = α ^ 2 + α * β * M.trace + β ^ 2 := by
  have hM' : M 0 0 * M 1 1 - M 0 1 * M 1 0 = 1 := by
    rw [← Matrix.det_fin_two]; exact hM
  have key : α • 1 + β • M
      = !![α + β * M 0 0, β * M 0 1; β * M 1 0, α + β * M 1 1] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.add_apply, Matrix.smul_apply]
  rw [key, Matrix.det_fin_two, Matrix.trace_fin_two]
  simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one]
  linear_combination (β ^ 2) * hM'

/-- **`x⁻¹ + x = (trace x) • 1`** for `x ∈ SL(2,F)` (`F` of characteristic two). -/
theorem bf2_sl2_coe_add_coe_inv {F : Type*} [Field F] [CharP F 2]
    (x : Work.Models.SL2 F) :
    (x : Matrix (Fin 2) (Fin 2) F) + ((x⁻¹ : Work.Models.SL2 F) : Matrix (Fin 2) (Fin 2) F)
      = ((x : Matrix (Fin 2) (Fin 2) F).trace) • 1 := by
  rw [Work.Models.PSL2.inv_coe]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.trace_fin_two, CharTwo.add_self_eq_zero, add_comm, add_left_comm, add_assoc]

/-- **`x * x⁻¹ = 1`** as matrices, for `x ∈ SL(2,F)`. -/
theorem bf2_sl2_mul_coe_inv {F : Type*} [Field F] [CharP F 2] (x : Work.Models.SL2 F) :
    (x : Matrix (Fin 2) (Fin 2) F) * ((x⁻¹ : Work.Models.SL2 F) : Matrix (Fin 2) (Fin 2) F)
      = 1 := by
  have h := congrArg (fun z : Work.Models.SL2 F => (z : Matrix (Fin 2) (Fin 2) F)) (mul_inv_cancel x)
  rwa [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_one] at h

/-- **Every element of the centraliser of `x ∈ SL(2,F)` is a polynomial in `x` of degree `≤ 1`**,
provided the `(1,0)`-entry of `x` is non-zero: writing `N * M = M * N` for `M = (x : Matrix …)`
with `M 1 0 ≠ 0` and `N` arbitrary, the `(0,0)`- and `(1,0)`-entries of the commutation relation
give `N = α • 1 + β • M` with `β = N 1 0 / (M 1 0)` and `α = N 0 0 + β * (M 0 0)`. -/
theorem bf2_sl2_mem_centralizer_eq_smul_one_add {F : Type*} [Field F] [CharP F 2]
    {x y : Work.Models.SL2 F}
    (hx10 : (x : Matrix (Fin 2) (Fin 2) F) 1 0 ≠ 0)
    (hy : y ∈ Subgroup.centralizer ({x} : Set (Work.Models.SL2 F))) :
    ∃ α β : F, (y : Matrix (Fin 2) (Fin 2) F)
      = α • 1 + β • (x : Matrix (Fin 2) (Fin 2) F) := by
  have hcomm : (y : Matrix (Fin 2) (Fin 2) F) * (x : Matrix (Fin 2) (Fin 2) F)
      = (x : Matrix (Fin 2) (Fin 2) F) * (y : Matrix (Fin 2) (Fin 2) F) := by
    have h := (Subgroup.mem_centralizer_iff.mp hy) x (Set.mem_singleton x)
    have h2 := congrArg (fun z : Work.Models.SL2 F => (z : Matrix (Fin 2) (Fin 2) F)) h
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul] at h2
    exact h2.symm
  have e00 : (y : Matrix (Fin 2) (Fin 2) F) 0 1 * (x : Matrix (Fin 2) (Fin 2) F) 1 0
      = (x : Matrix (Fin 2) (Fin 2) F) 0 1 * (y : Matrix (Fin 2) (Fin 2) F) 1 0 := by
    have h := congrArg (fun N : Matrix (Fin 2) (Fin 2) F => N 0 0) hcomm
    simp only [Matrix.mul_apply, Fin.sum_univ_two] at h
    linear_combination h
  have e10 : (y : Matrix (Fin 2) (Fin 2) F) 1 0
        * ((x : Matrix (Fin 2) (Fin 2) F) 0 0 + (x : Matrix (Fin 2) (Fin 2) F) 1 1)
      = (x : Matrix (Fin 2) (Fin 2) F) 1 0
        * ((y : Matrix (Fin 2) (Fin 2) F) 0 0 + (y : Matrix (Fin 2) (Fin 2) F) 1 1) := by
    have h := congrArg (fun N : Matrix (Fin 2) (Fin 2) F => N 1 0) hcomm
    simp only [Matrix.mul_apply, Fin.sum_univ_two] at h
    have hsum : (y : Matrix (Fin 2) (Fin 2) F) 1 0 * (x : Matrix (Fin 2) (Fin 2) F) 0 0
        + (y : Matrix (Fin 2) (Fin 2) F) 1 1 * (x : Matrix (Fin 2) (Fin 2) F) 1 0
        + ((x : Matrix (Fin 2) (Fin 2) F) 1 0 * (y : Matrix (Fin 2) (Fin 2) F) 0 0
          + (x : Matrix (Fin 2) (Fin 2) F) 1 1 * (y : Matrix (Fin 2) (Fin 2) F) 1 0) = 0 := by
      rw [h, CharTwo.add_self_eq_zero]
    have hsum2 : (y : Matrix (Fin 2) (Fin 2) F) 1 0
          * ((x : Matrix (Fin 2) (Fin 2) F) 0 0 + (x : Matrix (Fin 2) (Fin 2) F) 1 1)
        + (x : Matrix (Fin 2) (Fin 2) F) 1 0
          * ((y : Matrix (Fin 2) (Fin 2) F) 0 0 + (y : Matrix (Fin 2) (Fin 2) F) 1 1) = 0 := by
      rw [show (y : Matrix (Fin 2) (Fin 2) F) 1 0 * (x : Matrix (Fin 2) (Fin 2) F) 0 0
            + (y : Matrix (Fin 2) (Fin 2) F) 1 1 * (x : Matrix (Fin 2) (Fin 2) F) 1 0
            + ((x : Matrix (Fin 2) (Fin 2) F) 1 0 * (y : Matrix (Fin 2) (Fin 2) F) 0 0
              + (x : Matrix (Fin 2) (Fin 2) F) 1 1 * (y : Matrix (Fin 2) (Fin 2) F) 1 0)
          = (y : Matrix (Fin 2) (Fin 2) F) 1 0
              * ((x : Matrix (Fin 2) (Fin 2) F) 0 0 + (x : Matrix (Fin 2) (Fin 2) F) 1 1)
            + (x : Matrix (Fin 2) (Fin 2) F) 1 0
              * ((y : Matrix (Fin 2) (Fin 2) F) 0 0 + (y : Matrix (Fin 2) (Fin 2) F) 1 1)
          by ring] at hsum
      exact hsum
    exact CharTwo.add_eq_zero.mp hsum2
  refine ⟨(y : Matrix (Fin 2) (Fin 2) F) 0 0
      + ((y : Matrix (Fin 2) (Fin 2) F) 1 0 * ((x : Matrix (Fin 2) (Fin 2) F) 1 0)⁻¹)
        * (x : Matrix (Fin 2) (Fin 2) F) 0 0,
    (y : Matrix (Fin 2) (Fin 2) F) 1 0 * ((x : Matrix (Fin 2) (Fin 2) F) 1 0)⁻¹, ?_⟩
  have h01 : (y : Matrix (Fin 2) (Fin 2) F) 0 1
      = ((y : Matrix (Fin 2) (Fin 2) F) 1 0 * ((x : Matrix (Fin 2) (Fin 2) F) 1 0)⁻¹)
        * (x : Matrix (Fin 2) (Fin 2) F) 0 1 := by
    calc (y : Matrix (Fin 2) (Fin 2) F) 0 1
        = ((y : Matrix (Fin 2) (Fin 2) F) 0 1 * (x : Matrix (Fin 2) (Fin 2) F) 1 0)
          * ((x : Matrix (Fin 2) (Fin 2) F) 1 0)⁻¹ := by
          rw [mul_assoc, mul_inv_cancel₀ hx10, mul_one]
      _ = ((x : Matrix (Fin 2) (Fin 2) F) 0 1 * (y : Matrix (Fin 2) (Fin 2) F) 1 0)
          * ((x : Matrix (Fin 2) (Fin 2) F) 1 0)⁻¹ := by rw [e00]
      _ = ((y : Matrix (Fin 2) (Fin 2) F) 1 0 * ((x : Matrix (Fin 2) (Fin 2) F) 1 0)⁻¹)
          * (x : Matrix (Fin 2) (Fin 2) F) 0 1 := by ring
  have hβ : ((y : Matrix (Fin 2) (Fin 2) F) 1 0 * ((x : Matrix (Fin 2) (Fin 2) F) 1 0)⁻¹)
        * ((x : Matrix (Fin 2) (Fin 2) F) 0 0 + (x : Matrix (Fin 2) (Fin 2) F) 1 1)
      = (y : Matrix (Fin 2) (Fin 2) F) 0 0 + (y : Matrix (Fin 2) (Fin 2) F) 1 1 := by
    calc ((y : Matrix (Fin 2) (Fin 2) F) 1 0 * ((x : Matrix (Fin 2) (Fin 2) F) 1 0)⁻¹)
          * ((x : Matrix (Fin 2) (Fin 2) F) 0 0 + (x : Matrix (Fin 2) (Fin 2) F) 1 1)
        = ((x : Matrix (Fin 2) (Fin 2) F) 1 0)⁻¹
          * ((y : Matrix (Fin 2) (Fin 2) F) 1 0
            * ((x : Matrix (Fin 2) (Fin 2) F) 0 0 + (x : Matrix (Fin 2) (Fin 2) F) 1 1)) := by
          ring
      _ = ((x : Matrix (Fin 2) (Fin 2) F) 1 0)⁻¹
          * ((x : Matrix (Fin 2) (Fin 2) F) 1 0
            * ((y : Matrix (Fin 2) (Fin 2) F) 0 0 + (y : Matrix (Fin 2) (Fin 2) F) 1 1)) := by
          rw [e10]
      _ = (y : Matrix (Fin 2) (Fin 2) F) 0 0 + (y : Matrix (Fin 2) (Fin 2) F) 1 1 := by
          rw [← mul_assoc, inv_mul_cancel₀ hx10, one_mul]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.add_apply, Matrix.smul_apply]
  · simp only [add_assoc, CharTwo.add_self_eq_zero, add_zero]
  · exact h01
  · simp only [mul_assoc, inv_mul_cancel₀ hx10, mul_one]
  · simp only [add_assoc, ← mul_add, hβ]
    simp only [← add_assoc, CharTwo.add_self_eq_zero, zero_add]

/-- **An element `u` inverting `x` inverts the whole centraliser of `x`.** -/
theorem bf2_sl2_conj_eq_inv_of_mem_centralizer {F : Type*} [Field F] [CharP F 2]
    {x u y : Work.Models.SL2 F}
    (hx10 : (x : Matrix (Fin 2) (Fin 2) F) 1 0 ≠ 0)
    (hxu : u * x * u⁻¹ = x⁻¹)
    (hy : y ∈ Subgroup.centralizer ({x} : Set (Work.Models.SL2 F))) :
    u * y * u⁻¹ = y⁻¹ := by
  obtain ⟨α, β, hαβ⟩ := bf2_sl2_mem_centralizer_eq_smul_one_add hx10 hy
  have hu1 : (u : Matrix (Fin 2) (Fin 2) F)
      * ((u⁻¹ : Work.Models.SL2 F) : Matrix (Fin 2) (Fin 2) F) = 1 := by
    have h := congrArg (fun z : Work.Models.SL2 F => (z : Matrix (Fin 2) (Fin 2) F))
      (mul_inv_cancel u)
    rwa [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_one] at h
  have huxu : (u : Matrix (Fin 2) (Fin 2) F) * (x : Matrix (Fin 2) (Fin 2) F)
      * ((u⁻¹ : Work.Models.SL2 F) : Matrix (Fin 2) (Fin 2) F)
      = ((x⁻¹ : Work.Models.SL2 F) : Matrix (Fin 2) (Fin 2) F) := by
    have h := congrArg (fun z : Work.Models.SL2 F => (z : Matrix (Fin 2) (Fin 2) F)) hxu
    rwa [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul] at h
  have huy : ((u * y * u⁻¹ : Work.Models.SL2 F) : Matrix (Fin 2) (Fin 2) F)
      = α • 1 + β • ((x⁻¹ : Work.Models.SL2 F) : Matrix (Fin 2) (Fin 2) F) := by
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, hαβ]
    simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul,
      Matrix.mul_one, hu1, huxu]
  have hdet : α ^ 2 + α * β * (x : Matrix (Fin 2) (Fin 2) F).trace + β ^ 2 = 1 := by
    rw [← bf2_det_smul_one_add x.2 α β, ← hαβ]
    exact y.2
  have hprod : ((y * (u * y * u⁻¹) : Work.Models.SL2 F) : Matrix (Fin 2) (Fin 2) F) = 1 := by
    rw [Matrix.SpecialLinearGroup.coe_mul, hαβ, huy,
      bf2_smul_one_add_mul_smul_one_add_inv (bf2_sl2_mul_coe_inv x) (bf2_sl2_coe_add_coe_inv x), hdet,
      one_smul]
  have hprodSL : y * (u * y * u⁻¹) = 1 := by
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_one]
    exact hprod
  exact (mul_eq_one_iff_inv_eq.mp hprodSL).symm

end Work.BSLit.BenderFacts2
