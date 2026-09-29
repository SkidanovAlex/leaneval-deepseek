import Mathlib
import Submission.CDT.LLData
import Submission.Commons.Algebra.Polynomial.dvd_sq_X_sub_C_iff
import Submission.Commons.FieldTheory.RatFunc.ordAtT_adjoint_eq_of_indicial
import Submission.Commons.FieldTheory.RatFunc.exists_leading_term
import Submission.Commons.FieldTheory.RatFunc.ordAtT_adjoint_eq_of_indicial_le

/-!
# The local (indicial) data of the C-side operator `LL`

The paper's order-four operator `LL = Σ_i c_i(y) d^i/dy^i` of the section
"Products of two logarithms" (CDT, arXiv:2408.15403) has

  `c₃ = (y-4)·y²·Λnum`,   `c₄ = (y-4)²·y³·R₄·R₁₀`

(`Submission/CDT/LLData`).  Locally at a point `α`, the eliminated fourth-order
equation is `Σ_i (-1)^i (γᵢ b₃)^{(i)} = -R` with `γᵢ = cᵢ/c₄`, and the local
indicial analysis (`Commons.FieldTheory.RatFunc.ordAtT_adjoint_eq_of_indicial`)
converts this into pole-order bounds for the unknown `b₃`.

This module collects the *local data* at a simple root `β` of `R₄` and at a
simple root `γ` of `R₁₀`: the orders and the leading coefficients of the `γᵢ`.
-/

set_option maxHeartbeats 1000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Submission.CDT.CsideLocal

open Commons.FieldTheory.RatFunc

noncomputable section

/-- The common denominator `(y-4)·y·R₄·R₁₀` of the logarithmic derivative
`c₃/c₄ = Λnum/((y-4)·y·R₄·R₁₀)`. -/
noncomputable def cden {K : Type*} [Field K] (R4 R10 : Polynomial K) : Polynomial K :=
  (Polynomial.X - Polynomial.C 4) * Polynomial.X * R4 * R10

variable {K : Type*} [Field K]

theorem cden_ne_zero_of_ne_zero {R4 R10 : Polynomial K} (hR4 : R4 ≠ 0) (hR10 : R10 ≠ 0) :
    cden R4 R10 ≠ 0 := by
  rw [cden]
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero (Polynomial.X_sub_C_ne_zero 4)
    Polynomial.X_ne_zero) hR4) hR10

theorem cden_ne_zero {R4 R10 : Polynomial K} {β : K}
    (hR4d : R4.derivative.eval β ≠ 0) (hR10 : R10.eval β ≠ 0) :
    cden R4 R10 ≠ 0 :=
  cden_ne_zero_of_ne_zero
    (fun h => hR4d (by rw [h, Polynomial.derivative_zero, Polynomial.eval_zero]))
    (fun h => hR10 (by rw [h, Polynomial.eval_zero]))

theorem eval_cden {R4 R10 : Polynomial K} {β : K} (hR4 : R4.eval β = 0) :
    (cden R4 R10).eval β = 0 := by
  rw [cden]
  simp only [Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C, hR4]
  ring

theorem eval_cden_R10 {R4 R10 : Polynomial K} {γ : K} (hR10 : R10.eval γ = 0) :
    (cden R4 R10).eval γ = 0 := by
  rw [cden]
  simp only [Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C, hR10]
  ring

/-- The derivative of `cden` at `β`, when `β` is a root of `R₄`. -/
theorem derivative_eval_cden {R4 R10 : Polynomial K} {β : K} (hR4 : R4.eval β = 0) :
    (cden R4 R10).derivative.eval β
      = (β - 4) * β * R4.derivative.eval β * R10.eval β := by
  rw [cden]
  simp only [Polynomial.derivative_mul, Polynomial.derivative_sub, Polynomial.derivative_X,
    Polynomial.derivative_C]
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_sub,
    Polynomial.eval_X, Polynomial.eval_C, hR4]
  ring

/-- The order of `cden R4 R10` at a simple root `β` of `R₄` (with `β ∉ {0,4}`) is `1`. -/
theorem rootMultiplicity_cden {R4 R10 : Polynomial K} {β : K} (hR4 : R4.eval β = 0)
    (hR4d : R4.derivative.eval β ≠ 0) (hR10 : R10.eval β ≠ 0) (hβ0 : β ≠ 0) (hβ4 : β ≠ 4) :
    Polynomial.rootMultiplicity β (cden R4 R10) = 1 := by
  classical
  have h4 : (Polynomial.X - Polynomial.C (4 : K) : Polynomial K) ≠ 0 :=
    Polynomial.X_sub_C_ne_zero 4
  have h4X : (Polynomial.X - Polynomial.C (4 : K) : Polynomial K) * Polynomial.X ≠ 0 :=
    mul_ne_zero h4 Polynomial.X_ne_zero
  have h4X4 : (Polynomial.X - Polynomial.C (4 : K) : Polynomial K) * Polynomial.X * R4 ≠ 0 :=
    mul_ne_zero h4X (fun h => hR4d (by rw [h, Polynomial.derivative_zero, Polynomial.eval_zero]))
  have h4X410 :
      (Polynomial.X - Polynomial.C (4 : K) : Polynomial K) * Polynomial.X * R4 * R10 ≠ 0 :=
    mul_ne_zero h4X4 (fun h => hR10 (by rw [h, Polynomial.eval_zero]))
  have hrm4 :
      Polynomial.rootMultiplicity β (Polynomial.X - Polynomial.C (4 : K) : Polynomial K) = 0 := by
    rw [Polynomial.rootMultiplicity_X_sub_C]; simp [hβ4]
  have hrmX : Polynomial.rootMultiplicity β (Polynomial.X : Polynomial K) = 0 := by
    have h : (Polynomial.X : Polynomial K) = Polynomial.X - Polynomial.C 0 := by simp
    rw [h, Polynomial.rootMultiplicity_X_sub_C]; simp [hβ0]
  have hrmR10 : Polynomial.rootMultiplicity β R10 = 0 :=
    Polynomial.rootMultiplicity_eq_zero (p := R10) (x := β) hR10
  have hrmR4 : Polynomial.rootMultiplicity β R4 = 1 := by
    have hR4ne : R4 ≠ 0 :=
      fun h => hR4d (by rw [h, Polynomial.derivative_zero, Polynomial.eval_zero])
    have h1 : 1 ≤ Polynomial.rootMultiplicity β R4 := by
      rw [Polynomial.le_rootMultiplicity_iff hR4ne]
      simpa using (Polynomial.dvd_iff_isRoot (p := R4) (a := β)).mpr hR4
    have h2 : Polynomial.rootMultiplicity β R4 ≤ 1 := by
      rw [Polynomial.rootMultiplicity_le_iff hR4ne]
      intro hdvd
      exact hR4d ((Commons.Algebra.Polynomial.dvd_sq_X_sub_C_iff R4 β).mp hdvd).2
    omega
  rw [cden,
    Polynomial.rootMultiplicity_mul (p := (Polynomial.X - Polynomial.C (4 : K)) * Polynomial.X * R4)
      (q := R10) h4X410,
    Polynomial.rootMultiplicity_mul (p := (Polynomial.X - Polynomial.C (4 : K)) * Polynomial.X)
      (q := R4) h4X4,
    Polynomial.rootMultiplicity_mul (p := (Polynomial.X - Polynomial.C (4 : K)))
      (q := Polynomial.X) h4X,
    hrm4, hrmX, hrmR4, hrmR10]

/-! ## The residue numerator -/

/-- The "residue numerator" `Λnum·(X-β) - 3·(y-4)·y·R₄·R₁₀`. -/
noncomputable def residueNum {K : Type*} [Field K] (R4 R10 Λnum : Polynomial K) (β : K) :
    Polynomial K :=
  Λnum * (Polynomial.X - Polynomial.C β) - Polynomial.C 3 * cden R4 R10

/-- The derivative, at `β`, of the residue numerator (when `β` is a root of `R₄`). -/
theorem derivative_residueNum {R4 R10 Λnum : Polynomial K} {β : K} (hR4 : R4.eval β = 0) :
    (residueNum R4 R10 Λnum β).derivative.eval β
      = Λnum.eval β - 3 * ((β - 4) * β * R4.derivative.eval β * R10.eval β) := by
  have hd1 : (Λnum * (Polynomial.X - Polynomial.C β)).derivative.eval β = Λnum.eval β := by
    rw [Polynomial.derivative_mul, Polynomial.derivative_X_sub_C, mul_one]
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_X,
      Polynomial.eval_C]
    ring
  have hd2 : (Polynomial.C 3 * cden R4 R10).derivative.eval β
      = 3 * ((β - 4) * β * R4.derivative.eval β * R10.eval β) := by
    rw [Polynomial.derivative_mul, Polynomial.derivative_C, zero_mul, zero_add]
    simp only [Polynomial.eval_mul, Polynomial.eval_C]
    rw [derivative_eval_cden hR4]
  rw [residueNum, Polynomial.derivative_sub, Polynomial.eval_sub, hd1, hd2]

/-- **`(X-β)²` divides the residue numerator at a simple root `β` of `R₄`.**  This is the
algebraic content of the residue `+3` of `c₃/c₄` at `β`: it says that
`Λnum/((y-4)·y·R₄·R₁₀) - 3/(y-β)` is regular at `β`. -/
theorem dvd_sq_X_sub_C_residueNum {R4 R10 Λnum : Polynomial K} {β : K} (hR4 : R4.eval β = 0)
    (hΛ : Λnum.eval β = 3 * (β - 4) * β * R4.derivative.eval β * R10.eval β) :
    (Polynomial.X - Polynomial.C β) ^ 2 ∣ residueNum R4 R10 Λnum β := by
  rw [Commons.Algebra.Polynomial.dvd_sq_X_sub_C_iff]
  refine ⟨?_, ?_⟩
  · rw [residueNum]
    simp only [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_X, Polynomial.eval_C,
      eval_cden hR4]
    ring
  · rw [derivative_residueNum hR4, hΛ]
    ring

/-! ## The algebraic rearrangement of `γ₃ - 3/(y-β)` -/

/-- `γ₃ - 3/(y-β)` written over the common denominator `(y-4)·y·R₄·R₁₀·(y-β)`. -/
theorem sub_div_identity {R4 R10 Λnum : Polynomial K} {β : K}
    (hden : cden R4 R10 ≠ 0) (hXβ : (Polynomial.X - Polynomial.C β : Polynomial K) ≠ 0) :
    algebraMap (Polynomial K) (RatFunc K) Λnum
        / algebraMap (Polynomial K) (RatFunc K) (cden R4 R10)
      - algebraMap (Polynomial K) (RatFunc K) (Polynomial.C 3)
        * linFactor (K := K) β ^ (-1 : ℤ)
    = algebraMap (Polynomial K) (RatFunc K) (residueNum R4 R10 Λnum β)
      / algebraMap (Polynomial K) (RatFunc K) (cden R4 R10 * (Polynomial.X - Polynomial.C β)) := by
  have h1 : algebraMap (Polynomial K) (RatFunc K) (cden R4 R10) ≠ 0 :=
    RatFunc.algebraMap_ne_zero hden
  have h2 : algebraMap (Polynomial K) (RatFunc K) (Polynomial.X - Polynomial.C β) ≠ 0 :=
    RatFunc.algebraMap_ne_zero hXβ
  rw [residueNum, linFactor, zpow_neg_one, ← div_eq_mul_inv,
    div_sub_div (algebraMap (Polynomial K) (RatFunc K) Λnum)
      (algebraMap (Polynomial K) (RatFunc K) (Polynomial.C 3)) h1 h2]
  congr 1
  · rw [← map_mul, ← map_mul, ← map_sub]
    congr 1
    ring
  · rw [← map_mul]

/-- **The local data at a simple root `β` of `R₄`.**  The residue of `γ₃ = c₃/c₄` at `β` is `+3`,
i.e. `γ₃ - 3/(y-β)` is regular at `β`.  Formally: `ord_β(γ₃ - 3·(X-β)^{-1}) ≥ 0`. -/
theorem residual_gamma3_at_root_of_R4 {R4 R10 Λnum : Polynomial K} {β : K}
    (hR4 : R4.eval β = 0) (hR4d : R4.derivative.eval β ≠ 0) (hR10 : R10.eval β ≠ 0)
    (hβ0 : β ≠ 0) (hβ4 : β ≠ 4)
    (hΛ : Λnum.eval β = 3 * (β - 4) * β * R4.derivative.eval β * R10.eval β) :
    (0 : WithTop ℤ) ≤ ordAtT β
      (algebraMap (Polynomial K) (RatFunc K) Λnum
          / algebraMap (Polynomial K) (RatFunc K) (cden R4 R10)
        - algebraMap (Polynomial K) (RatFunc K) (Polynomial.C 3)
          * linFactor (K := K) β ^ (-1 : ℤ)) := by
  classical
  have hden : cden R4 R10 ≠ 0 := cden_ne_zero hR4d hR10
  have hXβ : (Polynomial.X - Polynomial.C β : Polynomial K) ≠ 0 := Polynomial.X_sub_C_ne_zero β
  rw [sub_div_identity hden hXβ]
  set A : Polynomial K := residueNum R4 R10 Λnum β with hA
  set B : Polynomial K := cden R4 R10 * (Polynomial.X - Polynomial.C β) with hB
  have hB0 : B ≠ 0 := by rw [hB]; exact mul_ne_zero hden hXβ
  have hdvd : (Polynomial.X - Polynomial.C β) ^ 2 ∣ A := by
    rw [hA]; exact dvd_sq_X_sub_C_residueNum hR4 hΛ
  change (0 : WithTop ℤ) ≤ ordAtT β (algebraMap (Polynomial K) (RatFunc K) A
    / algebraMap (Polynomial K) (RatFunc K) B)
  by_cases hA0 : A = 0
  · rw [hA0, map_zero, zero_div]
    simp [ordAtT]
  · have hdiv : algebraMap (Polynomial K) (RatFunc K) A / algebraMap (Polynomial K) (RatFunc K) B
        ≠ 0 := div_ne_zero (RatFunc.algebraMap_ne_zero hA0) (RatFunc.algebraMap_ne_zero hB0)
    rw [ordAtT_def β hdiv,
      ordAt_div β (RatFunc.algebraMap_ne_zero hA0) (RatFunc.algebraMap_ne_zero hB0),
      ordAt_algebraMap, ordAt_algebraMap, ← WithTop.coe_zero, WithTop.coe_le_coe]
    have hrmA : 2 ≤ Polynomial.rootMultiplicity β A := by
      rw [Polynomial.le_rootMultiplicity_iff hA0]
      exact hdvd
    have hrmB : Polynomial.rootMultiplicity β B = 2 := by
      rw [hB, Polynomial.rootMultiplicity_mul (mul_ne_zero hden hXβ),
        rootMultiplicity_cden hR4 hR4d hR10 hβ0 hβ4]
      have hself : Polynomial.rootMultiplicity β
          (Polynomial.X - Polynomial.C β : Polynomial K) = 1 := by
        rw [Polynomial.rootMultiplicity_X_sub_C]; simp
      rw [hself]
    omega

/-! ## The local data at a simple root of `R₁₀` -/

/-- The order of `cden R4 R10` at a simple root `γ` of `R₁₀` (with `γ ∉ {0,4}`) is `1`. -/
theorem rootMultiplicity_cden_R10 {R4 R10 : Polynomial K} {γ : K} (hR10 : R10.eval γ = 0)
    (hR10d : R10.derivative.eval γ ≠ 0) (hR4 : R4.eval γ ≠ 0) (hγ0 : γ ≠ 0) (hγ4 : γ ≠ 4) :
    Polynomial.rootMultiplicity γ (cden R4 R10) = 1 := by
  classical
  have h4 : (Polynomial.X - Polynomial.C (4 : K) : Polynomial K) ≠ 0 :=
    Polynomial.X_sub_C_ne_zero 4
  have h4X : (Polynomial.X - Polynomial.C (4 : K) : Polynomial K) * Polynomial.X ≠ 0 :=
    mul_ne_zero h4 Polynomial.X_ne_zero
  have h4X4 : (Polynomial.X - Polynomial.C (4 : K) : Polynomial K) * Polynomial.X * R4 ≠ 0 :=
    mul_ne_zero h4X (fun h => hR4 (by rw [h, Polynomial.eval_zero]))
  have h4X410 :
      (Polynomial.X - Polynomial.C (4 : K) : Polynomial K) * Polynomial.X * R4 * R10 ≠ 0 :=
    mul_ne_zero h4X4 (fun h => hR10d (by rw [h, Polynomial.derivative_zero, Polynomial.eval_zero]))
  have hrm4 :
      Polynomial.rootMultiplicity γ (Polynomial.X - Polynomial.C (4 : K) : Polynomial K) = 0 := by
    rw [Polynomial.rootMultiplicity_X_sub_C]; simp [hγ4]
  have hrmX : Polynomial.rootMultiplicity γ (Polynomial.X : Polynomial K) = 0 := by
    have h : (Polynomial.X : Polynomial K) = Polynomial.X - Polynomial.C 0 := by simp
    rw [h, Polynomial.rootMultiplicity_X_sub_C]; simp [hγ0]
  have hrmR4 : Polynomial.rootMultiplicity γ R4 = 0 :=
    Polynomial.rootMultiplicity_eq_zero (p := R4) (x := γ) hR4
  have hrmR10 : Polynomial.rootMultiplicity γ R10 = 1 := by
    have hne : R10 ≠ 0 :=
      fun h => hR10d (by rw [h, Polynomial.derivative_zero, Polynomial.eval_zero])
    have h1 : 1 ≤ Polynomial.rootMultiplicity γ R10 := by
      rw [Polynomial.le_rootMultiplicity_iff hne]
      simpa using (Polynomial.dvd_iff_isRoot (p := R10) (a := γ)).mpr hR10
    have h2 : Polynomial.rootMultiplicity γ R10 ≤ 1 := by
      rw [Polynomial.rootMultiplicity_le_iff hne]
      intro hdvd
      exact hR10d ((Commons.Algebra.Polynomial.dvd_sq_X_sub_C_iff R10 γ).mp hdvd).2
    omega
  rw [cden,
    Polynomial.rootMultiplicity_mul (p := (Polynomial.X - Polynomial.C (4 : K)) * Polynomial.X * R4)
      (q := R10) h4X410,
    Polynomial.rootMultiplicity_mul (p := (Polynomial.X - Polynomial.C (4 : K)) * Polynomial.X)
      (q := R4) h4X4,
    Polynomial.rootMultiplicity_mul (p := (Polynomial.X - Polynomial.C (4 : K)))
      (q := Polynomial.X) h4X,
    hrm4, hrmX, hrmR4, hrmR10]

/-- The "residue numerator" of `γ₃ + 1/(y-γ)`: `Λnum·(X-γ) + (y-4)·y·R₄·R₁₀`. -/
noncomputable def residueNumG {K : Type*} [Field K] (R4 R10 Λnum : Polynomial K) (γ : K) :
    Polynomial K :=
  Λnum * (Polynomial.X - Polynomial.C γ) + cden R4 R10

/-- The derivative, at `γ`, of `residueNumG` (when `γ` is a root of `R₁₀`). -/
theorem derivative_residueNumG {R4 R10 Λnum : Polynomial K} {γ : K} (hR10 : R10.eval γ = 0) :
    (residueNumG R4 R10 Λnum γ).derivative.eval γ
      = Λnum.eval γ + (γ - 4) * γ * R4.eval γ * R10.derivative.eval γ := by
  have hd1 : (Λnum * (Polynomial.X - Polynomial.C γ)).derivative.eval γ = Λnum.eval γ := by
    rw [Polynomial.derivative_mul, Polynomial.derivative_X_sub_C, mul_one]
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_X,
      Polynomial.eval_C]
    ring
  have hd2 : (cden R4 R10).derivative.eval γ
      = (γ - 4) * γ * R4.eval γ * R10.derivative.eval γ := by
    rw [cden]
    simp only [Polynomial.derivative_mul, Polynomial.derivative_sub, Polynomial.derivative_X,
      Polynomial.derivative_C]
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_sub,
      Polynomial.eval_X, Polynomial.eval_C, hR10]
    ring
  rw [residueNumG, Polynomial.derivative_add, Polynomial.eval_add, hd1, hd2]

/-- **`(X-γ)²` divides the residue numerator at a simple root `γ` of `R₁₀`** (residue `-1`). -/
theorem dvd_sq_X_sub_C_residueNumG {R4 R10 Λnum : Polynomial K} {γ : K} (hR10 : R10.eval γ = 0)
    (hΛ : Λnum.eval γ = -(γ - 4) * γ * R4.eval γ * R10.derivative.eval γ) :
    (Polynomial.X - Polynomial.C γ) ^ 2 ∣ residueNumG R4 R10 Λnum γ := by
  rw [Commons.Algebra.Polynomial.dvd_sq_X_sub_C_iff]
  refine ⟨?_, ?_⟩
  · rw [residueNumG]
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_X,
      Polynomial.eval_C, eval_cden_R10 hR10]
    ring
  · rw [derivative_residueNumG hR10, hΛ]
    ring

/-- `γ₃ + 1/(y-γ)` over the common denominator `(y-4)·y·R₄·R₁₀·(y-γ)`. -/
theorem add_div_identity {R4 R10 Λnum : Polynomial K} {γ : K}
    (hden : cden R4 R10 ≠ 0) (hXγ : (Polynomial.X - Polynomial.C γ : Polynomial K) ≠ 0) :
    algebraMap (Polynomial K) (RatFunc K) Λnum
        / algebraMap (Polynomial K) (RatFunc K) (cden R4 R10)
      + algebraMap (Polynomial K) (RatFunc K) (Polynomial.C 1)
        * linFactor (K := K) γ ^ (-1 : ℤ)
    = algebraMap (Polynomial K) (RatFunc K) (residueNumG R4 R10 Λnum γ)
      / algebraMap (Polynomial K) (RatFunc K) (cden R4 R10 * (Polynomial.X - Polynomial.C γ)) := by
  have h1 : algebraMap (Polynomial K) (RatFunc K) (cden R4 R10) ≠ 0 :=
    RatFunc.algebraMap_ne_zero hden
  have h2 : algebraMap (Polynomial K) (RatFunc K) (Polynomial.X - Polynomial.C γ) ≠ 0 :=
    RatFunc.algebraMap_ne_zero hXγ
  rw [residueNumG, linFactor, zpow_neg_one, ← div_eq_mul_inv,
    div_add_div (algebraMap (Polynomial K) (RatFunc K) Λnum)
      (algebraMap (Polynomial K) (RatFunc K) (Polynomial.C 1)) h1 h2]
  congr 1
  · rw [← map_mul, ← map_mul, ← map_add]
    congr 1
    simp only [Polynomial.C_1, mul_one]
  · rw [← map_mul]

/-- **The local data at a simple root `γ` of `R₁₀`.**  The residue of `γ₃ = c₃/c₄` at `γ` is `-1`,
i.e. `γ₃ + 1/(y-γ)` is regular at `γ`.  Formally: `ord_γ(γ₃ + (X-γ)^{-1}) ≥ 0`. -/
theorem residual_gamma3_at_root_of_R10 {R4 R10 Λnum : Polynomial K} {γ : K}
    (hR10 : R10.eval γ = 0) (hR10d : R10.derivative.eval γ ≠ 0) (hR4 : R4.eval γ ≠ 0)
    (hγ0 : γ ≠ 0) (hγ4 : γ ≠ 4)
    (hΛ : Λnum.eval γ = -(γ - 4) * γ * R4.eval γ * R10.derivative.eval γ) :
    (0 : WithTop ℤ) ≤ ordAtT γ
      (algebraMap (Polynomial K) (RatFunc K) Λnum
          / algebraMap (Polynomial K) (RatFunc K) (cden R4 R10)
        + algebraMap (Polynomial K) (RatFunc K) (Polynomial.C 1)
          * linFactor (K := K) γ ^ (-1 : ℤ)) := by
  classical
  have hden : cden R4 R10 ≠ 0 :=
    cden_ne_zero_of_ne_zero (fun h => hR4 (by rw [h, Polynomial.eval_zero]))
      (fun h => hR10d (by rw [h, Polynomial.derivative_zero, Polynomial.eval_zero]))
  have hXγ : (Polynomial.X - Polynomial.C γ : Polynomial K) ≠ 0 := Polynomial.X_sub_C_ne_zero γ
  rw [add_div_identity hden hXγ]
  set A : Polynomial K := residueNumG R4 R10 Λnum γ with hA
  set B : Polynomial K := cden R4 R10 * (Polynomial.X - Polynomial.C γ) with hB
  have hB0 : B ≠ 0 := by rw [hB]; exact mul_ne_zero hden hXγ
  have hdvd : (Polynomial.X - Polynomial.C γ) ^ 2 ∣ A := by
    rw [hA]; exact dvd_sq_X_sub_C_residueNumG hR10 hΛ
  change (0 : WithTop ℤ) ≤ ordAtT γ (algebraMap (Polynomial K) (RatFunc K) A
    / algebraMap (Polynomial K) (RatFunc K) B)
  by_cases hA0 : A = 0
  · rw [hA0, map_zero, zero_div]
    simp [ordAtT]
  · have hdiv : algebraMap (Polynomial K) (RatFunc K) A / algebraMap (Polynomial K) (RatFunc K) B
        ≠ 0 := div_ne_zero (RatFunc.algebraMap_ne_zero hA0) (RatFunc.algebraMap_ne_zero hB0)
    rw [ordAtT_def γ hdiv,
      ordAt_div γ (RatFunc.algebraMap_ne_zero hA0) (RatFunc.algebraMap_ne_zero hB0),
      ordAt_algebraMap, ordAt_algebraMap, ← WithTop.coe_zero, WithTop.coe_le_coe]
    have hrmA : 2 ≤ Polynomial.rootMultiplicity γ A := by
      rw [Polynomial.le_rootMultiplicity_iff hA0]
      exact hdvd
    have hrmB : Polynomial.rootMultiplicity γ B = 2 := by
      rw [hB, Polynomial.rootMultiplicity_mul (mul_ne_zero hden hXγ),
        rootMultiplicity_cden_R10 hR10 hR10d hR4 hγ0 hγ4]
      have hself : Polynomial.rootMultiplicity γ
          (Polynomial.X - Polynomial.C γ : Polynomial K) = 1 := by
        rw [Polynomial.rootMultiplicity_X_sub_C]; simp
      rw [hself]
    omega

/-- The order of `algebraMap c / algebraMap (cden R4 R10)` at a simple root `β` of `R₄` is at
least `-1` (used for the indices `i ≤ 2`, whose leading coefficients are not needed). -/
theorem ordAtT_div_cden_ge {R4 R10 : Polynomial K} {β : K} (hR4 : R4.eval β = 0)
    (hR4d : R4.derivative.eval β ≠ 0) (hR10 : R10.eval β ≠ 0) (hβ0 : β ≠ 0) (hβ4 : β ≠ 4)
    (c : Polynomial K) :
    ((-1 : ℤ) : WithTop ℤ) ≤ ordAtT β (algebraMap (Polynomial K) (RatFunc K) c
      / algebraMap (Polynomial K) (RatFunc K) (cden R4 R10)) := by
  have hden : cden R4 R10 ≠ 0 := cden_ne_zero hR4d hR10
  rcases eq_or_ne c 0 with hc | hc
  · rw [hc, map_zero, zero_div]
    simp [ordAtT]
  · have hdiv : algebraMap (Polynomial K) (RatFunc K) c
        / algebraMap (Polynomial K) (RatFunc K) (cden R4 R10) ≠ 0 :=
      div_ne_zero (RatFunc.algebraMap_ne_zero hc) (RatFunc.algebraMap_ne_zero hden)
    rw [ordAtT_def β hdiv,
      ordAt_div β (RatFunc.algebraMap_ne_zero hc) (RatFunc.algebraMap_ne_zero hden),
      ordAt_algebraMap, ordAt_algebraMap, rootMultiplicity_cden hR4 hR4d hR10 hβ0 hβ4,
      WithTop.coe_le_coe]
    have : (0 : ℤ) ≤ (Polynomial.rootMultiplicity β c : ℤ) := Int.natCast_nonneg _
    omega

/-- The order of `algebraMap c / algebraMap (cden R4 R10)` at a simple root `γ` of `R₁₀` is at
least `-1`. -/
theorem ordAtT_div_cden_ge_R10 {R4 R10 : Polynomial K} {γ : K} (hR10 : R10.eval γ = 0)
    (hR10d : R10.derivative.eval γ ≠ 0) (hR4 : R4.eval γ ≠ 0) (hγ0 : γ ≠ 0) (hγ4 : γ ≠ 4)
    (c : Polynomial K) :
    ((-1 : ℤ) : WithTop ℤ) ≤ ordAtT γ (algebraMap (Polynomial K) (RatFunc K) c
      / algebraMap (Polynomial K) (RatFunc K) (cden R4 R10)) := by
  have hden : cden R4 R10 ≠ 0 :=
    cden_ne_zero_of_ne_zero (fun h => hR4 (by rw [h, Polynomial.eval_zero]))
      (fun h => hR10d (by rw [h, Polynomial.derivative_zero, Polynomial.eval_zero]))
  rcases eq_or_ne c 0 with hc | hc
  · rw [hc, map_zero, zero_div]
    simp [ordAtT]
  · have hdiv : algebraMap (Polynomial K) (RatFunc K) c
        / algebraMap (Polynomial K) (RatFunc K) (cden R4 R10) ≠ 0 :=
      div_ne_zero (RatFunc.algebraMap_ne_zero hc) (RatFunc.algebraMap_ne_zero hden)
    rw [ordAtT_def γ hdiv,
      ordAt_div γ (RatFunc.algebraMap_ne_zero hc) (RatFunc.algebraMap_ne_zero hden),
      ordAt_algebraMap, ordAt_algebraMap, rootMultiplicity_cden_R10 hR10 hR10d hR4 hγ0 hγ4,
      WithTop.coe_le_coe]
    have : (0 : ℤ) ≤ (Polynomial.rootMultiplicity γ c : ℤ) := Int.natCast_nonneg _
    omega

/-! ## The pole-order bound at a simple root of `R₄` -/

/-- **The local bound `N_β ≥ 1` at a simple root `β` of `R₄`.**

Let `γ : Fin 5 → K(X)` be the coefficients `γᵢ = cᵢ/c₄` of the eliminated fourth-order equation
`Σᵢ (-1)ⁱ (γᵢ b)^{(i)} = -R` of the paper (`γ₄ = 1`, `γ₃ = c₃/c₄ = Λnum/((y-4)·y·R₄·R₁₀)`,
`γ₀,γ₁,γ₂ = cᵢ/c₄` with polynomial numerators).  If `β` is a *simple* root of `R₄` with
`β ∉ {0,4}`, `R₁₀(β) ≠ 0`, the residue of `Λnum/((y-4)yR₄R₁₀)` at `β` is `3`, and the
inhomogeneity `R` is regular at `β`, then the order of `b` at `β` is at least `1`.

The indicial polynomial at `β` is `(N-1)(N-2)(N-3)²`, whose integer roots are `1,2,3`; since
`ord_β(-R) ≥ 0` while the indicial order equals `N-4`, a value `N ≤ 0` would force the indicial
value to vanish, i.e. `N ∈ {1,2,3}` — a contradiction. -/
theorem local_bound_at_root_of_R4 {K : Type*} [Field K] [CharZero K]
    (D : Derivation K (RatFunc K) (RatFunc K))
    (hd : ∀ p : Polynomial K, D (algebraMap (Polynomial K) (RatFunc K) p)
      = algebraMap (Polynomial K) (RatFunc K) p.derivative)
    {β : K} {R4 R10 Λnum : Polynomial K}
    (hR4 : R4.eval β = 0) (hR4d : R4.derivative.eval β ≠ 0) (hR10 : R10.eval β ≠ 0)
    (hβ0 : β ≠ 0) (hβ4 : β ≠ 4)
    (hΛ : Λnum.eval β = 3 * (β - 4) * β * R4.derivative.eval β * R10.eval β)
    (b R : RatFunc K) (hb : b ≠ 0) (hR : (0 : WithTop ℤ) ≤ ordAtT β R)
    (γ : Fin 5 → RatFunc K)
    (hγ4 : γ 4 = 1)
    (hγ3 : γ 3 = algebraMap (Polynomial K) (RatFunc K) Λnum
      / algebraMap (Polynomial K) (RatFunc K) (cden R4 R10))
    (hγ012 : ∀ i : Fin 5, (i : ℕ) ≤ 2 → ∃ c : Polynomial K,
      γ i = algebraMap (Polynomial K) (RatFunc K) c
        / algebraMap (Polynomial K) (RatFunc K) (cden R4 R10))
    (hsys : (∑ i : Fin 5, (-1 : ℤ) ^ (i : ℕ) • ((fun x : RatFunc K => D x)^[i]) (γ i * b))
      = -R) :
    (1 : ℤ) ≤ ordAt β b := by
  classical
  by_contra hcon
  have hcon' : ordAt β b < 1 := not_le.mp hcon
  set N : ℤ := ordAt β b
  have hNle : N ≤ 0 := by omega
  obtain ⟨r, hr, hb'⟩ := exists_leading_term β hb
  let e : Fin 5 → ℤ := ![(-1 : ℤ), -1, -1, -1, 0]
  let lam : Fin 5 → K := ![0, 0, 0, 3, 1]
  have hfin : ∀ i : Fin 5, e i - ((i : ℕ) : ℤ) = -4 ↔ (i = 3 ∨ i = 4) := by decide
  have hlow : ∀ i : Fin 5, (i : ℕ) ≤ 2 → e i = (-1 : ℤ) := by decide
  have he : ∀ i : Fin 5, e i - ((i : ℕ) : ℤ) ≠ -4 →
      ((e i : ℤ) : WithTop ℤ) ≤ ordAtT β (γ i) := by
    intro i hi
    have h3 : i ≠ 3 := fun h => hi ((hfin i).mpr (Or.inl h))
    have h4 : i ≠ 4 := fun h => hi ((hfin i).mpr (Or.inr h))
    have hle : (i : ℕ) ≤ 2 := by
      have hlt := i.isLt
      omega
    obtain ⟨c, hc⟩ := hγ012 i hle
    rw [hc, hlow i hle]
    exact ordAtT_div_cden_ge hR4 hR4d hR10 hβ0 hβ4 c
  have hm : ∀ i : Fin 5, -4 ≤ e i - ((i : ℕ) : ℤ) := by decide
  have hlam : ∀ i : Fin 5, e i - ((i : ℕ) : ℤ) = -4 →
      (((e i + 1 : ℤ)) : WithTop ℤ) ≤ ordAtT β (γ i
        - algebraMap (Polynomial K) (RatFunc K) (Polynomial.C (lam i))
          * linFactor (K := K) β ^ (e i)) := by
    intro i hi
    rcases (hfin i).mp hi with h | h
    · subst h
      have hc1 : (((e 3 + 1 : ℤ)) : WithTop ℤ) = (0 : WithTop ℤ) := by
        rw [show e 3 = (-1 : ℤ) from rfl]; norm_num
      have hl3 : lam 3 = (3 : K) := rfl
      rw [hc1, hl3, hγ3]
      exact residual_gamma3_at_root_of_R4 hR4 hR4d hR10 hβ0 hβ4 hΛ
    · subst h
      rw [show e 4 = (0 : ℤ) from rfl, show lam 4 = (1 : K) from rfl, hγ4]
      have hc : (((0 : ℤ) + 1 : ℤ) : WithTop ℤ) = (1 : WithTop ℤ) := by norm_num
      rw [hc]
      simp only [map_one, zpow_zero, mul_one, sub_self]
      simp [ordAtT]
  have hP : (∑ i ∈ Finset.univ.filter (fun i : Fin 5 => e i - ((i : ℕ) : ℤ) = -4),
      (-1 : ℤ) ^ (i : ℕ) • (lam i
        * ∏ j ∈ Finset.range (i : ℕ), ((N + e i - (j : ℤ) : ℤ) : K))) ≠ 0 := by
    have hval : (∑ i ∈ Finset.univ.filter (fun i : Fin 5 => e i - ((i : ℕ) : ℤ) = -4),
        (-1 : ℤ) ^ (i : ℕ) • (lam i
          * ∏ j ∈ Finset.range (i : ℕ), ((N + e i - (j : ℤ) : ℤ) : K)))
        = ((N - 1 : ℤ) : K) * ((N - 2 : ℤ) : K) * ((N - 3 : ℤ) : K) * ((N - 3 : ℤ) : K) := by
      rw [show (Finset.univ.filter (fun i : Fin 5 => e i - ((i : ℕ) : ℤ) = -4))
        = ({3, 4} : Finset (Fin 5)) from by decide]
      rw [Finset.sum_pair (by decide : (3 : Fin 5) ≠ 4)]
      simp only [show (lam (3 : Fin 5)) = (3 : K) from rfl,
        show (lam (4 : Fin 5)) = (1 : K) from rfl,
        show (e (3 : Fin 5)) = (-1 : ℤ) from rfl,
        show (e (4 : Fin 5)) = (0 : ℤ) from rfl,
        show (((3 : Fin 5) : ℕ)) = 3 from rfl, show (((4 : Fin 5) : ℕ)) = 4 from rfl,
        Finset.prod_range_succ, Finset.prod_range_zero, zero_add]
      push_cast
      rw [show ((N : ℤ) : K) = ((N - 3 : ℤ) : K) + 3 from by
        rw [Int.cast_sub, Int.cast_ofNat]; ring]
      ring
    rw [hval]
    refine mul_ne_zero (mul_ne_zero (mul_ne_zero ?_ ?_) ?_) ?_
    · rw [Int.cast_ne_zero]; omega
    · rw [Int.cast_ne_zero]; omega
    · rw [Int.cast_ne_zero]; omega
    · rw [Int.cast_ne_zero]; omega
  have hmain := ordAtT_adjoint_eq_of_indicial_le D hd β b hb N rfl r hr hb' γ e lam (-4)
    he hm hlam hP
  rw [hsys, ordAtT_neg] at hmain
  have hthis : (0 : WithTop ℤ) ≤ ((N + (-4) : ℤ) : WithTop ℤ) := by
    rw [← hmain]; exact hR
  rw [← WithTop.coe_zero, WithTop.coe_le_coe] at hthis
  omega

/-! ## The pole-order bound at a simple root of `R₁₀` -/

/-- **The local bound `N_γ ≥ -1` at a simple root `γ` of `R₁₀`.**

The exact analogue of `local_bound_at_root_of_R4`: now `γ` is a simple root of `R₁₀` with
`γ ∉ {0,4}`, `R₄(γ) ≠ 0`, and the residue of `Λnum/((y-4)yR₄R₁₀)` at `γ` is `-1`.  The indicial
polynomial is `(N-1)(N-2)(N-3)(N+1)`, whose integer roots are `-1, 1, 2, 3`, so a value
`N ≤ -2` forces the indicial value to vanish — impossible since it is `(N-1)(N-2)(N-3)(N+1)`. -/
theorem local_bound_at_root_of_R10 {K : Type*} [Field K] [CharZero K]
    (D : Derivation K (RatFunc K) (RatFunc K))
    (hd : ∀ p : Polynomial K, D (algebraMap (Polynomial K) (RatFunc K) p)
      = algebraMap (Polynomial K) (RatFunc K) p.derivative)
    {γ : K} {R4 R10 Λnum : Polynomial K}
    (hR10 : R10.eval γ = 0) (hR10d : R10.derivative.eval γ ≠ 0) (hR4 : R4.eval γ ≠ 0)
    (hγ0 : γ ≠ 0) (hγ4 : γ ≠ 4)
    (hΛ : Λnum.eval γ = -(γ - 4) * γ * R4.eval γ * R10.derivative.eval γ)
    (b R : RatFunc K) (hb : b ≠ 0) (hR : (0 : WithTop ℤ) ≤ ordAtT γ R)
    (g : Fin 5 → RatFunc K)
    (hg4 : g 4 = 1)
    (hg3 : g 3 = algebraMap (Polynomial K) (RatFunc K) Λnum
      / algebraMap (Polynomial K) (RatFunc K) (cden R4 R10))
    (hg012 : ∀ i : Fin 5, (i : ℕ) ≤ 2 → ∃ c : Polynomial K,
      g i = algebraMap (Polynomial K) (RatFunc K) c
        / algebraMap (Polynomial K) (RatFunc K) (cden R4 R10))
    (hsys : (∑ i : Fin 5, (-1 : ℤ) ^ (i : ℕ) • ((fun x : RatFunc K => D x)^[i]) (g i * b))
      = -R) :
    (-1 : ℤ) ≤ ordAt γ b := by
  classical
  by_contra hcon
  have hcon' : ordAt γ b < -1 := not_le.mp hcon
  set N : ℤ := ordAt γ b
  have hNle : N ≤ -2 := by omega
  obtain ⟨r, hr, hb'⟩ := exists_leading_term γ hb
  let e : Fin 5 → ℤ := ![(-1 : ℤ), -1, -1, -1, 0]
  let lam : Fin 5 → K := ![0, 0, 0, -1, 1]
  have hfin : ∀ i : Fin 5, e i - ((i : ℕ) : ℤ) = -4 ↔ (i = 3 ∨ i = 4) := by decide
  have hlow : ∀ i : Fin 5, (i : ℕ) ≤ 2 → e i = (-1 : ℤ) := by decide
  have he : ∀ i : Fin 5, e i - ((i : ℕ) : ℤ) ≠ -4 →
      ((e i : ℤ) : WithTop ℤ) ≤ ordAtT γ (g i) := by
    intro i hi
    have h3 : i ≠ 3 := fun h => hi ((hfin i).mpr (Or.inl h))
    have h4 : i ≠ 4 := fun h => hi ((hfin i).mpr (Or.inr h))
    have hle : (i : ℕ) ≤ 2 := by
      have hlt := i.isLt
      omega
    obtain ⟨c, hc⟩ := hg012 i hle
    rw [hc, hlow i hle]
    exact ordAtT_div_cden_ge_R10 hR10 hR10d hR4 hγ0 hγ4 c
  have hm : ∀ i : Fin 5, -4 ≤ e i - ((i : ℕ) : ℤ) := by decide
  have hlam : ∀ i : Fin 5, e i - ((i : ℕ) : ℤ) = -4 →
      (((e i + 1 : ℤ)) : WithTop ℤ) ≤ ordAtT γ (g i
        - algebraMap (Polynomial K) (RatFunc K) (Polynomial.C (lam i))
          * linFactor (K := K) γ ^ (e i)) := by
    intro i hi
    rcases (hfin i).mp hi with h | h
    · subst h
      rw [show e 3 = (-1 : ℤ) from rfl, show lam 3 = (-1 : K) from rfl, hg3]
      have hc1 : (((-1 : ℤ) + 1 : ℤ) : WithTop ℤ) = (0 : WithTop ℤ) := by norm_num
      rw [hc1]
      have hneg : algebraMap (Polynomial K) (RatFunc K) (Polynomial.C (-1 : K))
            * linFactor (K := K) γ ^ (-1 : ℤ)
          = -(algebraMap (Polynomial K) (RatFunc K) (Polynomial.C (1 : K))
            * linFactor (K := K) γ ^ (-1 : ℤ)) := by
        rw [show (-1 : K) = -(1 : K) from rfl, Polynomial.C_neg, map_neg]
        ring
      rw [hneg, sub_neg_eq_add]
      exact residual_gamma3_at_root_of_R10 hR10 hR10d hR4 hγ0 hγ4 hΛ
    · subst h
      rw [show e 4 = (0 : ℤ) from rfl, show lam 4 = (1 : K) from rfl, hg4]
      have hc : (((0 : ℤ) + 1 : ℤ) : WithTop ℤ) = (1 : WithTop ℤ) := by norm_num
      rw [hc]
      simp only [map_one, zpow_zero, mul_one, sub_self]
      simp [ordAtT]
  have hP : (∑ i ∈ Finset.univ.filter (fun i : Fin 5 => e i - ((i : ℕ) : ℤ) = -4),
      (-1 : ℤ) ^ (i : ℕ) • (lam i
        * ∏ j ∈ Finset.range (i : ℕ), ((N + e i - (j : ℤ) : ℤ) : K))) ≠ 0 := by
    have hval : (∑ i ∈ Finset.univ.filter (fun i : Fin 5 => e i - ((i : ℕ) : ℤ) = -4),
        (-1 : ℤ) ^ (i : ℕ) • (lam i
          * ∏ j ∈ Finset.range (i : ℕ), ((N + e i - (j : ℤ) : ℤ) : K)))
        = ((N - 1 : ℤ) : K) * ((N - 2 : ℤ) : K) * ((N - 3 : ℤ) : K) * ((N + 1 : ℤ) : K) := by
      rw [show (Finset.univ.filter (fun i : Fin 5 => e i - ((i : ℕ) : ℤ) = -4))
        = ({3, 4} : Finset (Fin 5)) from by decide]
      rw [Finset.sum_pair (by decide : (3 : Fin 5) ≠ 4)]
      simp only [show (lam (3 : Fin 5)) = (-1 : K) from rfl,
        show (lam (4 : Fin 5)) = (1 : K) from rfl,
        show (e (3 : Fin 5)) = (-1 : ℤ) from rfl,
        show (e (4 : Fin 5)) = (0 : ℤ) from rfl,
        show (((3 : Fin 5) : ℕ)) = 3 from rfl, show (((4 : Fin 5) : ℕ)) = 4 from rfl,
        Finset.prod_range_succ, Finset.prod_range_zero, zero_add]
      push_cast
      ring
    rw [hval]
    refine mul_ne_zero (mul_ne_zero (mul_ne_zero ?_ ?_) ?_) ?_
    · rw [Int.cast_ne_zero]; omega
    · rw [Int.cast_ne_zero]; omega
    · rw [Int.cast_ne_zero]; omega
    · rw [Int.cast_ne_zero]; omega
  have hmain := ordAtT_adjoint_eq_of_indicial_le D hd γ b hb N rfl r hr hb' g e lam (-4)
    he hm hlam hP
  rw [hsys, ordAtT_neg] at hmain
  have hthis : (0 : WithTop ℤ) ≤ ((N + (-4) : ℤ) : WithTop ℤ) := by
    rw [← hmain]; exact hR
  rw [← WithTop.coe_zero, WithTop.coe_le_coe] at hthis
  omega

/-! ## The bridge to the paper's polynomials `R₄, R₁₀, Λnum ∈ ℚ[a,b,y]`

`Submission/CDT/LLData` defines `R₄`, `R₁₀`, `Λnum` as elements of
`MvPolynomial (Fin 3) ℚ` (with `X 0 = a`, `X 1 = b`, `X 2 = y`).  Here we
specialise `a, b` to elements of a field `K` and keep `y` as the polynomial
variable; the divisibility lemmas of `LLData` (the residue computations) then
specialise to the "local data" hypotheses of the two local-bound theorems. -/

/-- Specialisation `ℚ[a,b,y] → K[y]` with `a ↦ a`, `b ↦ b`, `y ↦ X`. -/
noncomputable def spec {K : Type*} [CommRing K] [Algebra ℚ K] (a b : K) :
    MvPolynomial (Fin 3) ℚ →+* Polynomial K :=
  MvPolynomial.eval₂Hom (Polynomial.C.comp (algebraMap ℚ K))
    ![Polynomial.C a, Polynomial.C b, Polynomial.X]

theorem spec_X0 {K : Type*} [CommRing K] [Algebra ℚ K] (a b : K) :
    spec a b (MvPolynomial.X 0) = Polynomial.C a := by
  rw [spec, MvPolynomial.eval₂Hom_X']; rfl

theorem spec_X1 {K : Type*} [CommRing K] [Algebra ℚ K] (a b : K) :
    spec a b (MvPolynomial.X 1) = Polynomial.C b := by
  rw [spec, MvPolynomial.eval₂Hom_X']; rfl

theorem spec_X2 {K : Type*} [CommRing K] [Algebra ℚ K] (a b : K) :
    spec a b (MvPolynomial.X 2) = Polynomial.X := by
  rw [spec, MvPolynomial.eval₂Hom_X']; rfl

/-- The specialisation carries the partial derivative `∂/∂y` to `d/dX`. -/
theorem spec_pderiv {K : Type*} [CommRing K] [Algebra ℚ K] (a b : K)
    (p : MvPolynomial (Fin 3) ℚ) :
    spec a b (MvPolynomial.pderiv 2 p) = (spec a b p).derivative := by
  induction p using MvPolynomial.induction_on with
  | C r =>
      simp only [MvPolynomial.pderiv_C, map_zero, spec, MvPolynomial.eval₂Hom_C,
        RingHom.comp_apply, Polynomial.derivative_C]
  | add p q hp hq =>
      simp only [Derivation.map_add, map_add, hp, hq, Polynomial.derivative_add]
  | mul_X p n hp =>
      rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul, map_add, map_mul, map_mul, map_mul,
        Polynomial.derivative_mul, hp]
      have hn : n = 0 ∨ n = 1 ∨ n = 2 := by fin_cases n <;> simp
      rcases hn with rfl | rfl | rfl
      · rw [MvPolynomial.pderiv_X, Pi.single_eq_of_ne (by decide : (0 : Fin 3) ≠ 2), map_zero,
          spec_X0, Polynomial.derivative_C]
        ring
      · rw [MvPolynomial.pderiv_X, Pi.single_eq_of_ne (by decide : (1 : Fin 3) ≠ 2), map_zero,
          spec_X1, Polynomial.derivative_C]
        ring
      · rw [MvPolynomial.pderiv_X, Pi.single_eq_same, map_one, spec_X2, Polynomial.derivative_X]
        ring

/-- **The residue of `Λnum/((y-4)·y·R₄·R₁₀)` at a root `β` of `R₄` is `+3`.** -/
theorem spec_LambdaNum_eval_at_root_of_R4 {K : Type*} [Field K] [Algebra ℚ K] (a b β : K)
    (hR4 : (spec a b LL.R4).eval β = 0) :
    (spec a b LL.LambdaNum).eval β
      = 3 * (β - 4) * β * (spec a b LL.R4).derivative.eval β * (spec a b LL.R10).eval β := by
  obtain ⟨H, hH⟩ := LL.R4_dvd_LambdaNum_sub
  have h1 : spec a b LL.LambdaNum
      - 3 * Polynomial.X * (Polynomial.X - Polynomial.C (4 : K))
        * (spec a b LL.R4).derivative * (spec a b LL.R10)
      = spec a b (LL.R4 * H) := by
    have h := congrArg (spec a b) hH
    rw [map_sub] at h
    rw [← h]
    congr 1
    simp only [map_mul, map_sub, spec_pderiv, spec_X2, map_ofNat]
  rw [map_mul] at h1
  have h2 := congrArg (fun p : Polynomial K => p.eval β) h1
  simp only [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_X, Polynomial.eval_C,
    Polynomial.eval_ofNat, hR4, mul_zero, zero_mul] at h2
  rw [sub_eq_zero] at h2
  rw [h2]
  ring

/-- **The residue of `Λnum/((y-4)·y·R₄·R₁₀)` at a root `γ` of `R₁₀` is `-1`.** -/
theorem spec_LambdaNum_eval_at_root_of_R10 {K : Type*} [Field K] [Algebra ℚ K] (a b γ : K)
    (hR10 : (spec a b LL.R10).eval γ = 0) :
    (spec a b LL.LambdaNum).eval γ
      = -(γ - 4) * γ * (spec a b LL.R4).eval γ * (spec a b LL.R10).derivative.eval γ := by
  obtain ⟨H, hH⟩ := LL.R10_dvd_LambdaNum_add
  have h1 : spec a b LL.LambdaNum
      + Polynomial.X * (Polynomial.X - Polynomial.C (4 : K))
        * (spec a b LL.R4) * (spec a b LL.R10).derivative
      = spec a b (LL.R10 * H) := by
    have h := congrArg (spec a b) hH
    rw [map_add] at h
    rw [← h]
    congr 1
    simp only [map_mul, map_sub, spec_pderiv, spec_X2, map_ofNat]
  rw [map_mul] at h1
  have h2 := congrArg (fun p : Polynomial K => p.eval γ) h1
  simp only [Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_X,
    Polynomial.eval_C, Polynomial.eval_ofNat, hR10, mul_zero, zero_mul] at h2
  rw [add_eq_zero_iff_eq_neg] at h2
  rw [h2]
  ring

/-! ## The two local bounds for the paper's polynomials -/

/-- **`N_β ≥ 1` for the paper's `R₄, R₁₀, Λnum`.**  `local_bound_at_root_of_R4` with the residue
`Λnum(β) = 3(β-4)βR₄'(β)R₁₀(β)` supplied by `spec_LambdaNum_eval_at_root_of_R4`. -/
theorem local_bound_at_root_of_R4_spec {K : Type*} [Field K] [CharZero K]
    (D : Derivation K (RatFunc K) (RatFunc K))
    (hd : ∀ p : Polynomial K, D (algebraMap (Polynomial K) (RatFunc K) p)
      = algebraMap (Polynomial K) (RatFunc K) p.derivative)
    (a b β : K)
    (hR4 : (spec a b LL.R4).eval β = 0) (hR4d : (spec a b LL.R4).derivative.eval β ≠ 0)
    (hR10 : (spec a b LL.R10).eval β ≠ 0) (hβ0 : β ≠ 0) (hβ4 : β ≠ 4)
    (bb R : RatFunc K) (hb : bb ≠ 0) (hR : (0 : WithTop ℤ) ≤ ordAtT β R)
    (g : Fin 5 → RatFunc K)
    (hg4 : g 4 = 1)
    (hg3 : g 3 = algebraMap (Polynomial K) (RatFunc K) (spec a b LL.LambdaNum)
      / algebraMap (Polynomial K) (RatFunc K) (cden (spec a b LL.R4) (spec a b LL.R10)))
    (hg012 : ∀ i : Fin 5, (i : ℕ) ≤ 2 → ∃ c : Polynomial K,
      g i = algebraMap (Polynomial K) (RatFunc K) c
        / algebraMap (Polynomial K) (RatFunc K) (cden (spec a b LL.R4) (spec a b LL.R10)))
    (hsys : (∑ i : Fin 5, (-1 : ℤ) ^ (i : ℕ) • ((fun x : RatFunc K => D x)^[i]) (g i * bb))
      = -R) :
    (1 : ℤ) ≤ ordAt β bb :=
  local_bound_at_root_of_R4 D hd hR4 hR4d hR10 hβ0 hβ4
    (spec_LambdaNum_eval_at_root_of_R4 a b β hR4) bb R hb hR g hg4 hg3 hg012 hsys

/-- **`N_γ ≥ -1` for the paper's `R₄, R₁₀, Λnum`.** -/
theorem local_bound_at_root_of_R10_spec {K : Type*} [Field K] [CharZero K]
    (D : Derivation K (RatFunc K) (RatFunc K))
    (hd : ∀ p : Polynomial K, D (algebraMap (Polynomial K) (RatFunc K) p)
      = algebraMap (Polynomial K) (RatFunc K) p.derivative)
    (a b γ : K)
    (hR10 : (spec a b LL.R10).eval γ = 0) (hR10d : (spec a b LL.R10).derivative.eval γ ≠ 0)
    (hR4 : (spec a b LL.R4).eval γ ≠ 0) (hγ0 : γ ≠ 0) (hγ4 : γ ≠ 4)
    (bb R : RatFunc K) (hb : bb ≠ 0) (hR : (0 : WithTop ℤ) ≤ ordAtT γ R)
    (g : Fin 5 → RatFunc K)
    (hg4 : g 4 = 1)
    (hg3 : g 3 = algebraMap (Polynomial K) (RatFunc K) (spec a b LL.LambdaNum)
      / algebraMap (Polynomial K) (RatFunc K) (cden (spec a b LL.R4) (spec a b LL.R10)))
    (hg012 : ∀ i : Fin 5, (i : ℕ) ≤ 2 → ∃ c : Polynomial K,
      g i = algebraMap (Polynomial K) (RatFunc K) c
        / algebraMap (Polynomial K) (RatFunc K) (cden (spec a b LL.R4) (spec a b LL.R10)))
    (hsys : (∑ i : Fin 5, (-1 : ℤ) ^ (i : ℕ) • ((fun x : RatFunc K => D x)^[i]) (g i * bb))
      = -R) :
    (-1 : ℤ) ≤ ordAt γ bb :=
  local_bound_at_root_of_R10 D hd hR10 hR10d hR4 hγ0 hγ4
    (spec_LambdaNum_eval_at_root_of_R10 a b γ hR10) bb R hb hR g hg4 hg3 hg012 hsys

/-! ## The local bound at `α = 0` -/

/-- The order of `c/(X^k·d)` at `0` is at least `-k` (when `d(0) ≠ 0`). -/
theorem ordAtT_div_mul_ge {K : Type*} [Field K] {d : Polynomial K} (hd0 : d.eval 0 ≠ 0)
    (c : Polynomial K) (k : ℕ) :
    ((-(k : ℤ) : ℤ) : WithTop ℤ) ≤ ordAtT (0 : K)
      (algebraMap (Polynomial K) (RatFunc K) c
        / algebraMap (Polynomial K) (RatFunc K) (Polynomial.X ^ k * d)) := by
  have hd : d ≠ 0 := fun h => hd0 (by rw [h, Polynomial.eval_zero])
  have hX : (Polynomial.X : Polynomial K) ≠ 0 := Polynomial.X_ne_zero
  have hden : (Polynomial.X ^ k * d : Polynomial K) ≠ 0 := mul_ne_zero (pow_ne_zero _ hX) hd
  rcases eq_or_ne c 0 with hc | hc
  · rw [hc, map_zero, zero_div]
    simp [ordAtT]
  · have hrmden : Polynomial.rootMultiplicity (0 : K) (Polynomial.X ^ k * d) = k := by
      have := Polynomial.rootMultiplicity_mul_X_sub_C_pow (p := d) (a := (0 : K)) (n := k) hd
      have hXk : (Polynomial.X : Polynomial K) ^ k = (Polynomial.X - Polynomial.C (0 : K)) ^ k := by
        simp
      rw [← hXk] at this
      rw [mul_comm, this, Polynomial.rootMultiplicity_eq_zero (p := d) (x := 0) hd0, zero_add]
    rw [ordAtT_def 0 (div_ne_zero (RatFunc.algebraMap_ne_zero hc)
        (RatFunc.algebraMap_ne_zero hden)),
      ordAt_div 0 (RatFunc.algebraMap_ne_zero hc) (RatFunc.algebraMap_ne_zero hden),
      ordAt_algebraMap, ordAt_algebraMap, hrmden, WithTop.coe_le_coe]
    have : (0 : ℤ) ≤ (Polynomial.rootMultiplicity (0 : K) c : ℤ) := Int.natCast_nonneg _
    omega

/-- **The local data at `α = 0`.**  For a polynomial `c` whose `k`-th jet matches `lam·d` at `0`,
`c/(X^k·d) - lam/X^k` is regular at `0`. -/
theorem residual_at_zero {K : Type*} [Field K] {d : Polynomial K} (hd0 : d.eval 0 ≠ 0)
    {c : Polynomial K} {lam : K} {k : ℕ} (hval : (c - Polynomial.C lam * d).eval 0 = 0) :
    ((((1 : ℤ) - (k : ℤ)) : ℤ) : WithTop ℤ) ≤ ordAtT (0 : K)
      (algebraMap (Polynomial K) (RatFunc K) c
          / algebraMap (Polynomial K) (RatFunc K) (Polynomial.X ^ k * d)
        - algebraMap (Polynomial K) (RatFunc K) (Polynomial.C lam)
          * linFactor (K := K) 0 ^ (-(k : ℤ))) := by
  have hd : d ≠ 0 := fun h => hd0 (by rw [h, Polynomial.eval_zero])
  have hX : (Polynomial.X : Polynomial K) ≠ 0 := Polynomial.X_ne_zero
  have hden : (Polynomial.X ^ k * d : Polynomial K) ≠ 0 := mul_ne_zero (pow_ne_zero _ hX) hd
  have hlf : linFactor (K := K) 0 = algebraMap (Polynomial K) (RatFunc K) Polynomial.X := by
    rw [linFactor]; simp
  have hB' : algebraMap (Polynomial K) (RatFunc K) (Polynomial.X ^ k * d : Polynomial K)
      = algebraMap (Polynomial K) (RatFunc K) (Polynomial.X ^ k)
        * algebraMap (Polynomial K) (RatFunc K) d := map_mul _ _ _
  have h3 : ((algebraMap (Polynomial K) (RatFunc K) Polynomial.X : RatFunc K)) ^ (-(k : ℤ))
      = (algebraMap (Polynomial K) (RatFunc K) (Polynomial.X ^ k : Polynomial K) : RatFunc K)⁻¹ := by
    rw [zpow_neg, map_pow]
    rfl
  have hkey : algebraMap (Polynomial K) (RatFunc K) c
        / algebraMap (Polynomial K) (RatFunc K) (Polynomial.X ^ k * d)
      - algebraMap (Polynomial K) (RatFunc K) (Polynomial.C lam)
        * linFactor (K := K) 0 ^ (-(k : ℤ))
      = algebraMap (Polynomial K) (RatFunc K) (c - Polynomial.C lam * d)
        / algebraMap (Polynomial K) (RatFunc K) (Polynomial.X ^ k * d) := by
    have hd' : algebraMap (Polynomial K) (RatFunc K) d ≠ 0 := RatFunc.algebraMap_ne_zero hd
    have hA : algebraMap (Polynomial K) (RatFunc K) (Polynomial.X ^ k : Polynomial K) ≠ 0 :=
      RatFunc.algebraMap_ne_zero (pow_ne_zero _ hX)
    rw [hlf, h3, hB', ← div_eq_mul_inv]
    field_simp
    rw [← map_mul, ← map_sub]
    congr 1
    ring
  rw [hkey]
  rcases eq_or_ne (c - Polynomial.C lam * d) 0 with h0 | h0
  · rw [h0, map_zero, zero_div]
    simp [ordAtT]
  · have hrmden : Polynomial.rootMultiplicity (0 : K) (Polynomial.X ^ k * d) = k := by
      have := Polynomial.rootMultiplicity_mul_X_sub_C_pow (p := d) (a := (0 : K)) (n := k) hd
      have hXk : (Polynomial.X : Polynomial K) ^ k = (Polynomial.X - Polynomial.C (0 : K)) ^ k := by
        simp
      rw [← hXk] at this
      rw [mul_comm, this, Polynomial.rootMultiplicity_eq_zero (p := d) (x := 0) hd0, zero_add]
    have hrmnum : 1 ≤ Polynomial.rootMultiplicity (0 : K) (c - Polynomial.C lam * d) := by
      rw [Polynomial.le_rootMultiplicity_iff h0]
      have hX1 : (Polynomial.X - Polynomial.C (0 : K) : Polynomial K) = Polynomial.X := by simp
      rw [hX1, pow_one]
      simpa [Polynomial.C_0] using Polynomial.dvd_iff_isRoot.mpr hval
    rw [ordAtT_def 0 (div_ne_zero (RatFunc.algebraMap_ne_zero h0) (RatFunc.algebraMap_ne_zero hden)),
      ordAt_div 0 (RatFunc.algebraMap_ne_zero h0) (RatFunc.algebraMap_ne_zero hden),
      ordAt_algebraMap, ordAt_algebraMap, hrmden, WithTop.coe_le_coe]
    omega

/-- **The local bound `N_0 ≥ 0` at the branch point `y = 0`.**

With `c₄ = X³d`, `g₀ = c₀/c₄`, `g₁ = c₁/c₄`, `g₂ = c₂/(X²d)`, `g₃ = (X−4)Λnum/(Xd)`, `g₄ = 1`,
and the local data `d(0) ≠ 0`, `4c₁(0) = d(0)`, `4c₂(0) = 17d(0)`, `4Λnum(0) = −5d(0)`
(equivalently `λ = (·, 1/4, 17/4, 5, 1)`, the leading coefficients of the `γᵢ` at `0`), the order of
a solution `b` of the eliminated equation `Σᵢ(−1)ⁱ Dⁱ(gᵢb) = −R` at `0` is at least `0`, provided
`R` is a Laurent polynomial with support in `y^{−4},…,y^{1}`. -/
theorem local_bound_at_zero {K : Type*} [Field K] [CharZero K]
    (D : Derivation K (RatFunc K) (RatFunc K))
    (hd : ∀ p : Polynomial K, D (algebraMap (Polynomial K) (RatFunc K) p)
      = algebraMap (Polynomial K) (RatFunc K) p.derivative)
    {d c0 c1 c2 Λnum : Polynomial K}
    (hd0 : d.eval 0 ≠ 0)
    (hc1 : 4 * c1.eval 0 = d.eval 0)
    (hc2 : 4 * c2.eval 0 = 17 * d.eval 0)
    (hΛ : 4 * Λnum.eval 0 = -(5 * d.eval 0))
    (bb R : RatFunc K) (hb : bb ≠ 0) (hR : ((-4 : ℤ) : WithTop ℤ) ≤ ordAtT (0 : K) R)
    (g : Fin 5 → RatFunc K)
    (hg0 : g 0 = algebraMap (Polynomial K) (RatFunc K) c0
      / algebraMap (Polynomial K) (RatFunc K) (Polynomial.X ^ 3 * d))
    (hg1 : g 1 = algebraMap (Polynomial K) (RatFunc K) c1
      / algebraMap (Polynomial K) (RatFunc K) (Polynomial.X ^ 3 * d))
    (hg2 : g 2 = algebraMap (Polynomial K) (RatFunc K) c2
      / algebraMap (Polynomial K) (RatFunc K) (Polynomial.X ^ 2 * d))
    (hg3 : g 3 = algebraMap (Polynomial K) (RatFunc K) ((Polynomial.X - Polynomial.C 4) * Λnum)
      / algebraMap (Polynomial K) (RatFunc K) (Polynomial.X * d))
    (hg4 : g 4 = 1)
    (hsys : (∑ i : Fin 5, (-1 : ℤ) ^ (i : ℕ) • ((fun x : RatFunc K => D x)^[i]) (g i * bb))
      = -R) :
    (0 : ℤ) ≤ ordAt (0 : K) bb := by
  classical
  by_contra hcon
  have hcon' : ordAt (0 : K) bb < 0 := not_le.mp hcon
  set N : ℤ := ordAt (0 : K) bb
  have hNle : N ≤ -1 := by omega
  obtain ⟨r, hr, hb'⟩ := exists_leading_term (0 : K) hb
  let e : Fin 5 → ℤ := ![-3, -3, -2, -1, 0]
  let lam : Fin 5 → K := ![(1 / 4 : K), 1 / 4, 17 / 4, 5, 1]
  have hfin : ∀ i : Fin 5, e i - ((i : ℕ) : ℤ) = -4 ↔ (i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4) := by decide
  have hlow : ∀ i : Fin 5, i = 0 → e i = (-3 : ℤ) := by decide
  have he : ∀ i : Fin 5, e i - ((i : ℕ) : ℤ) ≠ -4 →
      ((e i : ℤ) : WithTop ℤ) ≤ ordAtT (0 : K) (g i) := by
    intro i hi
    have hne : i ≠ 1 := fun h => hi ((hfin i).mpr (Or.inl h))
    have hne2 : i ≠ 2 := fun h => hi ((hfin i).mpr (Or.inr (Or.inl h)))
    have hne3 : i ≠ 3 := fun h => hi ((hfin i).mpr (Or.inr (Or.inr (Or.inl h))))
    have hne4 : i ≠ 4 := fun h => hi ((hfin i).mpr (Or.inr (Or.inr (Or.inr h))))
    have h0 : i = 0 := by
      have := i.isLt
      omega
    subst h0
    rw [hg0, hlow 0 rfl]
    exact ordAtT_div_mul_ge hd0 c0 3
  have hm : ∀ i : Fin 5, -4 ≤ e i - ((i : ℕ) : ℤ) := by decide
  have hlam : ∀ i : Fin 5, e i - ((i : ℕ) : ℤ) = -4 →
      (((e i + 1 : ℤ)) : WithTop ℤ) ≤ ordAtT (0 : K) (g i
        - algebraMap (Polynomial K) (RatFunc K) (Polynomial.C (lam i))
          * linFactor (K := K) 0 ^ (e i)) := by
    intro i hi
    rcases (hfin i).mp hi with h | h | h | h
    · subst h
      rw [hg1]
      exact residual_at_zero hd0 (k := 3) (lam := (1 / 4 : K)) (by
        rw [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_C]
        have h4 : (4 : K) ≠ 0 := by norm_num
        have key : (1 / 4 : K) * d.eval 0 = c1.eval 0 := by
          calc (1 / 4 : K) * d.eval 0 = (4 : K)⁻¹ * d.eval 0 := by rw [one_div]
            _ = (4 : K)⁻¹ * (4 * c1.eval 0) := by rw [← hc1]
            _ = c1.eval 0 := by rw [← mul_assoc, inv_mul_cancel₀ h4, one_mul]
        rw [key, sub_self])
    · subst h
      rw [hg2]
      exact residual_at_zero hd0 (k := 2) (lam := (17 / 4 : K)) (by
        rw [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_C]
        have h4 : (4 : K) ≠ 0 := by norm_num
        have key : (17 / 4 : K) * d.eval 0 = c2.eval 0 := by
          calc (17 / 4 : K) * d.eval 0 = (17 * (4 : K)⁻¹) * d.eval 0 := by rw [div_eq_mul_inv]
            _ = (4 : K)⁻¹ * (17 * d.eval 0) := by ring
            _ = (4 : K)⁻¹ * (4 * c2.eval 0) := by rw [← hc2]
            _ = c2.eval 0 := by rw [← mul_assoc, inv_mul_cancel₀ h4, one_mul]
        rw [key, sub_self])
    · subst h
      rw [hg3, show e 3 = (-1 : ℤ) from rfl, show lam 3 = (5 : K) from rfl]
      have h3k := residual_at_zero hd0 (k := 1) (lam := (5 : K))
        (c := (Polynomial.X - Polynomial.C 4) * Λnum) (by
          have key : ((Polynomial.X - Polynomial.C 4) * Λnum).eval 0
              = (5 : K) * d.eval 0 := by
            rw [Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
            rw [show ((0 : K) - 4) * Λnum.eval 0 = -(4 * Λnum.eval 0) from by ring, hΛ, neg_neg]
          rw [Polynomial.eval_sub, key, Polynomial.eval_mul, Polynomial.eval_C, sub_self])
      simpa [pow_one] using h3k
    · subst h
      have hc : (((e 4 + 1 : ℤ)) : WithTop ℤ) = (1 : WithTop ℤ) := by
        rw [show e 4 = (0 : ℤ) from rfl]; norm_num
      rw [hc, hg4, show lam 4 = (1 : K) from rfl, show e 4 = (0 : ℤ) from rfl,
        zpow_zero, mul_one]
      simp only [map_one, sub_self]
      simp [ordAtT]
  have hP : (∑ i ∈ Finset.univ.filter (fun i : Fin 5 => e i - ((i : ℕ) : ℤ) = -4),
      (-1 : ℤ) ^ (i : ℕ) • (lam i
        * ∏ j ∈ Finset.range (i : ℕ), ((N + e i - (j : ℤ) : ℤ) : K))) ≠ 0 := by
    have hval : (∑ i ∈ Finset.univ.filter (fun i : Fin 5 => e i - ((i : ℕ) : ℤ) = -4),
        (-1 : ℤ) ^ (i : ℕ) • (lam i
          * ∏ j ∈ Finset.range (i : ℕ), ((N + e i - (j : ℤ) : ℤ) : K)))
        = -(1 / 4 : K) * ((N - 3 : ℤ) : K)
          + (17 / 4 : K) * ((N - 2 : ℤ) : K) * ((N - 3 : ℤ) : K)
          - (5 : K) * ((N - 1 : ℤ) : K) * ((N - 2 : ℤ) : K) * ((N - 3 : ℤ) : K)
          + ((N : ℤ) : K) * ((N - 1 : ℤ) : K) * ((N - 2 : ℤ) : K)
            * ((N - 3 : ℤ) : K) := by
      rw [show (Finset.univ.filter (fun i : Fin 5 => e i - ((i : ℕ) : ℤ) = -4))
        = ({1, 2, 3, 4} : Finset (Fin 5)) from by decide]
      rw [show ({1, 2, 3, 4} : Finset (Fin 5))
          = insert 1 (insert 2 (insert 3 ({4} : Finset (Fin 5)))) from rfl]
      rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
        Finset.sum_insert (by decide), Finset.sum_singleton]
      simp only [show (lam (1 : Fin 5)) = (1 / 4 : K) from rfl,
        show (lam (2 : Fin 5)) = (17 / 4 : K) from rfl,
        show (lam (3 : Fin 5)) = (5 : K) from rfl,
        show (lam (4 : Fin 5)) = (1 : K) from rfl,
        show (e (1 : Fin 5)) = (-3 : ℤ) from rfl,
        show (e (2 : Fin 5)) = (-2 : ℤ) from rfl,
        show (e (3 : Fin 5)) = (-1 : ℤ) from rfl,
        show (e (4 : Fin 5)) = (0 : ℤ) from rfl,
        show (((1 : Fin 5) : ℕ)) = 1 from rfl, show (((2 : Fin 5) : ℕ)) = 2 from rfl,
        show (((3 : Fin 5) : ℕ)) = 3 from rfl, show (((4 : Fin 5) : ℕ)) = 4 from rfl,
        Finset.prod_range_succ, Finset.prod_range_zero]
      push_cast
      ring
    have hfac : -(1 / 4 : K) * ((N - 3 : ℤ) : K)
          + (17 / 4 : K) * ((N - 2 : ℤ) : K) * ((N - 3 : ℤ) : K)
          - (5 : K) * ((N - 1 : ℤ) : K) * ((N - 2 : ℤ) : K) * ((N - 3 : ℤ) : K)
          + ((N : ℤ) : K) * ((N - 1 : ℤ) : K) * ((N - 2 : ℤ) : K) * ((N - 3 : ℤ) : K)
        = (1 / 4 : K) * ((N - 3 : ℤ) : K) * ((N - 3 : ℤ) : K)
          * (((2 * N - 5 : ℤ)) : K) * (((2 * N - 5 : ℤ)) : K) := by
      push_cast
      ring
    rw [hval, hfac]
    refine mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero ?_ ?_) ?_) ?_) ?_
    · norm_num
    · rw [Int.cast_ne_zero]; omega
    · rw [Int.cast_ne_zero]; omega
    · rw [Int.cast_ne_zero]; omega
    · rw [Int.cast_ne_zero]; omega
  have hmain := ordAtT_adjoint_eq_of_indicial_le D hd (0 : K) bb hb N rfl r hr hb' g e lam (-4)
    he hm hlam hP
  rw [hsys, ordAtT_neg] at hmain
  have hthis : ((-4 : ℤ) : WithTop ℤ) ≤ ((N + (-4) : ℤ) : WithTop ℤ) := by
    rw [← hmain]; exact hR
  rw [WithTop.coe_le_coe] at hthis
  omega

/-! ## The local data at a general point, and the bound at `α = 4` -/

/-- The order of `c/((X-α)^k·d)` at `α` is at least `-k` (when `d(α) ≠ 0`). -/
theorem ordAtT_div_pow_sub_ge {K : Type*} [Field K] (α : K) {d : Polynomial K}
    (hdα : d.eval α ≠ 0) (c : Polynomial K) (k : ℕ) :
    ((-(k : ℤ) : ℤ) : WithTop ℤ) ≤ ordAtT α
      (algebraMap (Polynomial K) (RatFunc K) c
        / algebraMap (Polynomial K) (RatFunc K) ((Polynomial.X - Polynomial.C α) ^ k * d)) := by
  classical
  have hd : d ≠ 0 := fun h => hdα (by rw [h, Polynomial.eval_zero])
  have hX : (Polynomial.X - Polynomial.C α : Polynomial K) ≠ 0 := Polynomial.X_sub_C_ne_zero α
  have hden : ((Polynomial.X - Polynomial.C α) ^ k * d : Polynomial K) ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ hX) hd
  rcases eq_or_ne c 0 with hc | hc
  · rw [hc, map_zero, zero_div]
    simp [ordAtT]
  · have hrmden : Polynomial.rootMultiplicity α
        ((Polynomial.X - Polynomial.C α) ^ k * d) = k := by
      have := Polynomial.rootMultiplicity_mul_X_sub_C_pow (p := d) (a := α) (n := k) hd
      rw [mul_comm, this, Polynomial.rootMultiplicity_eq_zero (p := d) (x := α) hdα, zero_add]
    rw [ordAtT_def α (div_ne_zero (RatFunc.algebraMap_ne_zero hc)
        (RatFunc.algebraMap_ne_zero hden)),
      ordAt_div α (RatFunc.algebraMap_ne_zero hc) (RatFunc.algebraMap_ne_zero hden),
      ordAt_algebraMap, ordAt_algebraMap, hrmden, WithTop.coe_le_coe]
    have : (0 : ℤ) ≤ (Polynomial.rootMultiplicity α c : ℤ) := Int.natCast_nonneg _
    omega

/-- **The local data at a general point `α`.**  For a polynomial `c` whose `k`-th jet matches
`lam·d` at `α`, the function `c/((X-α)^k·d) - lam/(X-α)^k` is regular at `α`. -/
theorem residual_at_alpha {K : Type*} [Field K] (α : K) {d : Polynomial K} (hdα : d.eval α ≠ 0)
    {c : Polynomial K} {lam : K} {k : ℕ} (hval : (c - Polynomial.C lam * d).eval α = 0) :
    ((((1 : ℤ) - (k : ℤ)) : ℤ) : WithTop ℤ) ≤ ordAtT α
      (algebraMap (Polynomial K) (RatFunc K) c
          / algebraMap (Polynomial K) (RatFunc K) ((Polynomial.X - Polynomial.C α) ^ k * d)
        - algebraMap (Polynomial K) (RatFunc K) (Polynomial.C lam)
          * linFactor (K := K) α ^ (-(k : ℤ))) := by
  classical
  have hd : d ≠ 0 := fun h => hdα (by rw [h, Polynomial.eval_zero])
  have hX : (Polynomial.X - Polynomial.C α : Polynomial K) ≠ 0 := Polynomial.X_sub_C_ne_zero α
  have hden : ((Polynomial.X - Polynomial.C α) ^ k * d : Polynomial K) ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ hX) hd
  have hlf : linFactor (K := K) α = algebraMap (Polynomial K) (RatFunc K) (Polynomial.X - Polynomial.C α) :=
    rfl
  have hB' : algebraMap (Polynomial K) (RatFunc K) ((Polynomial.X - Polynomial.C α) ^ k * d : Polynomial K)
      = algebraMap (Polynomial K) (RatFunc K) ((Polynomial.X - Polynomial.C α) ^ k)
        * algebraMap (Polynomial K) (RatFunc K) d := map_mul _ _ _
  have h3 : ((algebraMap (Polynomial K) (RatFunc K) (Polynomial.X - Polynomial.C α) : RatFunc K)) ^ (-(k : ℤ))
      = (algebraMap (Polynomial K) (RatFunc K)
          ((Polynomial.X - Polynomial.C α) ^ k : Polynomial K) : RatFunc K)⁻¹ := by
    rw [zpow_neg, map_pow]
    rfl
  have hkey : algebraMap (Polynomial K) (RatFunc K) c
        / algebraMap (Polynomial K) (RatFunc K) ((Polynomial.X - Polynomial.C α) ^ k * d)
      - algebraMap (Polynomial K) (RatFunc K) (Polynomial.C lam)
        * linFactor (K := K) α ^ (-(k : ℤ))
      = algebraMap (Polynomial K) (RatFunc K) (c - Polynomial.C lam * d)
        / algebraMap (Polynomial K) (RatFunc K) ((Polynomial.X - Polynomial.C α) ^ k * d) := by
    have hd' : algebraMap (Polynomial K) (RatFunc K) d ≠ 0 := RatFunc.algebraMap_ne_zero hd
    have hA : algebraMap (Polynomial K) (RatFunc K)
        ((Polynomial.X - Polynomial.C α) ^ k : Polynomial K) ≠ 0 :=
      RatFunc.algebraMap_ne_zero (pow_ne_zero _ hX)
    rw [hlf, h3, hB', ← div_eq_mul_inv]
    field_simp
    rw [← map_mul, ← map_sub]
    congr 1
    ring
  rw [hkey]
  rcases eq_or_ne (c - Polynomial.C lam * d) 0 with h0 | h0
  · rw [h0, map_zero, zero_div]
    simp [ordAtT]
  · have hrmden : Polynomial.rootMultiplicity α
        ((Polynomial.X - Polynomial.C α) ^ k * d) = k := by
      have := Polynomial.rootMultiplicity_mul_X_sub_C_pow (p := d) (a := α) (n := k) hd
      rw [mul_comm, this, Polynomial.rootMultiplicity_eq_zero (p := d) (x := α) hdα, zero_add]
    have hrmnum : 1 ≤ Polynomial.rootMultiplicity α (c - Polynomial.C lam * d) :=
      (Polynomial.rootMultiplicity_pos h0).mpr hval
    have hdiv : algebraMap (Polynomial K) (RatFunc K) (c - Polynomial.C lam * d)
        / algebraMap (Polynomial K) (RatFunc K) ((Polynomial.X - Polynomial.C α) ^ k * d) ≠ 0 :=
      div_ne_zero (RatFunc.algebraMap_ne_zero h0) (RatFunc.algebraMap_ne_zero hden)
    rw [ordAtT_def α hdiv]
    rw [ordAt_div α (RatFunc.algebraMap_ne_zero h0) (RatFunc.algebraMap_ne_zero hden)]
    rw [ordAt_algebraMap, ordAt_algebraMap, hrmden]
    rw [WithTop.coe_le_coe]
    omega

/-- **The local bound `N_4 ≥ 2` at `y = 4`.**

With `c₄ = (X−4)²·dt`, `g₀ = c₀/c₄`, `g₁ = c₁/c₄`, `g₂ = c₂/c₄`, `g₃ = X²Λnum/((X−4)·dt)`, `g₄ = 1`,
and the local data `dt(4) ≠ 0`, `4c₂(4) = 3dt(4)`, `16Λnum(4) = 3dt(4)` (equivalently the leading
coefficients `λ = (·,·,3/4,3,1)` of the `γᵢ` at `4`), the order at `4` of a solution `b` of the
eliminated equation is at least `2`, provided `R` is regular at `4`.  The indicial polynomial at `4`
is `¼(2−N)(3−N)(5−2N)(3−2N)`, with integer roots `2,3`. -/
theorem local_bound_at_four {K : Type*} [Field K] [CharZero K]
    (D : Derivation K (RatFunc K) (RatFunc K))
    (hd : ∀ p : Polynomial K, D (algebraMap (Polynomial K) (RatFunc K) p)
      = algebraMap (Polynomial K) (RatFunc K) p.derivative)
    {dt c0 c1 c2 Λnum : Polynomial K}
    (hdt : dt.eval 4 ≠ 0)
    (hc2 : 4 * c2.eval 4 = 3 * dt.eval 4)
    (hc3 : 16 * Λnum.eval 4 = 3 * dt.eval 4)
    (bb R : RatFunc K) (hb : bb ≠ 0) (hR : (0 : WithTop ℤ) ≤ ordAtT (4 : K) R)
    (g : Fin 5 → RatFunc K)
    (hg0 : g 0 = algebraMap (Polynomial K) (RatFunc K) c0
      / algebraMap (Polynomial K) (RatFunc K) ((Polynomial.X - Polynomial.C 4) ^ 2 * dt))
    (hg1 : g 1 = algebraMap (Polynomial K) (RatFunc K) c1
      / algebraMap (Polynomial K) (RatFunc K) ((Polynomial.X - Polynomial.C 4) ^ 2 * dt))
    (hg2 : g 2 = algebraMap (Polynomial K) (RatFunc K) c2
      / algebraMap (Polynomial K) (RatFunc K) ((Polynomial.X - Polynomial.C 4) ^ 2 * dt))
    (hg3 : g 3 = algebraMap (Polynomial K) (RatFunc K) (Polynomial.X ^ 2 * Λnum)
      / algebraMap (Polynomial K) (RatFunc K) ((Polynomial.X - Polynomial.C 4) * dt))
    (hg4 : g 4 = 1)
    (hsys : (∑ i : Fin 5, (-1 : ℤ) ^ (i : ℕ) • ((fun x : RatFunc K => D x)^[i]) (g i * bb))
      = -R) :
    (2 : ℤ) ≤ ordAt (4 : K) bb := by
  classical
  by_contra hcon
  have hcon' : ordAt (4 : K) bb < 2 := not_le.mp hcon
  set N : ℤ := ordAt (4 : K) bb
  have hNle : N ≤ 1 := by omega
  obtain ⟨r, hr, hb'⟩ := exists_leading_term (4 : K) hb
  let e : Fin 5 → ℤ := ![-2, -2, -2, -1, 0]
  let lam : Fin 5 → K := ![0, 0, 3 / 4, 3, 1]
  have hfin : ∀ i : Fin 5, e i - ((i : ℕ) : ℤ) = -4 ↔ (i = 2 ∨ i = 3 ∨ i = 4) := by decide
  have hlow : ∀ i : Fin 5, (i = 0 ∨ i = 1) → e i = (-2 : ℤ) := by decide
  have he : ∀ i : Fin 5, e i - ((i : ℕ) : ℤ) ≠ -4 →
      ((e i : ℤ) : WithTop ℤ) ≤ ordAtT (4 : K) (g i) := by
    intro i hi
    have hne2 : i ≠ 2 := fun h => hi ((hfin i).mpr (Or.inl h))
    have hne3 : i ≠ 3 := fun h => hi ((hfin i).mpr (Or.inr (Or.inl h)))
    have hne4 : i ≠ 4 := fun h => hi ((hfin i).mpr (Or.inr (Or.inr h)))
    have h01 : i = 0 ∨ i = 1 := by
      have := i.isLt
      omega
    rcases h01 with h | h
    · subst h
      rw [hg0, hlow 0 (Or.inl rfl)]
      exact ordAtT_div_pow_sub_ge (4 : K) hdt c0 2
    · subst h
      rw [hg1, hlow 1 (Or.inr rfl)]
      exact ordAtT_div_pow_sub_ge (4 : K) hdt c1 2
  have hm : ∀ i : Fin 5, -4 ≤ e i - ((i : ℕ) : ℤ) := by decide
  have hlam : ∀ i : Fin 5, e i - ((i : ℕ) : ℤ) = -4 →
      (((e i + 1 : ℤ)) : WithTop ℤ) ≤ ordAtT (4 : K) (g i
        - algebraMap (Polynomial K) (RatFunc K) (Polynomial.C (lam i))
          * linFactor (K := K) 4 ^ (e i)) := by
    intro i hi
    rcases (hfin i).mp hi with h | h | h
    · subst h
      rw [hg2, show e 2 = (-2 : ℤ) from rfl, show lam 2 = (3 / 4 : K) from rfl]
      have h4 : (4 : K) ≠ 0 := by norm_num
      exact residual_at_alpha (4 : K) hdt (k := 2) (lam := (3 / 4 : K)) (by
        rw [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_C]
        have key : (3 / 4 : K) * dt.eval 4 = c2.eval 4 := by
          calc (3 / 4 : K) * dt.eval 4 = (3 * (4 : K)⁻¹) * dt.eval 4 := by rw [div_eq_mul_inv]
            _ = (4 : K)⁻¹ * (3 * dt.eval 4) := by ring
            _ = (4 : K)⁻¹ * (4 * c2.eval 4) := by rw [← hc2]
            _ = c2.eval 4 := by rw [← mul_assoc, inv_mul_cancel₀ h4, one_mul]
        rw [key, sub_self])
    · subst h
      rw [hg3, show e 3 = (-1 : ℤ) from rfl, show lam 3 = (3 : K) from rfl]
      have hk := residual_at_alpha (4 : K) hdt (k := 1) (lam := (3 : K))
        (c := Polynomial.X ^ 2 * Λnum) (by
          rw [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_mul, Polynomial.eval_pow,
            Polynomial.eval_X, Polynomial.eval_C]
          rw [show ((4 : K)) ^ 2 = 16 from by norm_num]
          rw [← hc3]
          ring)
      simpa [pow_one] using hk
    · subst h
      have hc : (((e 4 + 1 : ℤ)) : WithTop ℤ) = (1 : WithTop ℤ) := by
        rw [show e 4 = (0 : ℤ) from rfl]; norm_num
      rw [hc, hg4, show lam 4 = (1 : K) from rfl, show e 4 = (0 : ℤ) from rfl,
        zpow_zero, mul_one]
      simp only [map_one, sub_self]
      simp [ordAtT]
  have hP : (∑ i ∈ Finset.univ.filter (fun i : Fin 5 => e i - ((i : ℕ) : ℤ) = -4),
      (-1 : ℤ) ^ (i : ℕ) • (lam i
        * ∏ j ∈ Finset.range (i : ℕ), ((N + e i - (j : ℤ) : ℤ) : K))) ≠ 0 := by
    have hval : (∑ i ∈ Finset.univ.filter (fun i : Fin 5 => e i - ((i : ℕ) : ℤ) = -4),
        (-1 : ℤ) ^ (i : ℕ) • (lam i
          * ∏ j ∈ Finset.range (i : ℕ), ((N + e i - (j : ℤ) : ℤ) : K)))
        = (3 / 4 : K) * ((N - 2 : ℤ) : K) * ((N - 3 : ℤ) : K)
          - (3 : K) * ((N - 1 : ℤ) : K) * ((N - 2 : ℤ) : K) * ((N - 3 : ℤ) : K)
          + ((N : ℤ) : K) * ((N - 1 : ℤ) : K) * ((N - 2 : ℤ) : K) * ((N - 3 : ℤ) : K) := by
      rw [show (Finset.univ.filter (fun i : Fin 5 => e i - ((i : ℕ) : ℤ) = -4))
        = ({2, 3, 4} : Finset (Fin 5)) from by decide]
      rw [show ({2, 3, 4} : Finset (Fin 5))
          = insert 2 (insert 3 ({4} : Finset (Fin 5))) from rfl]
      rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
      simp only [show (lam (2 : Fin 5)) = (3 / 4 : K) from rfl,
        show (lam (3 : Fin 5)) = (3 : K) from rfl,
        show (lam (4 : Fin 5)) = (1 : K) from rfl,
        show (e (2 : Fin 5)) = (-2 : ℤ) from rfl,
        show (e (3 : Fin 5)) = (-1 : ℤ) from rfl,
        show (e (4 : Fin 5)) = (0 : ℤ) from rfl,
        show (((2 : Fin 5) : ℕ)) = 2 from rfl, show (((3 : Fin 5) : ℕ)) = 3 from rfl,
        show (((4 : Fin 5) : ℕ)) = 4 from rfl,
        Finset.prod_range_succ, Finset.prod_range_zero]
      push_cast
      ring
    have hfac : (3 / 4 : K) * ((N - 2 : ℤ) : K) * ((N - 3 : ℤ) : K)
          - (3 : K) * ((N - 1 : ℤ) : K) * ((N - 2 : ℤ) : K) * ((N - 3 : ℤ) : K)
          + ((N : ℤ) : K) * ((N - 1 : ℤ) : K) * ((N - 2 : ℤ) : K) * ((N - 3 : ℤ) : K)
        = (1 / 4 : K) * ((2 - N : ℤ) : K) * ((3 - N : ℤ) : K)
          * (((5 - 2 * N : ℤ)) : K) * (((3 - 2 * N : ℤ)) : K) := by
      push_cast
      ring
    rw [hval, hfac]
    refine mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero ?_ ?_) ?_) ?_) ?_
    · norm_num
    · rw [Int.cast_ne_zero]; omega
    · rw [Int.cast_ne_zero]; omega
    · rw [Int.cast_ne_zero]; omega
    · rw [Int.cast_ne_zero]; omega
  have hmain := ordAtT_adjoint_eq_of_indicial_le D hd (4 : K) bb hb N rfl r hr hb' g e lam (-4)
    he hm hlam hP
  rw [hsys, ordAtT_neg] at hmain
  have hthis : (0 : WithTop ℤ) ≤ ((N + (-4) : ℤ) : WithTop ℤ) := by
    rw [← hmain]; exact hR
  rw [← WithTop.coe_zero, WithTop.coe_le_coe] at hthis
  omega

end

end Submission.CDT.CsideLocal

