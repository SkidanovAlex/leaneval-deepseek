/-
# `Work.FTS.StrongPersist.L3Rhs.Pricing` — the pricing factor and the shape lemmas

The block estimates of `L3Rhs/Defs.lean` come with different `α`-powers, different powers of
`(1+|Cs|)`, `(1+|Ce|)`, `(1+M)` and `(1+|f|_{ℋ⁶})`.  This module fixes the single factor

  `pricedR α Cpow M X Ce Cs = (1+|Ce|+|Cs|)⁴ α^{-Cpow} (1+M)⁴ (1+X)²`

in which the final estimate is stated, proves that it is `≥ 1`, and records the elementary
dominations of each block shape by it (all four factors are `≥ 1`, so every partial product of
them with dominated exponents is `≤ pricedR`).

It also contains the *binary additivity of `HkNorm`* used to sum the nine blocks:
`|u+v|_{ℋ³} ≤ 2 (B_u + B_v)` whenever `|u|_{ℋ³} ≤ B_u`, `|v|_{ℋ³} ≤ B_v` and `u`, `v` are `C³`
on the open quadrant (the finite-order companion of `HkNorm_add_le`, which asks for `C^∞`).
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.StrongPersist.Defs
import Submission.Work.FTS.StrongPersist.L3Rhs.Assembly

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.L3Rhs

open Work.FTS.Galerkin (Fn)
open Work.Spaces (HkMem HkSq HkNorm)

set_option autoImplicit false
set_option linter.unusedVariables false

/-- The factor `R = (1+|Ce|+|Cs|)⁴ α^{-Cpow} (1+M)⁴ (1+|f|_{ℋ⁶})²` in which every block
estimate is expressed. -/
def pricedR (α Cpow M X Ce Cs : ℝ) : ℝ :=
  (1 + |Ce| + |Cs|) ^ 4 * α ^ (-Cpow) * (1 + M) ^ 4 * (1 + X) ^ 2

theorem pricedR_nonneg {α Cpow M X Ce Cs : ℝ} (hα : 0 < α) (hX : 0 ≤ X) :
    0 ≤ pricedR α Cpow M X Ce Cs := by
  rw [pricedR]
  exact mul_nonneg (mul_nonneg (mul_nonneg (by positivity) (Real.rpow_nonneg hα.le _))
    (by positivity)) (by positivity)

/-- `α^{-Cpow} ≥ 1` for `0 < α ≤ 1` and `Cpow ≥ 0`. -/
theorem one_le_rpow_neg {α Cpow : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) (hCpow : 0 ≤ Cpow) :
    (1 : ℝ) ≤ α ^ (-Cpow) := by
  have h1α : (1 : ℝ) ≤ α⁻¹ := (one_le_inv₀ hα).mpr hα1
  calc (1 : ℝ) = (α⁻¹) ^ (0 : ℝ) := (Real.rpow_zero _).symm
    _ ≤ (α⁻¹) ^ Cpow := Real.rpow_le_rpow_of_exponent_le h1α hCpow
    _ = α ^ (-Cpow) := by rw [Real.inv_rpow hα.le Cpow, Real.rpow_neg hα.le Cpow]

/-- `α^{-Cp} ≤ α^{-Cpow}` for `0 < α ≤ 1` and `Cp ≤ Cpow`. -/
theorem rpow_neg_le_neg {α Cp Cpow : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) (hle : Cp ≤ Cpow) :
    α ^ (-Cp) ≤ α ^ (-Cpow) := by
  have h1α : (1 : ℝ) ≤ α⁻¹ := (one_le_inv₀ hα).mpr hα1
  calc α ^ (-Cp) = (α⁻¹) ^ Cp := by rw [Real.inv_rpow hα.le Cp, Real.rpow_neg hα.le Cp]
    _ ≤ (α⁻¹) ^ Cpow := Real.rpow_le_rpow_of_exponent_le h1α hle
    _ = α ^ (-Cpow) := by rw [Real.inv_rpow hα.le Cpow, Real.rpow_neg hα.le Cpow]

theorem one_le_pricedR {α Cpow M X Ce Cs : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) (hCpow : 0 ≤ Cpow)
    (hM : 0 ≤ M) (hX : 0 ≤ X) : 1 ≤ pricedR α Cpow M X Ce Cs := by
  have h1 : (1 : ℝ) ≤ (1 + |Ce| + |Cs|) ^ 4 :=
    one_le_pow₀ (by have := abs_nonneg Ce; have := abs_nonneg Cs; linarith)
  have h2 : (1 : ℝ) ≤ α ^ (-Cpow) := one_le_rpow_neg hα hα1 hCpow
  have h3 : (1 : ℝ) ≤ (1 + M) ^ 4 := one_le_pow₀ (by linarith)
  have h4 : (1 : ℝ) ≤ (1 + X) ^ 2 := one_le_pow₀ (by linarith)
  have h12 : (1 : ℝ) ≤ (1 + |Ce| + |Cs|) ^ 4 * α ^ (-Cpow) :=
    le_trans h1 (le_mul_of_one_le_right (by positivity) h2)
  have h123 : (1 : ℝ) ≤ (1 + |Ce| + |Cs|) ^ 4 * α ^ (-Cpow) * (1 + M) ^ 4 :=
    le_trans h12 (le_mul_of_one_le_right (by positivity) h3)
  have h1234 : (1 : ℝ) ≤ (1 + |Ce| + |Cs|) ^ 4 * α ^ (-Cpow) * (1 + M) ^ 4 * (1 + X) ^ 2 :=
    le_trans h123 (le_mul_of_one_le_right (by positivity) h4)
  simpa only [pricedR] using h1234

/-- **Factor-wise domination of any partial product by the pricing factor.** -/
theorem pricedR_of_factors {α Cpow M X Ce Cs A B C D : ℝ} (hα : 0 < α)
    (hA : A ≤ (1 + |Ce| + |Cs|) ^ 4) (hB : B ≤ α ^ (-Cpow))
    (hC : C ≤ (1 + M) ^ 4) (hD : D ≤ (1 + X) ^ 2)
    (hA0 : 0 ≤ A) (hB0 : 0 ≤ B) (hC0 : 0 ≤ C) (hD0 : 0 ≤ D) :
    A * B * C * D ≤ pricedR α Cpow M X Ce Cs := by
  rw [pricedR]
  have ha4 : (0 : ℝ) ≤ (1 + |Ce| + |Cs|) ^ 4 := by positivity
  have hrp : (0 : ℝ) ≤ α ^ (-Cpow) := Real.rpow_nonneg hα.le _
  have hm4 : (0 : ℝ) ≤ (1 + M) ^ 4 := by positivity
  have hAB : A * B ≤ (1 + |Ce| + |Cs|) ^ 4 * α ^ (-Cpow) := mul_le_mul hA hB hB0 ha4
  have hABC : A * B * C ≤ (1 + |Ce| + |Cs|) ^ 4 * α ^ (-Cpow) * (1 + M) ^ 4 :=
    mul_le_mul hAB hC hC0 (mul_nonneg ha4 hrp)
  exact mul_le_mul hABC hD hD0 (mul_nonneg (mul_nonneg ha4 hrp) hm4)

/-! ## The block shapes -/

theorem shape_alpha2 {α Cpow M X Ce Cs : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) (hCpow : 0 ≤ Cpow)
    (hM : 0 ≤ M) (hX : 0 ≤ X) : α ^ 2 ≤ pricedR α Cpow M X Ce Cs := by
  have h1 : (1 : ℝ) ≤ (1 + |Ce| + |Cs|) ^ 4 :=
    one_le_pow₀ (by have := abs_nonneg Ce; have := abs_nonneg Cs; linarith)
  have h2 : (1 : ℝ) ≤ α ^ (-Cpow) := one_le_rpow_neg hα hα1 hCpow
  have h3 : (1 : ℝ) ≤ (1 + M) ^ 4 := one_le_pow₀ (by linarith)
  have h4 : (1 : ℝ) ≤ (1 + X) ^ 2 := one_le_pow₀ (by linarith)
  have hα2 : α ^ 2 ≤ 1 := by nlinarith [hα.le, hα1]
  have := pricedR_of_factors hα (A := 1) (B := α ^ 2) (C := 1) (D := 1)
    h1 (le_trans hα2 h2) h3 h4 (by norm_num) (by positivity) (by norm_num) (by norm_num)
  simpa using this

theorem shape_M {α Cpow M X Ce Cs : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) (hCpow : 0 ≤ Cpow)
    (hM : 0 ≤ M) (hX : 0 ≤ X) : 1 + M ≤ pricedR α Cpow M X Ce Cs := by
  have h1 : (1 : ℝ) ≤ (1 + |Ce| + |Cs|) ^ 4 :=
    one_le_pow₀ (by have := abs_nonneg Ce; have := abs_nonneg Cs; linarith)
  have h2 : (1 : ℝ) ≤ α ^ (-Cpow) := one_le_rpow_neg hα hα1 hCpow
  have h4 : (1 : ℝ) ≤ (1 + X) ^ 2 := one_le_pow₀ (by linarith)
  have hM4 : 1 + M ≤ (1 + M) ^ 4 := by
    have hy1 : (1 : ℝ) ≤ 1 + M := by linarith
    simpa using pow_le_pow_right₀ hy1 (by norm_num : (1 : ℕ) ≤ 4)
  have := pricedR_of_factors hα (A := 1) (B := 1) (C := 1 + M) (D := 1)
    h1 h2 hM4 h4 (by norm_num) (by norm_num) (by linarith) (by norm_num)
  simpa using this

theorem shape_MX {α Cp Cpow M X Ce Cs : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) (hCp : 0 ≤ Cp)
    (hCple : Cp ≤ Cpow) (hCpow : 0 ≤ Cpow) (hM : 0 ≤ M) (hX : 0 ≤ X) :
    α ^ (-Cp) * (1 + M) ^ 4 * (1 + X) ^ 2 ≤ pricedR α Cpow M X Ce Cs := by
  have h1 : (1 : ℝ) ≤ (1 + |Ce| + |Cs|) ^ 4 :=
    one_le_pow₀ (by have := abs_nonneg Ce; have := abs_nonneg Cs; linarith)
  have h2 : α ^ (-Cp) ≤ α ^ (-Cpow) := rpow_neg_le_neg hα hα1 hCple
  have h3 : (0 : ℝ) ≤ α ^ (-Cp) := Real.rpow_nonneg hα.le _
  have := pricedR_of_factors hα (A := 1) (B := α ^ (-Cp))
    (C := (1 + M) ^ 4) (D := (1 + X) ^ 2)
    h1 h2 le_rfl le_rfl (by norm_num) h3 (by positivity) (by positivity)
  simpa using this

theorem shape_s {α Cp Cpow M X Ce Cs : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) (hCp : 0 ≤ Cp)
    (hCple : Cp ≤ Cpow) (hCpow : 0 ≤ Cpow) (hM : 0 ≤ M) (hX : 0 ≤ X) :
    (1 + |Cs|) ^ 4 * α ^ (-Cp) ≤ pricedR α Cpow M X Ce Cs := by
  have h1 : (1 + |Cs|) ^ 4 ≤ (1 + |Ce| + |Cs|) ^ 4 :=
    pow_le_pow_left₀ (by positivity) (by have := abs_nonneg Ce; linarith) 4
  have h2 : α ^ (-Cp) ≤ α ^ (-Cpow) := rpow_neg_le_neg hα hα1 hCple
  have h3 : (0 : ℝ) ≤ α ^ (-Cp) := Real.rpow_nonneg hα.le _
  have h4 : (1 : ℝ) ≤ (1 + M) ^ 4 := one_le_pow₀ (by linarith)
  have h5 : (1 : ℝ) ≤ (1 + X) ^ 2 := one_le_pow₀ (by linarith)
  have := pricedR_of_factors hα (A := (1 + |Cs|) ^ 4) (B := α ^ (-Cp)) (C := 1) (D := 1)
    h1 h2 h4 h5 (by positivity) h3 (by norm_num) (by norm_num)
  simpa using this

theorem shape_sM {α Cp Cpow M X Ce Cs : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) (hCp : 0 ≤ Cp)
    (hCple : Cp ≤ Cpow) (hCpow : 0 ≤ Cpow) (hM : 0 ≤ M) (hX : 0 ≤ X) :
    (1 + |Cs|) ^ 4 * α ^ (-Cp) * (1 + M) ^ 4 ≤ pricedR α Cpow M X Ce Cs := by
  have h1 : (1 + |Cs|) ^ 4 ≤ (1 + |Ce| + |Cs|) ^ 4 :=
    pow_le_pow_left₀ (by positivity) (by have := abs_nonneg Ce; linarith) 4
  have h2 : α ^ (-Cp) ≤ α ^ (-Cpow) := rpow_neg_le_neg hα hα1 hCple
  have h3 : (0 : ℝ) ≤ α ^ (-Cp) := Real.rpow_nonneg hα.le _
  have h5 : (1 : ℝ) ≤ (1 + X) ^ 2 := one_le_pow₀ (by linarith)
  have := pricedR_of_factors hα (A := (1 + |Cs|) ^ 4) (B := α ^ (-Cp))
    (C := (1 + M) ^ 4) (D := 1)
    h1 h2 le_rfl h5 (by positivity) h3 (by positivity) (by norm_num)
  simpa using this

theorem shape_e {α Cp Cpow M X Ce Cs : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) (hCp : 0 ≤ Cp)
    (hCple : Cp ≤ Cpow) (hCpow : 0 ≤ Cpow) (hM : 0 ≤ M) (hX : 0 ≤ X) :
    (1 + |Ce|) ^ 4 * α ^ (-Cp) * (1 + M) ^ 4 * (1 + X) ^ 2 ≤ pricedR α Cpow M X Ce Cs := by
  have h1 : (1 + |Ce|) ^ 4 ≤ (1 + |Ce| + |Cs|) ^ 4 :=
    pow_le_pow_left₀ (by positivity) (by have := abs_nonneg Cs; linarith) 4
  have h2 : α ^ (-Cp) ≤ α ^ (-Cpow) := rpow_neg_le_neg hα hα1 hCple
  have h3 : (0 : ℝ) ≤ α ^ (-Cp) := Real.rpow_nonneg hα.le _
  have := pricedR_of_factors hα (A := (1 + |Ce|) ^ 4) (B := α ^ (-Cp))
    (C := (1 + M) ^ 4) (D := (1 + X) ^ 2)
    h1 h2 le_rfl le_rfl (by positivity) h3 (by positivity) (by positivity)
  simpa using this

/-! ## The shapes with a constant factor -/

theorem mul_shape_alpha2 {α Cpow M X Ce Cs C : ℝ} (hα : 0 < α) (hα1 : α ≤ 1)
    (hCpow : 0 ≤ Cpow) (hM : 0 ≤ M) (hX : 0 ≤ X) (hC : 0 ≤ C) :
    C * α ^ 2 ≤ C * pricedR α Cpow M X Ce Cs :=
  mul_le_mul_of_nonneg_left (shape_alpha2 hα hα1 hCpow hM hX) hC

theorem mul_shape_M {α Cpow M X Ce Cs C : ℝ} (hα : 0 < α) (hα1 : α ≤ 1)
    (hCpow : 0 ≤ Cpow) (hM : 0 ≤ M) (hX : 0 ≤ X) (hC : 0 ≤ C) :
    C * (1 + M) ≤ C * pricedR α Cpow M X Ce Cs :=
  mul_le_mul_of_nonneg_left (shape_M hα hα1 hCpow hM hX) hC

theorem mul_shape_MX {α Cp Cpow M X Ce Cs C : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) (hCp : 0 ≤ Cp)
    (hCple : Cp ≤ Cpow) (hCpow : 0 ≤ Cpow) (hM : 0 ≤ M) (hX : 0 ≤ X) (hC : 0 ≤ C) :
    C * α ^ (-Cp) * (1 + M) ^ 4 * (1 + X) ^ 2 ≤ C * pricedR α Cpow M X Ce Cs := by
  rw [show C * α ^ (-Cp) * (1 + M) ^ 4 * (1 + X) ^ 2
      = C * (α ^ (-Cp) * (1 + M) ^ 4 * (1 + X) ^ 2) by ring]
  exact mul_le_mul_of_nonneg_left (shape_MX hα hα1 hCp hCple hCpow hM hX) hC

theorem mul_shape_s {α Cp Cpow M X Ce Cs C : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) (hCp : 0 ≤ Cp)
    (hCple : Cp ≤ Cpow) (hCpow : 0 ≤ Cpow) (hM : 0 ≤ M) (hX : 0 ≤ X) (hC : 0 ≤ C) :
    C * (1 + |Cs|) ^ 4 * α ^ (-Cp) ≤ C * pricedR α Cpow M X Ce Cs := by
  rw [show C * (1 + |Cs|) ^ 4 * α ^ (-Cp) = C * ((1 + |Cs|) ^ 4 * α ^ (-Cp)) by ring]
  exact mul_le_mul_of_nonneg_left (shape_s hα hα1 hCp hCple hCpow hM hX) hC

theorem mul_shape_sM {α Cp Cpow M X Ce Cs C : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) (hCp : 0 ≤ Cp)
    (hCple : Cp ≤ Cpow) (hCpow : 0 ≤ Cpow) (hM : 0 ≤ M) (hX : 0 ≤ X) (hC : 0 ≤ C) :
    C * (1 + |Cs|) ^ 4 * α ^ (-Cp) * (1 + M) ^ 4 ≤ C * pricedR α Cpow M X Ce Cs := by
  rw [show C * (1 + |Cs|) ^ 4 * α ^ (-Cp) * (1 + M) ^ 4
      = C * ((1 + |Cs|) ^ 4 * α ^ (-Cp) * (1 + M) ^ 4) by ring]
  exact mul_le_mul_of_nonneg_left (shape_sM hα hα1 hCp hCple hCpow hM hX) hC

theorem mul_shape_e {α Cp Cpow M X Ce Cs C : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) (hCp : 0 ≤ Cp)
    (hCple : Cp ≤ Cpow) (hCpow : 0 ≤ Cpow) (hM : 0 ≤ M) (hX : 0 ≤ X) (hC : 0 ≤ C) :
    C * (1 + |Ce|) ^ 4 * α ^ (-Cp) * (1 + M) ^ 4 * (1 + X) ^ 2
      ≤ C * pricedR α Cpow M X Ce Cs := by
  rw [show C * (1 + |Ce|) ^ 4 * α ^ (-Cp) * (1 + M) ^ 4 * (1 + X) ^ 2
      = C * ((1 + |Ce|) ^ 4 * α ^ (-Cp) * (1 + M) ^ 4 * (1 + X) ^ 2) by ring]
  exact mul_le_mul_of_nonneg_left (shape_e hα hα1 hCp hCple hCpow hM hX) hC

/-! ## Binary additivity of `HkNorm` -/

private theorem sqrt_add_le' {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    Real.sqrt (a + b) ≤ Real.sqrt a + Real.sqrt b := by
  have h : a + b ≤ (Real.sqrt a + Real.sqrt b) ^ 2 := by
    rw [add_sq, Real.sq_sqrt ha, Real.sq_sqrt hb]
    nlinarith [Real.sqrt_nonneg a, Real.sqrt_nonneg b]
  calc Real.sqrt (a + b) ≤ Real.sqrt ((Real.sqrt a + Real.sqrt b) ^ 2) := Real.sqrt_le_sqrt h
    _ = Real.sqrt a + Real.sqrt b := Real.sqrt_sq (by positivity)

theorem HkNorm_add_le2 (α : ℝ) {u v : Fn} {Bu Bv : ℝ}
    (hu : HkMem α 3 u) (hv : HkMem α 3 v)
    (hc : ContDiffOn ℝ 3 (Function.uncurry u) Work.FTS.EllipticEst.Q0)
    (hd : ContDiffOn ℝ 3 (Function.uncurry v) Work.FTS.EllipticEst.Q0)
    (bu : HkNorm α 3 u ≤ Bu) (bv : HkNorm α 3 v ≤ Bv)
    (hBu : 0 ≤ Bu) (hBv : 0 ≤ Bv) :
    HkMem α 3 (fun z θ => u z θ + v z θ) ∧
      HkNorm α 3 (fun z θ => u z θ + v z θ) ≤ 2 * (Bu + Bv) := by
  obtain ⟨hm, hsq⟩ := HkMem_HkSq_add2 α hc hd hu hv
  refine ⟨hm, ?_⟩
  have hsqrt : HkNorm α 3 (fun z θ => u z θ + v z θ)
      ≤ Real.sqrt 2 * (HkNorm α 3 u + HkNorm α 3 v) := by
    rw [Work.Spaces.HkNorm, Work.Spaces.HkNorm, Work.Spaces.HkNorm]
    calc Real.sqrt (HkSq α 3 (fun z θ => u z θ + v z θ))
        ≤ Real.sqrt (2 * HkSq α 3 u + 2 * HkSq α 3 v) := Real.sqrt_le_sqrt hsq
      _ = Real.sqrt 2 * Real.sqrt (HkSq α 3 u + HkSq α 3 v) := by
          rw [show (2 : ℝ) * HkSq α 3 u + 2 * HkSq α 3 v
              = 2 * (HkSq α 3 u + HkSq α 3 v) by ring, Real.sqrt_mul (by norm_num)]
      _ ≤ Real.sqrt 2 * (Real.sqrt (HkSq α 3 u) + Real.sqrt (HkSq α 3 v)) :=
          mul_le_mul_of_nonneg_left
            (sqrt_add_le' (Work.Spaces.HkSq_nonneg α 3 u) (Work.Spaces.HkSq_nonneg α 3 v))
            (Real.sqrt_nonneg 2)
  have h1 : Real.sqrt 2 * (HkNorm α 3 u + HkNorm α 3 v) ≤ 2 * (Bu + Bv) := by
    have h2 : Real.sqrt 2 ≤ 2 := by
      have := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
      nlinarith [Real.sqrt_nonneg 2, this]
    have h3 : (0 : ℝ) ≤ HkNorm α 3 u := Real.sqrt_nonneg _
    have h4 : (0 : ℝ) ≤ HkNorm α 3 v := Real.sqrt_nonneg _
    nlinarith [bu, bv]
  exact le_trans hsqrt h1

end Work.FTS.StrongPersist.L3Rhs
