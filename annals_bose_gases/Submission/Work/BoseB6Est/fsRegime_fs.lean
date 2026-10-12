import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Submission.Work.BoseB6Est.Regime
import Submission.Work.BoseB6Est.fsI2_le_bound
import Submission.Work.BoseB6Est.fsRegimeArith.latticeMesh_ceil
import Submission.Work.BoseB6Est.fsRegimeArith.lhyEps_fs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Node B6-est — FS's own parameter regime is inhabited

This file exhibits FS's *own* parameter values
(`a = X^{323/3}`, `K_ℓ = X^{-3/2}`, `s = X`, `d = X^6`, `ε_T = X^{23/4}`,
`μ = ρ_z = 1`, `R = 0`, with `X = (μa³)^{1/323} ∈ (0,1/10]`) as a witness for the
regime `FsZeroRegime` of `Submission/Work/BoseB6Est/Regime.lean`, i.e. it removes
the last "parameters-are-admissible" caveat: `FsZeroRegime` holds with the data
the paper uses.

The remaining freedom in the data is used as follows:

* `T = 10⁴X^{-1/4}` is the kernel's momentum cutoff.  It must be large enough
  that FS's error dominates the tail `4π(8π)³/(2T)` of the model bracket, and
  (with the `X`-dependence kept) small enough that the logarithmic terms
  `(c₁+ε_Tc₂)log T` stay below the error; `10⁴X^{-1/4}` satisfies both with room
  to spare.
* `n+1 = ⌈10⁶X^{-1/4}⌉` is the mode count.  The lattice mesh error of the
  zero-point comparison is `O((n+1)^{-1}log(n+1))`, against an error that
  decays only like `X^{1/4}log X^{-1}`; the choice `n+1 ≈ 10⁶X^{-1/4}` makes the
  mesh error smaller by a factor `≈ 10³`.

Everything is explicit: the witness is the pair `(fsrN X, fsrK X hX0)` together
with `fsrA X = X^{323/3}`, `fsrL X = (n+1)/√(ρ_z a)`, `fsrC1 X = ½X^{1/2}`,
`fsrC2 X = ½X^{-11/2}`, `z = chiM = δ = 0`.
-/

noncomputable section

open scoped Real BigOperators

namespace Work.BoseB6Est

/-! ## 1. The witness data -/

/-- the kernel's momentum cutoff `T = 10⁴X^{-1/4}` -/
def fsrT (X : ℝ) : ℝ := 10 ^ 4 * X ^ (-(1 / 4) : ℝ)

/-- the mode count `n = ⌈10⁶X^{-1/4}⌉` -/
def fsrN (X : ℝ) : ℕ := Nat.ceil (10 ^ 6 * X ^ (-(1 / 4) : ℝ))

/-- `β(r) = 8π` for `r ≤ T`, `0` beyond the cutoff -/
def fsrBeta (T r : ℝ) : ℝ := if r ≤ T then 8 * Real.pi else 0

/-- the witness kernel `β = 8π·1_{[0,T]}`: `B = 8π`, `η = 0`, cutoff `T = fsrT X` -/
def fsrK (X : ℝ) (hX : 0 < X) : FsKernel where
  β := fsrBeta (fsrT X)
  B := 8 * Real.pi
  η := 0
  T := fsrT X
  Bnn := by positivity
  ηnn := le_rfl
  Tnn := by rw [fsrT]; positivity
  meas := by
    have h : Measurable fun r : ℝ => if r ≤ fsrT X then (8 : ℝ) * Real.pi else 0 :=
      Measurable.ite measurableSet_Iic measurable_const measurable_const
    convert h using 1
    funext r
    rw [fsrBeta]
  nonneg := by intro r; rw [fsrBeta]; split <;> positivity
  bound := by intro r; rw [fsrBeta]; split <;> first | exact le_rfl | positivity
  close := by intro r _ hrT; rw [fsrBeta]; simp [hrT]
  support := by intro r hr; rw [fsrBeta]; simp only [not_le.mpr hr, ↓reduceIte]

/-- `a = X^{323/3}` (`X = (μa³)^{1/323}` with `μ = 1`) -/
def fsrA (X : ℝ) : ℝ := X ^ (323 / 3 : ℝ)

/-- `ℓ = (n+1)/√(ρ_z a)` (the box side; `hrel` of `FsZeroRegime`) -/
def fsrL (X : ℝ) : ℝ := ((fsrN X : ℝ) + 1) / Real.sqrt (fsrA X)

/-- FS's kinetic cutoff `c₁ = ½(K_ℓs)^{-1}√(μ/ρ_z) = ½X^{1/2}` -/
def fsrC1 (X : ℝ) : ℝ := (1 / 2) * X ^ (1 / 2 : ℝ)

/-- FS's kinetic cutoff `c₂ = ½(K_ℓds)^{-1}√(μ/ρ_z) = ½X^{-11/2}` -/
def fsrC2 (X : ℝ) : ℝ := (1 / 2) * X ^ (-(11 / 2) : ℝ)

/-- FS's error `ε(μ,ρ_z)` at FS's parameters -/
def fsrE (X : ℝ) : ℝ :=
  Work.BoseB6.lhyEps (fsrA X) 0 (X ^ (23 / 4 : ℝ)) (X ^ (-(3 / 2) : ℝ)) X (X ^ 6) 1

lemma fsrK_B (X : ℝ) (hX : 0 < X) : (fsrK X hX).B = 8 * Real.pi := rfl
lemma fsrK_eta (X : ℝ) (hX : 0 < X) : (fsrK X hX).η = 0 := rfl
lemma fsrK_T (X : ℝ) (hX : 0 < X) : (fsrK X hX).T = fsrT X := rfl

/-! ## 2. Elementary numeric facts -/

lemma fsr_log_ten_ge_two : (2 : ℝ) ≤ Real.log 10 := by
  rw [Real.le_log_iff_exp_le (by norm_num)]
  have h : Real.exp 2 < 10 := by
    have h1 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
    nlinarith [Real.exp_one_lt_three, Real.exp_pos 1]
  linarith

lemma fsr_log_inv_ge_two {X : ℝ} (hX0 : 0 < X) (hX1 : X ≤ 1 / 10) :
    2 ≤ Real.log X⁻¹ := by
  have h10 : (10 : ℝ) ≤ X⁻¹ := by
    rw [le_inv_comm₀ (by norm_num) hX0]
    linarith
  exact le_trans fsr_log_ten_ge_two (Real.log_le_log (by norm_num) h10)

lemma fsr_log_inv_nonneg {X : ℝ} (hX0 : 0 < X) (hX1 : X ≤ 1 / 10) :
    0 ≤ Real.log X⁻¹ := le_trans (by norm_num) (fsr_log_inv_ge_two hX0 hX1)

lemma fsr_log_two_le_one : Real.log 2 ≤ 1 := by
  rw [Real.log_le_iff_le_exp (by norm_num)]
  exact le_trans (by norm_num : (2 : ℝ) ≤ 1 + 1) (Real.add_one_le_exp 1)

lemma fsr_log_two_ten_le : Real.log (2 * 10 ^ 4) ≤ 1 + 4 * Real.log 10 := by
  rw [Real.log_mul (by norm_num) (by norm_num), Real.log_pow]
  push_cast
  linarith [fsr_log_two_le_one]

/-- `1 ≤ X^{-y}` for `0 ≤ y` and `X ∈ (0, 1/10]`. -/
lemma fsr_one_le_rpow_neg {X : ℝ} (hX0 : 0 < X) (hX1 : X ≤ 1 / 10) {y : ℝ} (hy : 0 ≤ y) :
    (1 : ℝ) ≤ X ^ (-y) := by
  have hle1 : X ≤ 1 := by linarith
  rw [Real.rpow_neg hX0.le, one_le_inv₀ (Real.rpow_pos_of_pos hX0 y)]
  exact Real.rpow_le_one hX0.le hle1 hy

/-- `X^{y} ≤ X^{z}` for `z ≤ y` and `X ∈ (0,1)`. -/
lemma fsr_rpow_le_of_le {X : ℝ} (hX0 : 0 < X) (hX1 : X ≤ 1 / 10) {y z : ℝ} (hyz : z ≤ y) :
    X ^ y ≤ X ^ z :=
  Real.rpow_le_rpow_of_exponent_ge hX0 (by linarith) hyz

/-! ## 3. The `X`-powers of FS's parameters -/

lemma fsrA_pos {X : ℝ} (hX0 : 0 < X) : 0 < fsrA X := Real.rpow_pos_of_pos hX0 _

lemma fsrA_cube {X : ℝ} (hX0 : 0 < X) : (fsrA X) ^ 3 = X ^ (323 : ℝ) := by
  rw [fsrA, ← Real.rpow_natCast (X ^ (323 / 3 : ℝ)) 3, ← Real.rpow_mul hX0.le]
  norm_num

lemma fsrA3_half {X : ℝ} (hX0 : 0 < X) :
    (1 * (fsrA X) ^ 3) ^ (1 / 2 : ℝ) = X ^ (323 / 2 : ℝ) := by
  rw [one_mul, fsrA_cube hX0, ← Real.rpow_mul hX0.le]
  norm_num

lemma fsrA_sq {X : ℝ} (hX0 : 0 < X) : (fsrA X) ^ 2 = X ^ (646 / 3 : ℝ) := by
  rw [fsrA, ← Real.rpow_natCast (X ^ (323 / 3 : ℝ)) 2, ← Real.rpow_mul hX0.le]
  norm_num

lemma fsrA_sqrt_cube {X : ℝ} (hX0 : 0 < X) :
    (Real.sqrt (fsrA X)) ^ 3 = X ^ (323 / 2 : ℝ) := by
  rw [show (Real.sqrt (fsrA X)) ^ 3 = (Real.sqrt (fsrA X)) ^ 2 * Real.sqrt (fsrA X) by ring,
    Real.sq_sqrt (fsrA_pos hX0).le, Real.sqrt_eq_rpow, fsrA, ← Real.rpow_mul hX0.le,
    ← Real.rpow_add hX0]
  norm_num

/-- `K_ℓs = X^{-1/2}` -/
lemma fsr_Kl_mul_s {X : ℝ} (hX0 : 0 < X) : X ^ (-(3 / 2) : ℝ) * X = X ^ (-(1 / 2) : ℝ) := by
  have h : X ^ (-(3 / 2) : ℝ) * X ^ (1 : ℝ) = X ^ (-(1 / 2) : ℝ) := by
    rw [← Real.rpow_add hX0]; norm_num
  simpa only [Real.rpow_one] using h

/-- `(K_ℓs)^{-1} = X^{1/2}` -/
lemma fsr_Kl_inv {X : ℝ} (hX0 : 0 < X) : (X ^ (-(3 / 2) : ℝ) * X)⁻¹ = X ^ (1 / 2 : ℝ) := by
  rw [fsr_Kl_mul_s hX0, Real.rpow_neg hX0.le, inv_inv]

/-- `K_ℓds = X^{11/2}` -/
lemma fsr_Kl_d_s {X : ℝ} (hX0 : 0 < X) :
    X ^ (-(3 / 2) : ℝ) * X ^ 6 * X = X ^ (11 / 2 : ℝ) := by
  have h : X ^ (-(3 / 2) : ℝ) * X ^ 6 * X ^ (1 : ℝ) = X ^ (11 / 2 : ℝ) := by
    rw [mul_assoc, ← Real.rpow_natCast X 6, ← Real.rpow_add hX0, ← Real.rpow_add hX0]
    norm_num
  simpa only [Real.rpow_one] using h

/-- `(K_ℓds)^{-1} = X^{-11/2}` -/
lemma fsr_Kl_d_s_inv {X : ℝ} (hX0 : 0 < X) :
    (X ^ (-(3 / 2) : ℝ) * X ^ 6 * X)⁻¹ = X ^ (-(11 / 2) : ℝ) := by
  rw [fsr_Kl_d_s hX0, Real.rpow_neg hX0.le]

/-- FS's log argument at FS's parameters: `K_ℓds/(μa³)^{1/2} = X^{-156}` -/
lemma fsr_ratio {X : ℝ} (hX0 : 0 < X) :
    X ^ (-(3 / 2) : ℝ) * X ^ 6 * X / (1 * (fsrA X) ^ 3) ^ (1 / 2 : ℝ)
      = X ^ (-(156) : ℝ) := by
  rw [fsr_Kl_d_s hX0, fsrA3_half hX0, div_eq_mul_inv, ← Real.rpow_neg hX0.le,
    ← Real.rpow_add hX0]
  norm_num

/-- `X^{-156} = (X^{-1})^{156}` -/
lemma fsr_neg156_eq {X : ℝ} (hX0 : 0 < X) : X ^ (-(156) : ℝ) = (X⁻¹) ^ (156 : ℝ) := by
  rw [Real.rpow_neg hX0.le, Real.inv_rpow hX0.le]

lemma fsr_one_le_neg156 {X : ℝ} (hX0 : 0 < X) (hX1 : X ≤ 1 / 10) :
    (1 : ℝ) ≤ X ^ (-(156) : ℝ) := by
  rw [fsr_neg156_eq hX0]
  refine Real.one_le_rpow ?_ (by norm_num)
  rw [le_inv_comm₀ (by norm_num) hX0]
  linarith

/-- `ε_T·c₂ = ½X^{1/4}` -/
lemma fsr_eT_c2 {X : ℝ} (hX0 : 0 < X) :
    X ^ (23 / 4 : ℝ) * fsrC2 X = (1 / 2) * X ^ (1 / 4 : ℝ) := by
  rw [fsrC2, ← mul_assoc, mul_comm (X ^ (23 / 4 : ℝ)) (1 / 2), mul_assoc,
    ← Real.rpow_add hX0]
  norm_num

/-! ## 4. The cutoff `T` and the error `ε` -/

lemma fsrT_pos {X : ℝ} (hX0 : 0 < X) : 0 < fsrT X := by rw [fsrT]; positivity

lemma fsrT_one_le {X : ℝ} (hX0 : 0 < X) (hX1 : X ≤ 1 / 10) : 1 ≤ fsrT X := by
  rw [fsrT]
  have h := fsr_one_le_rpow_neg hX0 hX1 (show (0 : ℝ) ≤ 1 / 4 by norm_num)
  nlinarith [h]

lemma fsrT_log {X : ℝ} (hX0 : 0 < X) :
    Real.log (fsrT X) = 4 * Real.log 10 + (1 / 4) * Real.log X⁻¹ := by
  rw [fsrT]
  have hpow : X ^ (-(1 / 4) : ℝ) = (X⁻¹) ^ (1 / 4 : ℝ) := by
    rw [Real.inv_rpow hX0.le, ← Real.rpow_neg hX0.le]
  rw [hpow, Real.log_mul (by positivity)
    (ne_of_gt (Real.rpow_pos_of_pos (inv_pos.mpr hX0) _)), Real.log_pow,
    Real.log_rpow (inv_pos.mpr hX0)]
  push_cast
  ring

lemma fsrT_inv {X : ℝ} (hX0 : 0 < X) : (fsrT X)⁻¹ = X ^ (1 / 4 : ℝ) / 10 ^ 4 := by
  rw [fsrT, mul_inv, Real.rpow_neg hX0.le, inv_inv, div_eq_mul_inv]
  ring

lemma fsrT_div_c2_pos {X : ℝ} (hX0 : 0 < X) : 0 < fsrT X / fsrC2 X :=
  div_pos (fsrT_pos hX0) (by rw [fsrC2]; positivity)

/-- `T/c₂ = 2·10⁴·X^{-1/4}X^{11/2} ≤ 2·10⁴` -/
lemma fsrT_div_c2_eq {X : ℝ} (hX0 : 0 < X) :
    fsrT X / fsrC2 X = 2 * 10 ^ 4 * (X ^ (-(1 / 4) : ℝ) * X ^ (11 / 2 : ℝ)) := by
  rw [fsrT, fsrC2, div_eq_mul_inv, mul_inv, Real.rpow_neg hX0.le (11 / 2), inv_inv]
  ring

lemma fsrT_div_c2_le {X : ℝ} (hX0 : 0 < X) (hX1 : X ≤ 1 / 10) :
    fsrT X / fsrC2 X ≤ 2 * 10 ^ 4 := by
  rw [fsrT_div_c2_eq hX0]
  have h1 : X ^ (-(1 / 4) : ℝ) * X ^ (11 / 2 : ℝ) ≤ 1 := by
    rw [← Real.rpow_add hX0]
    exact Real.rpow_le_one hX0.le (by linarith) (by norm_num)
  have h2 : (0 : ℝ) ≤ X ^ (-(1 / 4) : ℝ) * X ^ (11 / 2 : ℝ) :=
    mul_nonneg (Real.rpow_nonneg hX0.le _) (Real.rpow_nonneg hX0.le _)
  nlinarith [h1, h2]

/-- **`lhyEps` at FS's parameters**: the four terms of `ε(μ,ρ_z)` evaluated
(`a = X^{323/3}`, `R = 0`, `ε_T = X^{23/4}`, `K_ℓ = X^{-3/2}`, `s = X`, `d = X^6`,
`μ = 1`).  This is `Work.BoseB6Est.fsRegimeArith.lhyEps_fs`. -/
lemma fsrE_eq {X : ℝ} (hX0 : 0 < X) :
    fsrE X = X ^ (23 / 4 : ℝ) + X ^ (1 / 2 : ℝ) * (1 + 162 * Real.log X⁻¹)
      + X ^ (1 / 4 : ℝ) * (1 + 156 * Real.log X⁻¹) := by
  rw [fsrE, fsrA]
  exact Work.BoseB6Est.fsRegimeArith.lhyEps_fs X hX0

/-- **The lower bound**: FS's error dominates `X^{1/4}·156·log X^{-1}`. -/
lemma fsrE_lower {X : ℝ} (hX0 : 0 < X) (hX1 : X ≤ 1 / 10) :
    X ^ (1 / 4 : ℝ) * 156 * Real.log X⁻¹ ≤ fsrE X := by
  rw [fsrE_eq hX0]
  have hL : (0 : ℝ) ≤ Real.log X⁻¹ := fsr_log_inv_nonneg hX0 hX1
  have h1 : (0 : ℝ) ≤ X ^ (23 / 4 : ℝ) := Real.rpow_nonneg hX0.le _
  have h2 : (0 : ℝ) ≤ X ^ (1 / 2 : ℝ) := Real.rpow_nonneg hX0.le _
  have h3 : (0 : ℝ) ≤ X ^ (1 / 4 : ℝ) := Real.rpow_nonneg hX0.le _
  have hexp : X ^ (23 / 4 : ℝ) + X ^ (1 / 2 : ℝ) * (1 + 162 * Real.log X⁻¹)
      + X ^ (1 / 4 : ℝ) * (1 + 156 * Real.log X⁻¹)
      = X ^ (1 / 4 : ℝ) * 156 * Real.log X⁻¹
        + (X ^ (23 / 4 : ℝ) + X ^ (1 / 2 : ℝ) * (1 + 162 * Real.log X⁻¹)
          + X ^ (1 / 4 : ℝ)) := by ring
  rw [hexp]
  nlinarith [h1, h2, h3, hL]

/-- FS's error is nonnegative at FS's parameters -/
lemma fsrE_nonneg {X : ℝ} (hX0 : 0 < X) (hX1 : X ≤ 1 / 10) : 0 ≤ fsrE X := by
  have h := fsrE_lower hX0 hX1
  have h1 : (0 : ℝ) ≤ X ^ (1 / 4 : ℝ) := Real.rpow_nonneg hX0.le _
  have h2 : (0 : ℝ) ≤ Real.log X⁻¹ := fsr_log_inv_nonneg hX0 hX1
  nlinarith [h, h1, h2]

/-- The master bound: any `C ∈ [0, 156·log X^{-1}]` gives `X^{1/4}C ≤ ε`. -/
lemma fsrE_mono {X : ℝ} (hX0 : 0 < X) (hX1 : X ≤ 1 / 10) {C : ℝ} (hC0 : 0 ≤ C)
    (hC : C ≤ 156 * Real.log X⁻¹) : X ^ (1 / 4 : ℝ) * C ≤ fsrE X := by
  have h1 := fsrE_lower hX0 hX1
  have h2 : X ^ (1 / 4 : ℝ) * C ≤ X ^ (1 / 4 : ℝ) * (156 * Real.log X⁻¹) :=
    mul_le_mul_of_nonneg_left hC (Real.rpow_nonneg hX0.le _)
  linarith

/-! ## 5. The mode number `n` and the box side `ℓ` -/

lemma fsrM_ge {X : ℝ} : (10 : ℝ) ^ 6 * X ^ (-(1 / 4) : ℝ) ≤ (fsrN X : ℝ) + 1 := by
  have h := Nat.le_ceil (10 ^ 6 * X ^ (-(1 / 4) : ℝ))
  rw [fsrN]
  linarith

lemma fsrM_pos {X : ℝ} (hX0 : 0 < X) : 0 < (fsrN X : ℝ) + 1 := by
  have h := fsrM_ge (X := X)
  have h1 : (0 : ℝ) ≤ X ^ (-(1 / 4) : ℝ) := Real.rpow_nonneg hX0.le _
  have h2 : (0 : ℝ) < (10 : ℝ) ^ 6 := by norm_num
  nlinarith

lemma fsrM_ge_ten6 {X : ℝ} (hX0 : 0 < X) (hX1 : X ≤ 1 / 10) :
    (10 : ℝ) ^ 6 ≤ (fsrN X : ℝ) + 1 := by
  have h := fsrM_ge (X := X)
  have h1 : (1 : ℝ) ≤ X ^ (-(1 / 4) : ℝ) :=
    fsr_one_le_rpow_neg hX0 hX1 (show (0 : ℝ) ≤ 1 / 4 by norm_num)
  nlinarith [h, h1]

lemma fsrN_one_le {X : ℝ} (hX0 : 0 < X) (hX1 : X ≤ 1 / 10) : 1 ≤ fsrN X := by
  have h := fsrM_ge_ten6 hX0 hX1
  have hR : (1 : ℝ) ≤ (fsrN X : ℝ) := by linarith
  exact_mod_cast hR

/-- `ℓ = (n+1)/√(ρ_z a)` is positive -/
lemma fsrL_pos {X : ℝ} (hX0 : 0 < X) : 0 < fsrL X :=
  div_pos (fsrM_pos hX0) (Real.sqrt_pos_of_pos (fsrA_pos hX0))

/-- `ℓ³ ≥ 3` -/
lemma fsrL_cube_ge_three {X : ℝ} (hX0 : 0 < X) (hX1 : X ≤ 1 / 10) :
    3 ≤ (fsrL X) ^ 3 := by
  rw [fsrL, div_pow]
  have hsqrt : 0 < (Real.sqrt (fsrA X)) ^ 3 := pow_pos (Real.sqrt_pos_of_pos (fsrA_pos hX0)) 3
  rw [le_div_iff₀ hsqrt, fsrA_sqrt_cube hX0]
  have ha : X ^ (323 / 2 : ℝ) ≤ 1 := Real.rpow_le_one hX0.le (by linarith) (by norm_num)
  have h3 : (3 : ℝ) * X ^ (323 / 2 : ℝ) ≤ 3 := by nlinarith [ha]
  have hm : (10 : ℝ) ^ 6 ≤ (fsrN X : ℝ) + 1 := fsrM_ge_ten6 hX0 hX1
  have hm3 : (3 : ℝ) ≤ ((fsrN X : ℝ) + 1) ^ 3 := by
    have h4 : (((10 : ℝ) ^ 6)) ^ 3 ≤ ((fsrN X : ℝ) + 1) ^ 3 :=
      pow_le_pow_left₀ (by norm_num) hm 3
    nlinarith [h4]
  linarith

/-- the mesh relation `(n:ℝ)+1 = ℓ√(ρ_z a)` -/
lemma fsrL_mul_sqrt {X : ℝ} (hX0 : 0 < X) :
    (fsrN X : ℝ) + 1 = fsrL X * Real.sqrt (1 * fsrA X) := by
  rw [fsrL, one_mul]
  exact (div_mul_cancel₀ _ (ne_of_gt (Real.sqrt_pos_of_pos (fsrA_pos hX0)))).symm

/-- `T ≤ √3π(n+1)`: the mode lattice covers the kernel's support -/
lemma fsrT_le_sqrt3PiM {X : ℝ} (hX0 : 0 < X) (hX1 : X ≤ 1 / 10) :
    fsrT X ≤ Real.sqrt 3 * Real.pi * ((fsrN X : ℝ) + 1) := by
  have h5 : (1 : ℝ) ≤ Real.sqrt 3 * Real.pi := by
    have h1 : (1 : ℝ) ≤ Real.sqrt 3 := by
      rw [Real.le_sqrt (by norm_num) (by norm_num)]; norm_num
    nlinarith [Real.pi_gt_three, Real.sqrt_nonneg 3]
  have hm : (10 : ℝ) ^ 6 * X ^ (-(1 / 4) : ℝ) ≤ (fsrN X : ℝ) + 1 := fsrM_ge (X := X)
  have hpow : (0 : ℝ) ≤ X ^ (-(1 / 4) : ℝ) := Real.rpow_nonneg hX0.le _
  have hT : fsrT X ≤ (10 : ℝ) ^ 6 * X ^ (-(1 / 4) : ℝ) := by
    rw [fsrT]; nlinarith [hpow]
  have hm0 : (0 : ℝ) ≤ (fsrN X : ℝ) + 1 := (fsrM_pos hX0).le
  calc fsrT X ≤ (10 : ℝ) ^ 6 * X ^ (-(1 / 4) : ℝ) := hT
    _ ≤ (fsrN X : ℝ) + 1 := hm
    _ ≤ Real.sqrt 3 * Real.pi * ((fsrN X : ℝ) + 1) := by nlinarith [h5, hm0]

/-! ## 6. The mass bound `hI2` -/

lemma fsrA_sq_sqrt {X : ℝ} (hX0 : 0 < X) :
    (fsrA X) ^ 2 * Real.sqrt (fsrA X) = X ^ (1615 / 6 : ℝ) := by
  rw [Real.sqrt_eq_rpow, fsrA, ← Real.rpow_natCast (X ^ (323 / 3 : ℝ)) 2,
    ← Real.rpow_mul hX0.le, ← Real.rpow_mul hX0.le, ← Real.rpow_add hX0]
  norm_num

/-- `ρ_z²a√(ρ_za³)·(I₂ bound) ≤ 1` at the witness kernel. -/
lemma fsrI2_le_one {X : ℝ} (hX0 : 0 < X) (hX1 : X ≤ 1 / 10) :
    fsrA X ^ 2 * Real.sqrt (1 * fsrA X)
        * (2 * Real.pi * (8 * Real.pi) ^ 2 * fsrT X) / (2 * Real.pi) ^ 3 ≤ 1 := by
  have hLHS : fsrA X ^ 2 * Real.sqrt (1 * fsrA X)
      * (2 * Real.pi * (8 * Real.pi) ^ 2 * fsrT X) / (2 * Real.pi) ^ 3
      = 16 * 10 ^ 4 * (X ^ (1615 / 6 : ℝ) * X ^ (-(1 / 4) : ℝ)) := by
    rw [one_mul, fsrA_sq_sqrt hX0, fsrT, div_eq_iff (by positivity : (2 * Real.pi) ^ 3 ≠ 0)]
    ring
  rw [hLHS]
  have h1 : X ^ (1615 / 6 : ℝ) * X ^ (-(1 / 4) : ℝ) ≤ X ^ (10 : ℝ) := by
    rw [← Real.rpow_add hX0]
    exact Real.rpow_le_rpow_of_exponent_ge hX0 (by linarith) (by norm_num)
  have h2 : X ^ (10 : ℝ) ≤ 1 / (10 : ℝ) ^ 10 := by
    have h : X ^ (10 : ℝ) ≤ ((1 : ℝ) / 10) ^ (10 : ℝ) :=
      Real.rpow_le_rpow hX0.le hX1 (z := (10 : ℝ)) (by norm_num)
    have h10 : ((1 : ℝ) / 10) ^ (10 : ℝ) = 1 / (10 : ℝ) ^ 10 := by norm_num
    rwa [h10] at h
  have h4 : X ^ (1615 / 6 : ℝ) * X ^ (-(1 / 4) : ℝ) ≤ 1 / (10 : ℝ) ^ 10 :=
    le_trans h1 h2
  calc 16 * 10 ^ 4 * (X ^ (1615 / 6 : ℝ) * X ^ (-(1 / 4) : ℝ))
      ≤ 16 * 10 ^ 4 * (1 / (10 : ℝ) ^ 10) :=
        mul_le_mul_of_nonneg_left h4 (by norm_num)
    _ ≤ 1 := by norm_num

/-! ## 7. The `I₁` regime at FS's parameters -/

theorem fsrI1 {X : ℝ} (hX0 : 0 < X) (hX1 : X ≤ 1 / 10) :
    FsI1Regime (fsrK X hX0) (fsrA X) 0 1 1 (X ^ (23 / 4 : ℝ)) (fsrC1 X) (fsrC2 X)
      (X ^ (-(3 / 2) : ℝ)) X (X ^ 6) := by
  have hle1 : X ≤ 1 := by linarith
  have hL2 := fsr_log_inv_ge_two hX0 hX1
  have hE : (0 : ℝ) ≤ fsrE X := fsrE_nonneg hX0 hX1
  refine
    { ha := fsrA_pos hX0
      hR := le_rfl
      hρz := one_pos
      hμ := one_pos
      hKl := Real.rpow_pos_of_pos hX0 _
      hs := hX0
      hd := by positivity
      hε0 := Real.rpow_nonneg hX0.le _
      hε1 := ?_
      hc1 := by rw [fsrC1]; positivity
      hc12 := ?_
      hcc1 := ?_
      hc1val := ?_
      hc2val := ?_
      hclose1 := by norm_num
      hclose2 := by norm_num
      hKl1 := ?_
      hd1 := ?_
      hlog1 := ?_
      hB := ?_
      hηT := by rw [fsrK_eta X hX0]; simp
      hT1 := by rw [fsrK_T X hX0]; exact fsrT_one_le hX0 hX1
      hc1T := ?_
      hTsupp := ?_
      hTm := ?_
      hsmall := by simp
      hI2 := ?_
      hEpsEta := by rw [fsrK_eta X hX0]; show (0 : ℝ) ≤ fsrE X; exact hE
      hEpsT := ?_
      hEpsR := by simp only [Real.sqrt_zero, mul_zero]; show (0 : ℝ) ≤ fsrE X; exact hE
      hEpsKl := ?_
      hEpsLog := ?_
      hEpsLogT := ?_
      hEpsTlog := ?_
      hTtail := ?_ }
  · -- `ε_T ≤ 1/2`
    have h2 : X ^ (23 / 4 : ℝ) ≤ ((1 : ℝ) / 10) ^ (23 / 4 : ℝ) :=
      Real.rpow_le_rpow hX0.le hX1 (by norm_num)
    have h4 : (2 : ℝ) ≤ (10 : ℝ) ^ (23 / 4 : ℝ) := by
      have h5 : (10 : ℝ) ^ (23 / 4 : ℝ)
          = (10 : ℝ) ^ (5 : ℝ) * (10 : ℝ) ^ (3 / 4 : ℝ) := by
        rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 10)]; norm_num
      rw [h5]
      have h6 : (1 : ℝ) ≤ (10 : ℝ) ^ (3 / 4 : ℝ) := Real.one_le_rpow (by norm_num) (by norm_num)
      have h7 : (1 : ℝ) ≤ (10 : ℝ) ^ (5 : ℝ) := by
        rw [show (5 : ℝ) = ((5 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
        norm_num
      nlinarith [h6, h7]
    have h8 : ((1 : ℝ) / 10) ^ (23 / 4 : ℝ) ≤ 1 / 2 := by
      have h9 : ((1 : ℝ) / 10) ^ (23 / 4 : ℝ) = ((10 : ℝ) ^ (23 / 4 : ℝ))⁻¹ := by
        rw [one_div, Real.inv_rpow (by norm_num : (0 : ℝ) ≤ 10)]
      rw [h9, inv_eq_one_div]
      exact one_div_le_one_div_of_le (by norm_num) h4
    linarith
  · -- `c₁ ≤ c₂`
    rw [fsrC1, fsrC2]
    have h1 : X ^ (1 / 2 : ℝ) ≤ 1 := Real.rpow_le_one hX0.le hle1 (by norm_num)
    have h2 : (1 : ℝ) ≤ X ^ (-(11 / 2) : ℝ) :=
      fsr_one_le_rpow_neg hX0 hX1 (by norm_num)
    nlinarith [h1, h2]
  · -- `c₁ + ε_Tc₂ ≤ 1`
    rw [fsrC1, fsr_eT_c2 hX0]
    have h1 : X ^ (1 / 2 : ℝ) ≤ 1 := Real.rpow_le_one hX0.le hle1 (by norm_num)
    have h2 : X ^ (1 / 4 : ℝ) ≤ 1 := Real.rpow_le_one hX0.le hle1 (by norm_num)
    linarith
  · -- `c₁ = ½(K_ℓs)^{-1}√(μ/ρ_z)`
    rw [fsrC1, fsr_Kl_inv hX0]
    norm_num
  · -- `c₂ = ½(K_ℓds)^{-1}√(μ/ρ_z)`
    rw [fsrC2, fsr_Kl_d_s_inv hX0]
    norm_num
  · -- `1 ≤ K_ℓs`
    rw [fsr_Kl_mul_s hX0]
    exact fsr_one_le_rpow_neg hX0 hX1 (by norm_num)
  · -- `d ≤ 1`
    exact pow_le_one₀ hX0.le hle1
  · -- `1 ≤ K_ℓds/(μa³)^{1/2}`
    rw [fsr_ratio hX0]
    exact fsr_one_le_neg156 hX0 hX1
  · -- `B ≤ 100`
    rw [fsrK_B X hX0]
    nlinarith [Real.pi_lt_four]
  · -- `c₁ < T`
    rw [fsrK_T X hX0, fsrC1]
    have h1 : X ^ (1 / 2 : ℝ) ≤ 1 := Real.rpow_le_one hX0.le hle1 (by norm_num)
    have h2 := fsrT_one_le hX0 hX1
    nlinarith
  · -- `T√(ρ_za)R ≤ K_ℓds/√(μa)`
    simp only [mul_zero]
    exact div_nonneg (mul_nonneg (mul_nonneg (Real.rpow_nonneg hX0.le _)
      (pow_pos hX0 6).le) hX0.le) (Real.sqrt_nonneg _)
  · -- `T(μa³)^{1/2} ≤ K_ℓds/(μa³)^{1/2}`
    rw [fsrK_T X hX0]
    have hT : fsrT X * (1 * (fsrA X) ^ 3) ^ (1 / 2 : ℝ) ≤ (10 : ℝ) ^ 4 := by
      rw [fsrT, fsrA3_half hX0]
      have h : X ^ (-(1 / 4) : ℝ) * X ^ (323 / 2 : ℝ) ≤ 1 := by
        rw [← Real.rpow_add hX0]
        exact Real.rpow_le_one hX0.le hle1 (by norm_num)
      nlinarith [h]
    have hR : (10 : ℝ) ^ 4
        ≤ X ^ (-(3 / 2) : ℝ) * X ^ 6 * X / (1 * (fsrA X) ^ 3) ^ (1 / 2 : ℝ) := by
      rw [fsr_ratio hX0, fsr_neg156_eq hX0]
      calc (10 : ℝ) ^ 4 ≤ (10 : ℝ) ^ (156 : ℝ) := by
            rw [show (156 : ℝ) = ((156 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
            norm_num
        _ ≤ (X⁻¹) ^ (156 : ℝ) := by
            refine Real.rpow_le_rpow (by norm_num) ?_ (by norm_num)
            rw [le_inv_comm₀ (by norm_num) hX0]
            linarith
    linarith
  · -- `fsGω0 ≤ 1`
    have hb := fsI2_le_bound (fsrK X hX0)
    rw [fsrK_B X hX0, fsrK_T X hX0] at hb
    have hpos : (0 : ℝ) < (2 * Real.pi) ^ 3 := by positivity
    have hnum : fsrA X ^ 2 * Real.sqrt (1 * fsrA X) * fsI2 (fsrK X hX0)
        ≤ fsrA X ^ 2 * Real.sqrt (1 * fsrA X) * (2 * Real.pi * (8 * Real.pi) ^ 2 * fsrT X) :=
      mul_le_mul_of_nonneg_left hb (mul_nonneg (sq_nonneg _) (Real.sqrt_nonneg _))
    rw [fsGω0]
    exact le_trans (div_le_div_of_nonneg_right hnum hpos.le) (fsrI2_le_one hX0 hX1)
  · -- `ε_T ≤ ε`
    have h1 : X ^ (23 / 4 : ℝ) ≤ X ^ (1 / 4 : ℝ) := fsr_rpow_le_of_le hX0 hX1 (by norm_num)
    have h2 : X ^ (1 / 4 : ℝ) * 1 ≤ fsrE X := fsrE_mono hX0 hX1 (C := 1) (by norm_num) (by linarith)
    show X ^ (23 / 4 : ℝ) ≤ fsrE X
    linarith
  · -- `(K_ℓs)^{-1} ≤ ε`
    rw [fsr_Kl_inv hX0]
    have h1 : X ^ (1 / 2 : ℝ) ≤ X ^ (1 / 4 : ℝ) := fsr_rpow_le_of_le hX0 hX1 (by norm_num)
    have h2 : X ^ (1 / 4 : ℝ) * 1 ≤ fsrE X := fsrE_mono hX0 hX1 (C := 1) (by norm_num) (by linarith)
    show X ^ (1 / 2 : ℝ) ≤ fsrE X
    linarith
  · -- `(K_ℓs)^{-1}(1 + log(T/c₂)) ≤ ε`
    have hlog1 : 1 + Real.log ((fsrK X hX0).T / fsrC2 X) ≤ 38 := by
      rw [fsrK_T X hX0]
      have h1 : Real.log (fsrT X / fsrC2 X) ≤ Real.log (2 * 10 ^ 4) :=
        Real.log_le_log (fsrT_div_c2_pos hX0) (fsrT_div_c2_le hX0 hX1)
      have h2 : Real.log (2 * 10 ^ 4) ≤ 1 + 4 * Real.log 10 := fsr_log_two_ten_le
      have h3 : Real.log 10 ≤ 9 := by
        linarith [Real.log_le_sub_one_of_pos (show (0 : ℝ) < 10 by norm_num)]
      have h4 : Real.log (2 * 10 ^ 4) ≤ 37 := by linarith
      have h5 : 1 + Real.log (fsrT X / fsrC2 X) ≤ 1 + 37 :=
        add_le_add_right (le_trans h1 h4) 1
      exact le_trans h5 (by norm_num)
    have hC := fsrE_mono hX0 hX1 (C := 38) (by norm_num) (by linarith)
    rw [fsr_Kl_inv hX0]
    calc X ^ (1 / 2 : ℝ) * (1 + Real.log ((fsrK X hX0).T / fsrC2 X))
        ≤ X ^ (1 / 2 : ℝ) * 38 :=
          mul_le_mul_of_nonneg_left hlog1 (Real.rpow_nonneg hX0.le _)
      _ ≤ X ^ (1 / 4 : ℝ) * 38 :=
          mul_le_mul_of_nonneg_right (fsr_rpow_le_of_le hX0 hX1 (by norm_num)) (by norm_num)
      _ ≤ fsrE X := hC
  · -- `(c₁ + ε_Tc₂)log T ≤ ε`
    have h1 : fsrC1 X + X ^ (23 / 4 : ℝ) * fsrC2 X ≤ X ^ (1 / 4 : ℝ) := by
      rw [fsrC1, fsr_eT_c2 hX0]
      have h2 : X ^ (1 / 2 : ℝ) ≤ X ^ (1 / 4 : ℝ) := fsr_rpow_le_of_le hX0 hX1 (by norm_num)
      linarith
    have hlogeq : Real.log (fsrK X hX0).T = 4 * Real.log 10 + (1 / 4) * Real.log X⁻¹ := by
      rw [fsrK_T X hX0]; exact fsrT_log hX0
    have hlog0 : (0 : ℝ) ≤ Real.log (fsrK X hX0).T := by
      have h := fsr_log_ten_ge_two
      rw [hlogeq]
      linarith [fsr_log_inv_nonneg hX0 hX1]
    have hC0 : (0 : ℝ) ≤ 4 * Real.log 10 + (1 / 4) * Real.log X⁻¹ := by
      have h := fsr_log_ten_ge_two
      linarith [fsr_log_inv_nonneg hX0 hX1]
    have hC : 4 * Real.log 10 + (1 / 4) * Real.log X⁻¹ ≤ 156 * Real.log X⁻¹ := by
      have h3 : Real.log 10 ≤ 9 := by
        linarith [Real.log_le_sub_one_of_pos (show (0 : ℝ) < 10 by norm_num)]
      linarith
    calc (fsrC1 X + X ^ (23 / 4 : ℝ) * fsrC2 X) * Real.log (fsrK X hX0).T
        ≤ X ^ (1 / 4 : ℝ) * (4 * Real.log 10 + (1 / 4) * Real.log X⁻¹) :=
          mul_le_mul h1 hlogeq.le hlog0 (Real.rpow_nonneg hX0.le _)
      _ ≤ fsrE X := fsrE_mono hX0 hX1 hC0 hC
  · -- `(B + 8π)²log T/T ≤ ε`
    have hπ : (16 * Real.pi) ^ 2 ≤ 4096 := by
      have h1 : (16 * Real.pi) ^ 2 = 256 * Real.pi ^ 2 := by ring
      rw [h1]
      nlinarith [Real.pi_lt_four, Real.pi_pos]
    have hlogeq : Real.log (fsrK X hX0).T = 4 * Real.log 10 + (1 / 4) * Real.log X⁻¹ := by
      rw [fsrK_T X hX0]; exact fsrT_log hX0
    have hinv : ((fsrK X hX0).T)⁻¹ = X ^ (1 / 4 : ℝ) / 10 ^ 4 := by
      rw [fsrK_T X hX0]; exact fsrT_inv hX0
    have hC0 : (0 : ℝ) ≤ 4096 * (4 * Real.log 10 + (1 / 4) * Real.log X⁻¹) / 10 ^ 4 := by
      have h1 := fsr_log_ten_ge_two
      have h2 := fsr_log_inv_nonneg hX0 hX1
      positivity
    have hC : 4096 * (4 * Real.log 10 + (1 / 4) * Real.log X⁻¹) / 10 ^ 4
        ≤ 156 * Real.log X⁻¹ := by
      have h3 : Real.log 10 ≤ 9 := by
        linarith [Real.log_le_sub_one_of_pos (show (0 : ℝ) < 10 by norm_num)]
      have hL := fsr_log_inv_ge_two hX0 hX1
      linarith
    rw [fsrK_B X hX0, show (8 * Real.pi + 8 * Real.pi) = 16 * Real.pi by ring]
    calc (16 * Real.pi) ^ 2 * Real.log (fsrK X hX0).T / (fsrK X hX0).T
        = (16 * Real.pi) ^ 2
            * (X ^ (1 / 4 : ℝ) * (4 * Real.log 10 + (1 / 4) * Real.log X⁻¹) / 10 ^ 4) := by
          rw [div_eq_mul_inv, hinv, hlogeq, div_eq_mul_inv]
          ring
      _ ≤ 4096 * (X ^ (1 / 4 : ℝ) * (4 * Real.log 10 + (1 / 4) * Real.log X⁻¹) / 10 ^ 4) := by
          have h : (0 : ℝ) ≤ X ^ (1 / 4 : ℝ) * (4 * Real.log 10 + (1 / 4) * Real.log X⁻¹) / 10 ^ 4 := by
            have h1 := fsr_log_ten_ge_two
            have h2 := fsr_log_inv_nonneg hX0 hX1
            positivity
          exact mul_le_mul_of_nonneg_right hπ h
      _ = X ^ (1 / 4 : ℝ) * (4096 * (4 * Real.log 10 + (1 / 4) * Real.log X⁻¹) / 10 ^ 4) := by
          rw [div_eq_mul_inv, div_eq_mul_inv]
          ring
      _ ≤ fsrE X := fsrE_mono hX0 hX1 hC0 hC
  · -- the cutoff tail `4π(8π)³/(2T) ≤ ε`
    have hpi4 : Real.pi ^ 4 ≤ 256 := by
      calc Real.pi ^ 4 ≤ 4 ^ 4 := pow_le_pow_left₀ Real.pi_pos.le Real.pi_lt_four.le 4
        _ = 256 := by norm_num
    have hpow : 4 * Real.pi * (8 * Real.pi) ^ 3 / 2 = 1024 * Real.pi ^ 4 := by ring
    have hinv : ((fsrK X hX0).T)⁻¹ = X ^ (1 / 4 : ℝ) / 10 ^ 4 := by
      rw [fsrK_T X hX0]; exact fsrT_inv hX0
    have hC0 : (0 : ℝ) ≤ 1024 * 256 / 10 ^ 4 := by norm_num
    have hC : 1024 * 256 / 10 ^ 4 ≤ 156 * Real.log X⁻¹ := by
      have hL := fsr_log_inv_ge_two hX0 hX1
      linarith
    calc 4 * Real.pi * (8 * Real.pi) ^ 3 / (2 * (fsrK X hX0).T)
        = (4 * Real.pi * (8 * Real.pi) ^ 3 / 2) * ((fsrK X hX0).T)⁻¹ := by
          rw [div_eq_mul_inv, mul_inv]; ring
      _ = (1024 * Real.pi ^ 4) * (X ^ (1 / 4 : ℝ) / 10 ^ 4) := by rw [hpow, hinv]
      _ ≤ (1024 * 256) * (X ^ (1 / 4 : ℝ) / 10 ^ 4) := by
          have h : (0 : ℝ) ≤ X ^ (1 / 4 : ℝ) / 10 ^ 4 := by positivity
          exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpi4 (by norm_num)) h
      _ = X ^ (1 / 4 : ℝ) * (1024 * 256 / 10 ^ 4) := by
          rw [div_eq_mul_inv, div_eq_mul_inv]; ring
      _ ≤ fsrE X := fsrE_mono hX0 hX1 hC0 hC

/-! ## 8. The zero-point regime at FS's parameters -/

theorem fsrZeroRegime {X : ℝ} (hX0 : 0 < X) (hX1 : X ≤ 1 / 10) :
    FsZeroRegime (fsrN X) (fsrK X hX0) (fsrA X) 0 1 (fsrL X) 1 0 0 0 (X ^ (23 / 4 : ℝ))
      (fsrC1 X) (fsrC2 X) (X ^ (-(3 / 2) : ℝ)) X (X ^ 6) := by
  refine
    { hi1 := fsrI1 hX0 hX1
      hn := fsrN_one_le hX0 hX1
      hℓ := fsrL_pos hX0
      hℓ3 := fsrL_cube_ge_three hX0 hX1
      hrel := fsrL_mul_sqrt hX0
      hTlat := ?_
      hEpsLatt := ?_ }
  · rw [fsrK_T X hX0, ← fsrL_mul_sqrt hX0]
    exact fsrT_le_sqrt3PiM hX0 hX1
  · -- the lattice mesh error vs. `2·10¹¹·ε`
    have h := Work.BoseB6Est.fsRegimeArith.latticeMesh_ceil X hX0 hX1
    have h2 := fsrE_lower hX0 hX1
    have h3 : fsrE X ≤ 2 * 10 ^ 11 * fsrE X := by
      have h0 := fsrE_nonneg hX0 hX1
      nlinarith
    exact le_trans (le_trans (by simpa only [fsrN] using h) h2) h3

/-! ## 9. FS's regime is inhabited -/

/-- **FS's own parameters satisfy the zero-point regime**: `a = X^{323/3}`,
`K_ℓ = X^{-3/2}`, `s = X`, `d = X^6`, `ε_T = X^{23/4}`, `μ = ρ_z = 1`, `R = 0`,
with the free data `n = ⌈10⁶X^{-1/4}⌉`, `T = 10⁴X^{-1/4}`,
`ℓ = (n+1)/√(ρ_za)`, `c₁ = ½X^{1/2}`, `c₂ = ½X^{-11/2}`,
`z = chiM = δ = 0`. -/
theorem fsRegime_fs (X : ℝ) (hX0 : 0 < X) (hX1 : X ≤ 1 / 10) :
    ∃ (n : ℕ) (K : FsKernel) (a R ρz ℓ μ z chiM δ εT c1 c2 Kl s d : ℝ),
      FsZeroRegime n K a R ρz ℓ μ z chiM δ εT c1 c2 Kl s d ∧
      a = X ^ (323 / 3 : ℝ) ∧ Kl = X ^ (-(3 / 2) : ℝ) ∧ s = X ∧ d = X ^ 6 ∧
      εT = X ^ (23 / 4 : ℝ) ∧ μ = 1 ∧ ρz = 1 ∧ R = 0 := by
  refine ⟨fsrN X, fsrK X hX0, fsrA X, 0, 1, fsrL X, 1, 0, 0, 0, X ^ (23 / 4 : ℝ),
    fsrC1 X, fsrC2 X, X ^ (-(3 / 2) : ℝ), X, X ^ 6,
    fsrZeroRegime hX0 hX1, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

end Work.BoseB6Est
