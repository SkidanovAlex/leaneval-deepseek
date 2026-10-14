import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.FDeriv.Defs
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.H2.HQ.Glue
import Submission.Work.FTS.Nonlinear.FstarPkgAll
import Submission.Work.FTS.Nonlinear.Pieces.rl1Pieces.Pgg
import Submission.Work.FTS.Nonlinear.Pieces.rl1Pieces.Pgs
import Submission.Work.FTS.Nonlinear.Pieces.rl1Pieces.Psg
import Submission.Work.FTS.Nonlinear.Pieces.rl1Tools.FzFacts
import Submission.Work.FTS.Nonlinear.Pieces.splitsDiff
import Submission.Work.FTS.OpenPkg.Defs
import Submission.Work.FTS.OpenPkg.WtohWin.Assembly
import Submission.Work.FTS.StrongEps.SupPort.HardyThetaOpen
import Submission.Work.FTS.TransportS.SlotT2.supThetaIntOpen
import Submission.Work.FTS.VocabO
import Submission.Work.H2.T1Q.SupAbsThOAesm
import Submission.Work.Spaces.HkSq_terms
import Submission.Work.Spaces.SmoothCompact_HkMem
import Submission.Work.Spaces.factor_bound
import Submission.Work.Spaces.sin_two_rpow
-- ===== merged: Submission.Work.FTS.Nonlinear.Pieces.rl1Bound =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology ENNReal NNReal
open MeasureTheory Set Filter

namespace Work.FTS.Nonlinear.Pieces

set_option autoImplicit false
set_option linter.unusedVariables false

open Work.FTS.Galerkin (Fn)

/-- The `L²`-functional of `rl1Bound`: `Q f = ∫∫ f² w` with `w = (1+z)²/z²`, i.e. the
Hardy-weighted angular energy whose square root dominates `|L₁₂(f)(0)|`
(`L12_zero_le_weak`).  It is the weighted `L²`-norm in which the `ℋ⁴`-slots of `g` are
controlled, because the `i = 0`-slot of `HkIntegrand` is `(g·w/sin(2θ)^{η/2})²`. -/
def Q (f : Fn) : ℝ := ∫ z in Set.Ioi (0 : ℝ), Work.Spaces.w z
  * ∫ θ in Work.Spaces.Iθ, (f z θ) ^ 2



/-! ## Pointwise bounds from the `𝒲^{l,∞}`-norm -/

/-- The `k = 0` summand of `WlInf` is `supAbs`, so a `WlInfMem`-bound controls `f` in
`L^∞`. -/
theorem supAbs_le_WlInf {α : ℝ} {l : ℕ} {f : ℝ → ℝ → ℝ}
    (hmem : Work.Spaces.WlInfMem α l f) :
    Work.Spaces.supAbs f ≤ Work.Spaces.WlInf α l f := by
  have h0 : Work.Spaces.supAbs f
      = Work.Spaces.supAbs (fun z θ => (z + 1) ^ (0 : ℕ) * Work.Spaces.pzIter 0 f z θ) := by
    simp
  rw [h0, Work.Spaces.WlInf]
  have hth : 0 ≤ ∑ j ∈ Finset.range (l + 1), ∑ k ∈ Finset.range (l + 1),
      if 1 ≤ j ∧ k + j ≤ l then
        Work.Spaces.supAbs (fun z θ => (z + 1) ^ k * Work.Spaces.pzIter k (Work.Spaces.DthIter j f)
          z θ * (Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ)))
      else 0 :=
    Work.Spaces.wlThSum_nonneg α l f hmem
  have hle := Finset.single_le_sum
    (s := Finset.range (l + 1))
    (f := fun k => Work.Spaces.supAbs (fun z θ => (z + 1) ^ k * Work.Spaces.pzIter k f z θ))
    (fun k hk => Work.Spaces.supAbs_nonneg
      (hmem.1 k (Nat.le_of_lt_succ (Finset.mem_range.mp hk))))
    (Finset.mem_range.mpr (Nat.succ_pos l))
  exact le_trans hle (le_add_of_nonneg_right hth)

/-- Pointwise bound from a `𝒲^{l,∞}`-bound. -/
theorem abs_le_WlInf {α : ℝ} {l : ℕ} {f : ℝ → ℝ → ℝ} {B : ℝ}
    (hmem : Work.Spaces.WlInfMem α l f) (h : Work.Spaces.WlInf α l f ≤ B)
    {z θ : ℝ} (hz : z ∈ Work.Spaces.Iz) (hθ : θ ∈ Work.Spaces.Iθ) :
    |f z θ| ≤ B := by
  have hmem' : Work.Spaces.SupFinite f := by
    simpa using hmem.1 0 (Nat.zero_le l)
  exact le_trans (Work.Spaces.abs_le_supAbs hz hθ hmem')
    (le_trans (supAbs_le_WlInf hmem) h)

/-! ## The density functional

`Fa f` is the absolutely convergent density integral `∫_r r⁻¹ ∫_θ |K(θ)f(r,θ)|` of `L₁₂(f)(0)`,
as an `ℝ≥0∞`-valued (lintegral) functional so that no integrability is needed to manipulate it. -/
def Fa (f : Fn) : ℝ≥0∞ := ∫⁻ r in Set.Ioi (0 : ℝ), ENNReal.ofReal r⁻¹
  * (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal |Work.Spaces.K θ * f r θ|)


/-- For a real-valued function on a measure space,
`ofReal |∫ x, h x| ≤ ∫⁻ x, ofReal |h x|`. -/
theorem ofReal_abs_integral_le (h : ℝ → ℝ) (μ : Measure ℝ) (s : Set ℝ) :
    ENNReal.ofReal |∫ x in s, h x ∂μ| ≤ ∫⁻ x in s, ENNReal.ofReal |h x| ∂μ := by
  have h3 := MeasureTheory.norm_integral_le_lintegral_norm h (μ := μ.restrict s)
  rw [Real.norm_eq_abs] at h3
  exact le_trans (ENNReal.ofReal_le_ofReal h3) ENNReal.ofReal_toReal_le

/-- **The `L₁₂`-glue.**  `|L₁₂(f)(0)|` is dominated by the density functional `Fa f`. -/
theorem ofReal_L12_le (f : Fn) :
    ENNReal.ofReal |Work.Construction.L12 f 0| ≤ Fa f := by
  have hL : Work.Construction.L12 f 0
      = ∫ r in Set.Ioi (0 : ℝ), Work.Construction.L12dens f r := rfl
  have hstep : ENNReal.ofReal |∫ r in Set.Ioi (0 : ℝ), Work.Construction.L12dens f r|
      ≤ ∫⁻ r in Set.Ioi (0 : ℝ), ENNReal.ofReal |Work.Construction.L12dens f r| :=
    ofReal_abs_integral_le _ _ _
  rw [hL, Fa]
  refine le_trans hstep ?_
  refine MeasureTheory.lintegral_mono_ae ?_
  filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with r hr
  have h0 : (0 : ℝ) < r := hr
  have h1 : Work.Construction.L12dens f r = r⁻¹ * ∫ θ in Work.Spaces.Iθ,
      (Work.Spaces.K θ * f r θ) := by
    rw [Work.Construction.L12dens, Work.FM.L12dens, Work.Spaces.Iθ]
    rw [show (fun θ : ℝ => Work.Spaces.K θ * f r θ / r)
        = fun θ : ℝ => r⁻¹ * (Work.Spaces.K θ * f r θ) from by
      funext θ; rw [div_eq_inv_mul]]
    rw [MeasureTheory.integral_const_mul]
  have h2 : ENNReal.ofReal |r⁻¹ * ∫ θ in Work.Spaces.Iθ, (Work.Spaces.K θ * f r θ)|
      = ENNReal.ofReal r⁻¹ * ENNReal.ofReal
          |∫ θ in Work.Spaces.Iθ, (Work.Spaces.K θ * f r θ)| := by
    rw [abs_mul, abs_of_pos (inv_pos.mpr h0),
      ENNReal.ofReal_mul (le_of_lt (inv_pos.mpr h0))]
  rw [h1, h2]
  exact mul_le_mul_right (ofReal_abs_integral_le _ _ _) _

/-! ## The vector of per-piece constants

The four estimates `rl1Pieces.Pgg`, `Pgs`, `Psg`, `Pss` give, for the twenty summands
`rl1Tools.pv α g Φs Φg k`, the constants `Mv K1 K2 K3 K4 α X k` below (in the same order as
`pv`): `K₁α^{-1/2}X²` for `N₁^{gg}, N₂^{gg}`, `K₁α^{1/2}X²` for `N₃^{gg}`, `K₁X²` for
`N₄^{gg}, N₅^{gg}`, `K₂α^{1/2}X` for the five `N_i^{gs}`, `K₃α^{1/2}X` for the five
`N_i^{sg}`, and `K₄α²` for the five `N_i^{ss}`.  (The envelope of the target estimate,
`α² + √α·X + α^{-3/2}X²`, is recovered from these in `Mv_sum_le` using
`α^{-1/2} ≤ α^{-3/2}`, `α^{1/2} ≤ α^{-3/2}` and `1 ≤ α^{-3/2}` for `0 < α ≤ 1`.) -/
def Mv (K1 K2 K3 K4 α X : ℝ) : Fin 20 → ℝ :=
  ![K1 * α ^ (-(1 / 2 : ℝ)) * X ^ 2,
    K2 * α ^ (1 / 2 : ℝ) * X,
    K3 * α ^ (1 / 2 : ℝ) * X,
    K4 * α ^ 2,
    K1 * α ^ (-(1 / 2 : ℝ)) * X ^ 2,
    K2 * α ^ (1 / 2 : ℝ) * X,
    K3 * α ^ (1 / 2 : ℝ) * X,
    K4 * α ^ 2,
    K1 * α ^ (1 / 2 : ℝ) * X ^ 2,
    K2 * α ^ (1 / 2 : ℝ) * X,
    K3 * α ^ (1 / 2 : ℝ) * X,
    K4 * α ^ 2,
    K1 * X ^ 2,
    K2 * α ^ (1 / 2 : ℝ) * X,
    K3 * α ^ (1 / 2 : ℝ) * X,
    K4 * α ^ 2,
    K1 * X ^ 2,
    K2 * α ^ (1 / 2 : ℝ) * X,
    K3 * α ^ (1 / 2 : ℝ) * X,
    K4 * α ^ 2]

/-- Every entry of `Mv` is nonnegative. -/
theorem Mv_nonneg {K1 K2 K3 K4 α X : ℝ} (h1 : 0 < K1) (h2 : 0 < K2) (h3 : 0 < K3)
    (h4 : 0 < K4) (hα : 0 < α) (hX : 0 ≤ X) : ∀ k : Fin 20, 0 ≤ Mv K1 K2 K3 K4 α X k := by
  have hp : (0 : ℝ) ≤ α ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg hα.le _
  have hq : (0 : ℝ) ≤ α ^ (1 / 2 : ℝ) := Real.rpow_nonneg hα.le _
  have ha : (0 : ℝ) ≤ α ^ 2 := sq_nonneg α
  have hX2 : (0 : ℝ) ≤ X ^ 2 := sq_nonneg X
  intro k
  fin_cases k <;>
    simp only [Mv, Matrix.cons_val_zero, Matrix.cons_val_succ, Fin.reduceFinMk] <;>
    first
      | exact mul_nonneg (mul_nonneg h1.le hp) hX2
      | exact mul_nonneg (mul_nonneg h1.le hq) hX2
      | exact mul_nonneg (mul_nonneg h2.le hq) hX
      | exact mul_nonneg (mul_nonneg h3.le hq) hX
      | exact mul_nonneg h4.le ha
      | exact mul_nonneg h1.le hX2

/-- The sum of the twenty constants of `Mv`. -/
theorem Mv_sum (K1 K2 K3 K4 α X : ℝ) :
    ∑ k : Fin 20, Mv K1 K2 K3 K4 α X k
      = K1 * (2 * α ^ (-(1 / 2 : ℝ)) * X ^ 2 + α ^ (1 / 2 : ℝ) * X ^ 2 + 2 * X ^ 2)
        + 5 * K2 * α ^ (1 / 2 : ℝ) * X + 5 * K3 * α ^ (1 / 2 : ℝ) * X + 5 * K4 * α ^ 2 := by
  simp [Mv, Fin.sum_univ_succ]
  ring

/-- The sum of the twenty constants of `Mv` fits the envelope
`K·(α² + √α·X + α^{-3/2}X²)` with `K = 5(K₁+K₂+K₃+K₄) + 1`, for `0 < α ≤ 1` and `X ≥ 0`. -/
theorem Mv_sum_le {K1 K2 K3 K4 α X : ℝ} (h1 : 0 < K1) (h2 : 0 < K2) (h3 : 0 < K3)
    (h4 : 0 < K4) (hα : 0 < α) (hα1 : α ≤ 1) (hX : 0 ≤ X) :
    ∑ k : Fin 20, Mv K1 K2 K3 K4 α X k
      ≤ (5 * (K1 + K2 + K3 + K4) + 1)
        * (α ^ 2 + Real.sqrt α * X + α ^ (-(3 / 2 : ℝ)) * X ^ 2) := by
  rw [Mv_sum, Real.sqrt_eq_rpow]
  have hp : α ^ (-(1 / 2 : ℝ)) ≤ α ^ (-(3 / 2 : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_ge hα hα1 (show (-(3 / 2 : ℝ)) ≤ -(1 / 2) by norm_num)
  have hq : α ^ (1 / 2 : ℝ) ≤ α ^ (-(3 / 2 : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_ge hα hα1 (show (-(3 / 2 : ℝ)) ≤ 1 / 2 by norm_num)
  have h1r : (1 : ℝ) ≤ α ^ (-(3 / 2 : ℝ)) := by
    have h := Real.rpow_le_rpow_of_exponent_ge hα hα1 (x := α) (y := (0 : ℝ))
      (z := -(3 / 2 : ℝ)) (show (-(3 / 2 : ℝ)) ≤ 0 by norm_num)
    simpa using h
  have hX2 : (0 : ℝ) ≤ X ^ 2 := sq_nonneg X
  have ha2 : (0 : ℝ) ≤ α ^ 2 := by positivity
  have hq0 : (0 : ℝ) ≤ α ^ (1 / 2 : ℝ) * X := mul_nonneg (Real.rpow_nonneg hα.le _) hX
  have hr0 : (0 : ℝ) ≤ α ^ (-(3 / 2 : ℝ)) * X ^ 2 :=
    mul_nonneg (Real.rpow_nonneg hα.le _) hX2
  have hB0 : (0 : ℝ) ≤ α ^ 2 + α ^ (1 / 2 : ℝ) * X + α ^ (-(3 / 2 : ℝ)) * X ^ 2 := by linarith
  have hle_alpha : α ^ 2 ≤ α ^ 2 + α ^ (1 / 2 : ℝ) * X + α ^ (-(3 / 2 : ℝ)) * X ^ 2 := by linarith
  have hle_q : α ^ (1 / 2 : ℝ) * X
      ≤ α ^ 2 + α ^ (1 / 2 : ℝ) * X + α ^ (-(3 / 2 : ℝ)) * X ^ 2 := by linarith
  have hle_r : α ^ (-(3 / 2 : ℝ)) * X ^ 2
      ≤ α ^ 2 + α ^ (1 / 2 : ℝ) * X + α ^ (-(3 / 2 : ℝ)) * X ^ 2 := by linarith
  have hX2r : X ^ 2 ≤ α ^ (-(3 / 2 : ℝ)) * X ^ 2 := by
    calc X ^ 2 = 1 * X ^ 2 := (one_mul _).symm
      _ ≤ α ^ (-(3 / 2 : ℝ)) * X ^ 2 := mul_le_mul_of_nonneg_right h1r hX2
  have hqX2 : α ^ (1 / 2 : ℝ) * X ^ 2 ≤ α ^ (-(3 / 2 : ℝ)) * X ^ 2 :=
    mul_le_mul_of_nonneg_right hq hX2
  have hpX2 : α ^ (-(1 / 2 : ℝ)) * X ^ 2 ≤ α ^ (-(3 / 2 : ℝ)) * X ^ 2 :=
    mul_le_mul_of_nonneg_right hp hX2
  have hK1 : K1 * (2 * α ^ (-(1 / 2 : ℝ)) * X ^ 2 + α ^ (1 / 2 : ℝ) * X ^ 2 + 2 * X ^ 2)
      ≤ 5 * K1 * (α ^ 2 + α ^ (1 / 2 : ℝ) * X + α ^ (-(3 / 2 : ℝ)) * X ^ 2) := by
    have hA : 2 * α ^ (-(1 / 2 : ℝ)) * X ^ 2 + α ^ (1 / 2 : ℝ) * X ^ 2 + 2 * X ^ 2
        ≤ 5 * (α ^ (-(3 / 2 : ℝ)) * X ^ 2) := by linarith [hpX2, hqX2, hX2r]
    calc K1 * (2 * α ^ (-(1 / 2 : ℝ)) * X ^ 2 + α ^ (1 / 2 : ℝ) * X ^ 2 + 2 * X ^ 2)
        ≤ K1 * (5 * (α ^ (-(3 / 2 : ℝ)) * X ^ 2)) := mul_le_mul_of_nonneg_left hA h1.le
      _ = 5 * K1 * (α ^ (-(3 / 2 : ℝ)) * X ^ 2) := by ring
      _ ≤ 5 * K1 * (α ^ 2 + α ^ (1 / 2 : ℝ) * X + α ^ (-(3 / 2 : ℝ)) * X ^ 2) :=
          mul_le_mul_of_nonneg_left hle_r (by linarith [h1])
  have hK2 : 5 * K2 * α ^ (1 / 2 : ℝ) * X
      ≤ 5 * K2 * (α ^ 2 + α ^ (1 / 2 : ℝ) * X + α ^ (-(3 / 2 : ℝ)) * X ^ 2) := by
    calc 5 * K2 * α ^ (1 / 2 : ℝ) * X = 5 * K2 * (α ^ (1 / 2 : ℝ) * X) := by ring
      _ ≤ 5 * K2 * (α ^ 2 + α ^ (1 / 2 : ℝ) * X + α ^ (-(3 / 2 : ℝ)) * X ^ 2) :=
          mul_le_mul_of_nonneg_left hle_q (by linarith [h2])
  have hK3 : 5 * K3 * α ^ (1 / 2 : ℝ) * X
      ≤ 5 * K3 * (α ^ 2 + α ^ (1 / 2 : ℝ) * X + α ^ (-(3 / 2 : ℝ)) * X ^ 2) := by
    calc 5 * K3 * α ^ (1 / 2 : ℝ) * X = 5 * K3 * (α ^ (1 / 2 : ℝ) * X) := by ring
      _ ≤ 5 * K3 * (α ^ 2 + α ^ (1 / 2 : ℝ) * X + α ^ (-(3 / 2 : ℝ)) * X ^ 2) :=
          mul_le_mul_of_nonneg_left hle_q (by linarith [h3])
  have hK4 : 5 * K4 * α ^ 2
      ≤ 5 * K4 * (α ^ 2 + α ^ (1 / 2 : ℝ) * X + α ^ (-(3 / 2 : ℝ)) * X ^ 2) :=
    mul_le_mul_of_nonneg_left hle_alpha (by linarith [h4])
  have hsum : K1 * (2 * α ^ (-(1 / 2 : ℝ)) * X ^ 2 + α ^ (1 / 2 : ℝ) * X ^ 2 + 2 * X ^ 2)
        + 5 * K2 * α ^ (1 / 2 : ℝ) * X + 5 * K3 * α ^ (1 / 2 : ℝ) * X + 5 * K4 * α ^ 2
      ≤ 5 * (K1 + K2 + K3 + K4)
        * (α ^ 2 + α ^ (1 / 2 : ℝ) * X + α ^ (-(3 / 2 : ℝ)) * X ^ 2) := by
    linarith [hK1, hK2, hK3, hK4]
  calc K1 * (2 * α ^ (-(1 / 2 : ℝ)) * X ^ 2 + α ^ (1 / 2 : ℝ) * X ^ 2 + 2 * X ^ 2)
        + 5 * K2 * α ^ (1 / 2 : ℝ) * X + 5 * K3 * α ^ (1 / 2 : ℝ) * X + 5 * K4 * α ^ 2
      ≤ 5 * (K1 + K2 + K3 + K4)
        * (α ^ 2 + α ^ (1 / 2 : ℝ) * X + α ^ (-(3 / 2 : ℝ)) * X ^ 2) := hsum
    _ ≤ (5 * (K1 + K2 + K3 + K4) + 1)
        * (α ^ 2 + α ^ (1 / 2 : ℝ) * X + α ^ (-(3 / 2 : ℝ)) * X ^ 2) := by
        nlinarith [hB0, h1, h2, h3, h4]


end Work.FTS.Nonlinear.Pieces
end
end
-- ===== merged: Submission.Work.FTS.VocabO2 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-! Scratch type-check of `cbc/fts_starpkg_t2.md` (Claude, curric-46, 2026-10-06).
LEAD-FROZEN (curric-46, 2026-10-06) lead file. Design: Submission/Work/FTS/STARPKG_T2_LEAD.md. Do not edit. Was: proposed lead file `FTS/VocabO2.lean` (Part A: definitions) + node statements (Part B, `sorry`). -/

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.VocabO2

open Work.FTS.Galerkin (Fn)
open Work.FTS.VocabO

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## Part A — definitions (the file the lead freezes) -/

/-- `Φ̃_* = Φ_* - (1/4α) sin 2θ L₁₂(F_*)`. -/
abbrev PhiTs (α : ℝ) (Φs : Fn) : Fn :=
  Work.Construction.PhiTil α (Work.Construction.Fstar α) Φs

/-- **The star package with the `𝒲^{4,∞}` (closed-domain `WlInf`) fields the rows consume.**
Every new field is in exactly the form of the consumer clause (`N4Norm'.wprod`, `N4Norm'.wtoh`
via `wtoHQ_of_pointwise_open`, `VocabO.T3Clause`). -/
structure StarPkgo2 (α Cs : ℝ) (Φs : Fn) : Prop extends StarPkgo α Cs Φs where
  /-- rows 10, 11 (`NRow10_of_WlInfStar`, `NRow11_of_wlInf`) -/
  RW : Work.Spaces.WlInfMem α 4 (fun z θ => (z + 1) / z * Work.Construction.Rop α (PhiTs α Φs) z θ) ∧
    Work.Spaces.WlInf α 4 (fun z θ => (z + 1) / z * Work.Construction.Rop α (PhiTs α Φs) z θ)
      ≤ Cs * α
  /-- row 18 (`T3Clause` + `wprod` honesty) -/
  VW : Work.Spaces.WlInfMem α 4 (Work.Construction.Vop (PhiTs α Φs)) ∧
    Work.Spaces.WlInf α 4 (Work.Construction.Vop (PhiTs α Φs)) ≤ Cs * α
  /-- row 19 (`wtoh` on `((z+1)³/z²)N₃^{**} = -2α[((z+1)/z)V]·[((z+1)²/z)D_zF_*]`) -/
  VzW : Work.Spaces.WlInfMem α 4 (fun z θ => (z + 1) / z * Work.Construction.Vop (PhiTs α Φs) z θ) ∧
    Work.Spaces.WlInf α 4 (fun z θ => (z + 1) / z * Work.Construction.Vop (PhiTs α Φs) z θ)
      ≤ Cs * α
  /-- row 14 (`N₂^{sg} = -2(U/s2)·D_θ g` on `Qd`, `wprod` honesty) -/
  UsW : Work.Spaces.WlInfMem α 4
      (fun z θ => Work.Construction.Uop α (PhiTs α Φs) z θ / Work.Construction.s2 θ) ∧
    Work.Spaces.WlInf α 4
      (fun z θ => Work.Construction.Uop α (PhiTs α Φs) z θ / Work.Construction.s2 θ) ≤ Cs * α
  /-- row 15 (`((z+1)³/z²)N₂^{**} = -2[((z+1)/z)(U/s2)]·[((z+1)²/z)D_θF_*]`) -/
  UszW : Work.Spaces.WlInfMem α 4
      (fun z θ => (z + 1) / z * (Work.Construction.Uop α (PhiTs α Φs) z θ / Work.Construction.s2 θ)) ∧
    Work.Spaces.WlInf α 4
      (fun z θ => (z + 1) / z * (Work.Construction.Uop α (PhiTs α Φs) z θ / Work.Construction.s2 θ))
      ≤ Cs * α

/-- `Ŷ = ((z+1)/z)·Φ̃_*/sin 2θ` — the single object whose flat `𝒲`-bound gives every star field. -/
def Ycheck (α : ℝ) (Φs : Fn) : Fn :=
  fun z θ => (z + 1) / z * (PhiTs α Φs z θ / Work.Construction.s2 θ)

/-- **Flat `𝒲^{l,∞}`-type bound on the open quadrant**: plain `(z+1)^k∂_z^k` up to order `l`, and
the flat angular part `(z+1)^k∂_z^k D_θ^i ∂_θ f` for `k+i+1 ≤ l`. -/
def FlatW (l : ℕ) (f : Fn) (K : ℝ) : Prop :=
  ∀ z θ : ℝ, 0 < z → 0 < θ → θ < π / 2 →
    (∀ k : ℕ, k ≤ l → |(z + 1) ^ k * Work.Spaces.pzIter k f z θ| ≤ K) ∧
    (∀ k i : ℕ, k + i + 1 ≤ l →
      |(z + 1) ^ k * Work.Spaces.pzIter k (Work.Spaces.DthIter i (Work.Spaces.pth f)) z θ| ≤ K)

/-- **The analysis target of `FTS/PhiStar`** (replaces the field-by-field targets). -/
structure StarCore (α Cs : ℝ) (Φs : Fn) : Prop where
  sol : Work.Elliptic.IsBslSol α (Work.Construction.Fstar α) Φs
  smooth : Work.FTS.EllipticEst.SmoothOpen Φs
  /-- normal form of the witness: `Φ̃_*` is extended by `0` off the open quadrant
  (free: `IsBslSol` only sees `Q0` and the two boundary lines, where `Θ = 0`) -/
  zeroOff : ∀ z θ : ℝ, (z, θ) ∉ Work.FTS.EllipticEst.Q0 → PhiTs α Φs z θ = 0
  core : FlatW 7 (Ycheck α Φs) (Cs * α)

/-- rows 8–26 with row 16 at the rate `X³` (in `Pbd`'s `α^{-3/2}X³` budget). -/
structure NRows2 (IP : ℝ → Fn → Fn → ℝ) (α K : ℝ) (g Φs Φg : Fn) : Prop where
  r8 : Work.FTS.Nonlin.Xn α (Work.FTS.Nonlin.N1gg α g Φg)
    ≤ K * (α ^ (-(1 / 2 : ℝ)) * Work.FTS.Nonlin.Xn α g ^ 2)
  r9 : Work.FTS.Nonlin.Xn α (Work.FTS.Nonlin.N1gs α g Φg) ≤ K * (Real.sqrt α * Work.FTS.Nonlin.Xn α g)
  r10 : Work.FTS.Nonlin.Xn α (Work.FTS.Nonlin.N1sg α Φs g) ≤ K * (Real.sqrt α * Work.FTS.Nonlin.Xn α g)
  r11 : Work.FTS.Nonlin.Xn α (Work.FTS.Nonlin.N1ss α Φs) ≤ K * α ^ 2
  r12 : |IP α (Work.FTS.Nonlin.N2gg α g Φg) g| ≤ K * (α ^ (-(1 / 2 : ℝ)) * Work.FTS.Nonlin.Xn α g ^ 3)
  r13 : Work.FTS.Nonlin.Xn α (Work.FTS.Nonlin.N2gs α g Φg) ≤ K * (α ^ (3 / 2 : ℝ) * Work.FTS.Nonlin.Xn α g)
  r14 : |IP α (Work.FTS.Nonlin.N2sg α Φs g) g| ≤ K * (Real.sqrt α * Work.FTS.Nonlin.Xn α g ^ 2)
  r15 : Work.FTS.Nonlin.Xn α (Work.FTS.Nonlin.N2ss α Φs) ≤ K * α ^ 2
  /-- **relaxed** (was `K·√α·X³`) -/
  r16 : |IP α (Work.FTS.Nonlin.N3gg α g Φg) g| ≤ K * Work.FTS.Nonlin.Xn α g ^ 3
  r17 : Work.FTS.Nonlin.Xn α (Work.FTS.Nonlin.N3gs α g Φg) ≤ K * (α ^ (3 / 2 : ℝ) * Work.FTS.Nonlin.Xn α g)
  r18 : |IP α (Work.FTS.Nonlin.N3sg α Φs g) g| ≤ K * (α ^ (3 / 2 : ℝ) * Work.FTS.Nonlin.Xn α g ^ 2)
  r19 : Work.FTS.Nonlin.Xn α (Work.FTS.Nonlin.N3ss α Φs) ≤ K * α ^ 3
  r20 : |IP α (Work.FTS.Nonlin.N4gg α g) g| ≤ K * (α ^ (-(1 / 2 : ℝ)) * Work.FTS.Nonlin.Xn α g ^ 3)
  r21 : Work.FTS.Nonlin.Xn α (Work.FTS.Nonlin.N4gs α g) ≤ K * (α ^ (3 / 2 : ℝ) * Work.FTS.Nonlin.Xn α g)
  r22 : |IP α (Work.FTS.Nonlin.N4sg α g) g| ≤ K * (Real.sqrt α * Work.FTS.Nonlin.Xn α g ^ 2)
  r23 : Work.FTS.Nonlin.Xn α (Work.FTS.Nonlin.N4ss α) ≤ K * α ^ 3
  r24 : Work.FTS.Nonlin.Xn α (Work.FTS.Nonlin.N5gg g) ≤ K * Work.FTS.Nonlin.Xn α g ^ 2
  r25 : Work.FTS.Nonlin.Xn α (Work.FTS.Nonlin.N5gs α g) + Work.FTS.Nonlin.Xn α (Work.FTS.Nonlin.N5sg α g)
    ≤ K * (Real.sqrt α * Work.FTS.Nonlin.Xn α g)
  r26 : Work.FTS.Nonlin.Xn α (Work.FTS.Nonlin.N5ss α) ≤ K * α ^ 2


/-! ### The seven row nodes, restated (each `∃ K, 0 < K ∧ ∀ …, Ctx2 … → honesty ∧ bound`) -/

end Work.FTS.VocabO2
end
end
