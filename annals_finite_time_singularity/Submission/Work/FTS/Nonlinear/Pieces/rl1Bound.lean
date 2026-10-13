/-
# `rl1Bound` — the `L₁₂(N)(0)` bound of design §3.5 (L-N4.6)

This file proves `Work.FTS.Nonlinear.Pieces.rl1Bound`: the second of the three zero-mode
estimates of the design table (`AuxRows.rl1`), i.e.

  `|L₁₂(N α (F_* + g) (Φs + Φg))(0)| ≤ K·(α² + √α·X + α^{-3/2}·X²)`,  `X = |g|_{ℋ⁴}`,

under the repaired context (`N4Norm Ci α₂`, `GalClass α g`, `StarPkg α Cs Φs`,
`EllPkgG α Ce g Φg`, `0 < α ≤ 1`, `α ≤ α₂`).

**Route (the paper's, §Modulation, tex 1516–1523).**  `N` is split into its twenty summands
`N₁^{gg}, …, N₅^{ss}` (`splits_of_diff`), and each is estimated separately.  The two devices
are

* the `L²`-route (`L12_zero_le_weak`): `|L₁₂(f)(0)| ≤ 3√(∫∫ f² w)` with `w = (1+z)²/z²`, which
  is exactly the weighted `L²`-slot of `ℋ⁴`; it handles the pieces whose coefficient is only
  known pointwise in `L^∞` (`LinfQ`/`PwBd` for the `Φ̃_g`-coefficients, the `𝒲^{4,∞}`-bounds
  of `StarPkg` for the `Φ̃_*` ones) times a factor of `g` or of the explicit profile `F_*`;
* the `θ`-ibp: because `K(θ) = 3 sin θ cos²θ` vanishes at `θ = 0, π/2`, every factor `D_θg`
  or `D_θF_*` in the `L₁₂`-integrand can be moved onto the coefficient.  The crucial identity
  making this work for the `N₂^{∗g}`, `N₂^{∗∗}` pieces is

    `K(θ)·U(Φ̃_*) = -3 cos³θ·(ℛ(Φ̃_*) - 𝒱(Φ̃_*))`

  (`K/tan θ = 3cos³θ`), so the *unbounded* coefficient `U(Φ̃_*)` is replaced by the two
  coefficients that `StarPkg` bounds pointwise.

Since `θ = 0, π/2` are null sets, all pointwise bounds are only used a.e. on the quadrant.
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.FDeriv.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.Nonlinear.Pieces.Rows
import Submission.Work.Construction.Terms
import Submission.Work.FTS.H2.L12ZeroQ
import Submission.Work.FTS.H2.LinfQ
import Submission.Work.FTS.H2.HQ.Glue
import Submission.Work.FTS.Nonlinear.Pieces.splitsDiff
import Submission.Work.FTS.Nonlinear.Pieces.L12_zero_le_weak
import Submission.Work.FTS.Nonlinear.FstarPkgAll
import Submission.Work.Spaces.HkSq_terms
import Submission.Work.Spaces.sin_two_rpow
import Submission.Work.FTS.Nonlinear.Pieces.Basic
import Submission.Work.FTS.Nonlinear.Pieces.L12FK_add_ge0
import Submission.Work.FTS.Nonlinear.Pieces.rl1Tools.starPt
import Submission.Work.FTS.Nonlinear.Pieces.rl1Tools.gPt
import Submission.Work.FTS.Nonlinear.Pieces.rl1Tools.FzFacts
import Submission.Work.FTS.Nonlinear.Pieces.rl1Tools.gSlots
import Submission.Work.FTS.Nonlinear.Pieces.rl1Tools.FKgFacts
import Submission.Work.FTS.Nonlinear.Pieces.rl1Tools.Nsplit
import Submission.Work.FTS.Nonlinear.Pieces.rl1Tools.FaSum
import Submission.Work.FTS.Nonlinear.Pieces.rl1Tools.FaSumAE
import Submission.Work.FTS.Nonlinear.Pieces.rl1Tools.Pvec
import Submission.Work.FTS.Nonlinear.Pieces.rl1Tools.PvecMeas
import Submission.Work.FTS.Nonlinear.Pieces.rl1Tools.blockMeas
import Submission.Work.FTS.Nonlinear.Pieces.rl1Pieces.Pgg
import Submission.Work.FTS.Nonlinear.Pieces.rl1Pieces.Pgs
import Submission.Work.FTS.Nonlinear.Pieces.rl1Pieces.Psg
import Submission.Work.FTS.Nonlinear.Pieces.rl1Pieces.Pss

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

theorem Q_nonneg (f : Fn) : 0 ≤ Q f := by
  rw [Q]
  refine MeasureTheory.integral_nonneg_of_ae (Filter.Eventually.of_forall fun z => ?_)
  refine mul_nonneg ?_ (MeasureTheory.integral_nonneg_of_ae
    (Filter.Eventually.of_forall fun θ => sq_nonneg _))
  rw [Work.Spaces.w]
  positivity

/-- `Q` only sees the values a.e. on the open quadrant. -/
theorem Q_congr {f h : Fn}
    (hf : ∀ z, 0 < z →
      ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ), f z θ = h z θ) : Q f = Q h := by
  rw [Q, Q]
  refine MeasureTheory.integral_congr_ae ?_
  filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with z hz
  congr 1
  exact MeasureTheory.integral_congr_ae ((hf z hz).mono fun θ hθ => by simp only [hθ])

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

theorem Fa_nonneg (f : Fn) : ∀ r θ, 0 ≤ |Work.Spaces.K θ * f r θ| :=
  fun r θ => abs_nonneg _

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

theorem rl1Bound {α₂ Ci Ce Cs : ℝ} :
    ∃ K : ℝ, 0 < K ∧ ∀ {α : ℝ} {g Φs Φg : Work.FTS.Galerkin.Fn},
    0 < α → α ≤ 1 → α ≤ α₂ → Work.FTS.Nonlin.N4Norm Ci α₂ →
    Work.FTS.Nonlin.GalClass α g → Work.FTS.Nonlin.StarPkg α Cs Φs →
    Work.FTS.Nonlin.EllPkgG α Ce g Φg →
    |Work.Construction.L12 (Work.Construction.N α (Work.Construction.Ftot α g)
        (fun z θ => Φs z θ + Φg z θ)) 0|
      ≤ K * (α ^ 2 + Real.sqrt α * Work.FTS.Nonlin.Xn α g
          + α ^ (-(3 / 2 : ℝ)) * Work.FTS.Nonlin.Xn α g ^ 2) := by
  obtain ⟨K1, hK1, hP1⟩ := rl1Pieces.Pgg (α₂ := α₂) (Ci := Ci) (Ce := Ce) (Cs := Cs)
  obtain ⟨K2, hK2, hP2⟩ := rl1Pieces.Pgs (α₂ := α₂) (Ci := Ci) (Ce := Ce) (Cs := Cs)
  obtain ⟨K3, hK3, hP3⟩ := rl1Pieces.Psg (α₂ := α₂) (Ci := Ci) (Ce := Ce) (Cs := Cs)
  obtain ⟨K4, hK4, hP4⟩ := rl1Pieces.Pss (α₂ := α₂) (Ci := Ci) (Ce := Ce) (Cs := Cs)
  refine ⟨5 * (K1 + K2 + K3 + K4) + 1, by linarith, ?_⟩
  intro α g Φs Φg hα hα1 hαα₂ hN hgal hs hell
  -- ## the four groups of piece estimates
  have hb1 := hP1 hα hα1 hαα₂ hN hgal hs hell
  have hb2 := hP2 hα hα1 hαα₂ hN hgal hs hell
  have hb3 := hP3 hα hα1 hαα₂ hN hgal hs hell
  have hb4 := hP4 hα hα1 hαα₂ hN hgal hs hell
  have hXn0 : 0 ≤ Work.FTS.Nonlin.Xn α g := Work.Spaces.HkNorm_nonneg α 4 g
  -- ## the pointwise split of `N` into its twenty summands
  have hL12g : ∀ z : ℝ, 0 < z →
      DifferentiableAt ℝ (fun z' => Work.Construction.L12 g z') z :=
    fun z hz => hN.l12diff α ⟨hα, hαα₂⟩ g hgal.reg.1
      (Work.FTS.GalerkinFix.RegQ.regQ_mono hgal.reg (by norm_num)).2.1 z hz
  have hsp := rl1Tools.Nsplit hα hα1 hgal.reg.1 hs.smooth hell.smooth
    (fun z hz => (L12FK_add_ge0 hα hα1 hgal).1 z hz.le)
    (fun z hz => (L12FK_add_ge0 hα hα1 hgal).2 z hz.le) hL12g
  have hsplit : ∀ r θ : ℝ, (r, θ) ∈ Work.Construction.Qd →
      Work.Construction.N α (Work.Construction.Ftot α g)
        (fun z θ => Φs z θ + Φg z θ) r θ
        = ∑ k : Fin 20, rl1Tools.pv α g Φs Φg k r θ := by
    intro r θ hq
    rw [hsp r θ hq]
    simp only [rl1Tools.pv, Fin.sum_univ_succ, Matrix.cons_val_zero, Matrix.cons_val_succ,
      Fin.reduceFinMk]
    ring
  -- ## the `L¹(r⁻¹dr)`-triangle inequality
  have hmeas := rl1Tools.PvecMeas (α := α) (Ce := Ce) (Cs := Cs) hgal hs hell
  have htri := rl1Tools.FaSumAE (N := Work.Construction.N α (Work.Construction.Ftot α g)
      (fun z θ => Φs z θ + Φg z θ)) (p := rl1Tools.pv α g Φs Φg) hsplit hmeas.2.1 hmeas.2.2
  -- ## the twenty per-piece bounds
  have hpiece : ∀ k : Fin 20, Fa (rl1Tools.pv α g Φs Φg k)
      ≤ ENNReal.ofReal (Mv K1 K2 K3 K4 α (Work.FTS.Nonlin.Xn α g) k) := by
    intro k
    fin_cases k <;>
      simp only [rl1Tools.pv, Mv, Fa, Matrix.cons_val_zero, Matrix.cons_val_succ,
        Fin.reduceFinMk] <;>
      first
        | exact hb1.1 | exact hb1.2.1 | exact hb1.2.2.1 | exact hb1.2.2.2.1 | exact hb1.2.2.2.2
        | exact hb2.1 | exact hb2.2.1 | exact hb2.2.2.1 | exact hb2.2.2.2.1 | exact hb2.2.2.2.2
        | exact hb3.1 | exact hb3.2.1 | exact hb3.2.2.1 | exact hb3.2.2.2.1 | exact hb3.2.2.2.2
        | exact hb4.1 | exact hb4.2.1 | exact hb4.2.2.1 | exact hb4.2.2.2.1 | exact hb4.2.2.2.2
  -- ## assembling
  have hMvnn : ∀ k : Fin 20, 0 ≤ Mv K1 K2 K3 K4 α (Work.FTS.Nonlin.Xn α g) k :=
    Mv_nonneg hK1 hK2 hK3 hK4 hα hXn0
  have hbig := Mv_sum_le hK1 hK2 hK3 hK4 hα hα1 hXn0
  have hFa : Fa (Work.Construction.N α (Work.Construction.Ftot α g)
      (fun z θ => Φs z θ + Φg z θ))
      ≤ ENNReal.ofReal ((5 * (K1 + K2 + K3 + K4) + 1)
        * (α ^ 2 + Real.sqrt α * Work.FTS.Nonlin.Xn α g
          + α ^ (-(3 / 2 : ℝ)) * Work.FTS.Nonlin.Xn α g ^ 2)) := by
    refine le_trans htri ?_
    refine le_trans (Finset.sum_le_sum (fun k _ => hpiece k)) ?_
    rw [(ENNReal.ofReal_sum_of_nonneg (fun k _ => hMvnn k)).symm]
    exact ENNReal.ofReal_le_ofReal hbig
  have hglue := ofReal_L12_le (Work.Construction.N α (Work.Construction.Ftot α g)
      (fun z θ => Φs z θ + Φg z θ))
  refine (ENNReal.ofReal_le_ofReal_iff ?_).mp (le_trans hglue hFa)
  refine mul_nonneg (by linarith) ?_
  have ha : (0 : ℝ) ≤ α ^ 2 := by positivity
  have hq : (0 : ℝ) ≤ Real.sqrt α * Work.FTS.Nonlin.Xn α g :=
    mul_nonneg (Real.sqrt_nonneg α) hXn0
  have hr : (0 : ℝ) ≤ α ^ (-(3 / 2 : ℝ)) * Work.FTS.Nonlin.Xn α g ^ 2 :=
    mul_nonneg (Real.rpow_nonneg hα.le _) (sq_nonneg _)
  linarith

end Work.FTS.Nonlinear.Pieces
