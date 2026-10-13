import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
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
import Submission.Work.FTS.Nonlinear.Pieces.rl1Pieces.PggEnvTools
import Submission.Work.FTS.Nonlinear.Pieces.rl1Pieces.Pgs
import Submission.Work.FTS.Nonlinear.Pieces.rl1Pieces.PsgEnv
import Submission.Work.FTS.Nonlinear.Pieces.rl1Pieces.Pss

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.Nonlinear.Pieces.Rl1

noncomputable section

open scoped Real Topology ENNReal
open MeasureTheory Set Filter

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

open Work.FTS.Galerkin (Fn)


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


def env (α X : ℝ) : ℝ := α ^ 2 + Real.sqrt α * X + α ^ (-(3 / 2 : ℝ)) * X ^ 2

def Mv (K1 K2 K3 K4 α X : ℝ) : Fin 20 → ℝ :=
  ![K1 * env α X,
    K2 * α ^ (1 / 2 : ℝ) * X,
    K3 * env α X,
    K4 * α ^ 2,
    K1 * env α X,
    K2 * α ^ (1 / 2 : ℝ) * X,
    K3 * env α X,
    K4 * α ^ 2,
    K1 * env α X,
    K2 * α ^ (1 / 2 : ℝ) * X,
    K3 * env α X,
    K4 * α ^ 2,
    K1 * env α X,
    K2 * α ^ (1 / 2 : ℝ) * X,
    K3 * env α X,
    K4 * α ^ 2,
    K1 * env α X,
    K2 * α ^ (1 / 2 : ℝ) * X,
    K3 * env α X,
    K4 * α ^ 2]

/-- Every entry of `Mv` is nonnegative. -/
theorem Mv_nonneg {K1 K2 K3 K4 α X : ℝ} (h1 : 0 < K1) (h2 : 0 < K2) (h3 : 0 < K3)
    (h4 : 0 < K4) (hα : 0 < α) (hX : 0 ≤ X) : ∀ k : Fin 20, 0 ≤ Mv K1 K2 K3 K4 α X k := by
  have henv : (0 : ℝ) ≤ env α X := by
    rw [env]
    have h1' : (0 : ℝ) ≤ Real.sqrt α * X := mul_nonneg (Real.sqrt_nonneg α) hX
    have h2' : (0 : ℝ) ≤ α ^ (-(3 / 2 : ℝ)) * X ^ 2 :=
      mul_nonneg (Real.rpow_nonneg hα.le _) (sq_nonneg X)
    have h3' : (0 : ℝ) ≤ α ^ 2 := sq_nonneg α
    linarith
  have hq : (0 : ℝ) ≤ α ^ (1 / 2 : ℝ) := Real.rpow_nonneg hα.le _
  have ha : (0 : ℝ) ≤ α ^ 2 := sq_nonneg α
  intro k
  fin_cases k <;>
    simp only [Mv, Matrix.cons_val_zero, Matrix.cons_val_succ, Fin.reduceFinMk] <;>
    first
      | exact mul_nonneg h1.le henv
      | exact mul_nonneg (mul_nonneg h2.le hq) hX
      | exact mul_nonneg h3.le henv
      | exact mul_nonneg h4.le ha

/-- The sum of the twenty constants of `Mv`, evaluated. -/
theorem Mv_sum (K1 K2 K3 K4 α X : ℝ) :
    ∑ k : Fin 20, Mv K1 K2 K3 K4 α X k
      = 5 * K1 * env α X + 5 * K2 * α ^ (1 / 2 : ℝ) * X + 5 * K3 * env α X
        + 5 * K4 * α ^ 2 := by
  simp [Mv, Fin.sum_univ_succ]
  ring

/-- The sum of the twenty constants of `Mv` fits the envelope `env`, with
`K = 5(K₁+K₂+K₃+K₄) + 1`, for `0 < α ≤ 1` and `X ≥ 0`. -/
theorem Mv_sum_le {K1 K2 K3 K4 α X : ℝ} (h1 : 0 < K1) (h2 : 0 < K2) (h3 : 0 < K3)
    (h4 : 0 < K4) (hα : 0 < α) (hα1 : α ≤ 1) (hX : 0 ≤ X) :
    ∑ k : Fin 20, Mv K1 K2 K3 K4 α X k
      ≤ (5 * (K1 + K2 + K3 + K4) + 1) * env α X := by
  rw [Mv_sum, env, Real.sqrt_eq_rpow]
  have hqX : α ^ (1 / 2 : ℝ) * X
      ≤ α ^ 2 + α ^ (1 / 2 : ℝ) * X + α ^ (-(3 / 2 : ℝ)) * X ^ 2 := by
    have h1' : (0 : ℝ) ≤ α ^ 2 := sq_nonneg α
    have h2' : (0 : ℝ) ≤ α ^ (-(3 / 2 : ℝ)) * X ^ 2 :=
      mul_nonneg (Real.rpow_nonneg hα.le _) (sq_nonneg X)
    linarith
  have ha2 : α ^ 2 ≤ α ^ 2 + α ^ (1 / 2 : ℝ) * X + α ^ (-(3 / 2 : ℝ)) * X ^ 2 := by
    have h1' : (0 : ℝ) ≤ α ^ (1 / 2 : ℝ) * X := mul_nonneg (Real.rpow_nonneg hα.le _) hX
    have h2' : (0 : ℝ) ≤ α ^ (-(3 / 2 : ℝ)) * X ^ 2 :=
      mul_nonneg (Real.rpow_nonneg hα.le _) (sq_nonneg X)
    linarith
  have hB0 : (0 : ℝ) ≤ α ^ 2 + α ^ (1 / 2 : ℝ) * X + α ^ (-(3 / 2 : ℝ)) * X ^ 2 := by
    have h1' : (0 : ℝ) ≤ α ^ (1 / 2 : ℝ) * X := mul_nonneg (Real.rpow_nonneg hα.le _) hX
    have h2' : (0 : ℝ) ≤ α ^ (-(3 / 2 : ℝ)) * X ^ 2 :=
      mul_nonneg (Real.rpow_nonneg hα.le _) (sq_nonneg X)
    have h3' : (0 : ℝ) ≤ α ^ 2 := sq_nonneg α
    linarith
  nlinarith [h1, h2, h3, h4, hqX, ha2, hB0]

theorem ggRow1 {α₂ Ci Ce Cs : ℝ} (hN : Work.FTS.Nonlin.N4Norm Ci α₂) :
    ∀ {α : ℝ} {g Φs Φg : Fn},
      Work.FTS.Nonlin.GalClass α g → Work.FTS.Nonlin.StarPkg α Cs Φs →
      Work.FTS.Nonlin.EllPkgG α Ce g Φg → 0 < α → α ≤ 1 → α ≤ α₂ →
      Fa (Work.FTS.Nonlin.N1gg α g Φg)
        ≤ ENNReal.ofReal (120 * Real.sqrt (10 / α) * max Ce 0 * (Work.FTS.Nonlin.Xn α g) ^ 2) := by
  intro α g Φs Φg hgal hs hell hα hα1 hαα₂
  have hreg : Work.FTS.Nonlin.RegQ α 4 g :=
    Work.FTS.GalerkinFix.RegQ.regQ_mono hgal.reg (by norm_num)
  have hsm : Work.FTS.LocData.SmoothQuad g := hreg.1
  have hmem : Work.Spaces.HkMem α 4 g := hreg.2.1
  have hX : 0 ≤ Work.FTS.Nonlin.Xn α g := Work.Spaces.HkNorm_nonneg α 4 g
  obtain ⟨hRop, -, -⟩ := Work.FTS.Nonlinear.Pieces.rl1Tools.gPt hα hα1 hell
  have hpt : ∀ z ∈ Set.Ioi (0:ℝ), ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ),
      |Work.Spaces.K θ * Work.FTS.Nonlin.N1gg α g Φg z θ| ≤
        (60 * Real.sqrt (10 / α) * max Ce 0 * Work.FTS.Nonlin.Xn α g) * |g z θ| := by
    intro z hz
    rw [Work.FTS.Nonlinear.Pieces.rl1Tools.restrict_Iθ_eq_Ioo]
    refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo (fun θ hθ => ?_)
    obtain ⟨hθ0, hθ1⟩ := hθ
    have hR := hRop z hz θ hθ0 hθ1
    have hK : |Work.Spaces.K θ| ≤ 3 := Work.FTS.Nonlinear.Pieces.rl1Pieces.K_abs_le_three θ
    have hc0 : 0 ≤ 10 * Real.sqrt (10 / α) * max Ce 0 * Work.FTS.Nonlin.Xn α g := by
      refine mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (Real.sqrt_nonneg _))
        (le_max_right _ _)) hX
    have habs : |Work.Spaces.K θ * Work.FTS.Nonlin.N1gg α g Φg z θ|
        = 2 * |Work.Construction.Rop α (Work.FTS.Nonlin.PhiTg α g Φg) z θ|
          * |Work.Spaces.K θ| * |g z θ| := by
      simp only [Work.FTS.Nonlin.N1gg]
      rw [show Work.Spaces.K θ * (2 * Work.Construction.Rop α (Work.FTS.Nonlin.PhiTg α g Φg) z θ
            * g z θ)
          = 2 * (Work.Construction.Rop α (Work.FTS.Nonlin.PhiTg α g Φg) z θ
            * Work.Spaces.K θ * g z θ) from by ring]
      rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2)]
      ring
    rw [habs]
    have h1 : |Work.Construction.Rop α (Work.FTS.Nonlin.PhiTg α g Φg) z θ|
        * |Work.Spaces.K θ|
        ≤ (10 * Real.sqrt (10 / α) * max Ce 0 * Work.FTS.Nonlin.Xn α g) * 3 :=
      mul_le_mul hR hK (abs_nonneg _) hc0
    have hstep : 2 * |Work.Construction.Rop α (Work.FTS.Nonlin.PhiTg α g Φg) z θ|
        * |Work.Spaces.K θ| * |g z θ|
        ≤ 2 * (10 * Real.sqrt (10 / α) * max Ce 0 * Work.FTS.Nonlin.Xn α g) * 3 * |g z θ| := by
      calc 2 * |Work.Construction.Rop α (Work.FTS.Nonlin.PhiTg α g Φg) z θ|
            * |Work.Spaces.K θ| * |g z θ|
          = (2 * (|Work.Construction.Rop α (Work.FTS.Nonlin.PhiTg α g Φg) z θ|
              * |Work.Spaces.K θ|)) * |g z θ| := by ring
        _ ≤ (2 * ((10 * Real.sqrt (10 / α) * max Ce 0 * Work.FTS.Nonlin.Xn α g) * 3))
              * |g z θ| := mul_le_mul_of_nonneg_right (by linarith) (abs_nonneg _)
        _ = 2 * (10 * Real.sqrt (10 / α) * max Ce 0 * Work.FTS.Nonlin.Xn α g) * 3
              * |g z θ| := by ring
    refine le_trans hstep (le_of_eq ?_)
    ring
  have hmain := Work.FTS.Nonlinear.Pieces.rl1Pieces.ggRow_single
    (N := Work.FTS.Nonlin.N1gg α g Φg) (B := g)
    (Φ := fun z => ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 g z θ)
    (S := fun z => ∫ θ in Work.Spaces.Iθ, (g z θ) ^ 2)
    (c := 60 * Real.sqrt (10 / α) * max Ce 0 * Work.FTS.Nonlin.Xn α g)
    (by
      refine mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (Real.sqrt_nonneg _))
        (le_max_right _ _)) hX)
    (fun z _ => Work.FTS.Nonlinear.Pieces.rl1Pieces.Phi_nonneg α g z)
    (Work.FTS.Nonlinear.Pieces.rl1Pieces.Phi_int hmem)
    (fun z hz => Work.FTS.Nonlinear.Pieces.rl1Pieces.slot_g_fun hα hsm hmem z hz)
    (fun z _ => le_rfl)
    (fun z hz => Work.FTS.Nonlinear.Pieces.rl1Pieces.aesm_g_slice hsm z hz)
    (fun z hz => Work.FTS.Nonlinear.Pieces.rl1Pieces.slice_sq_int_g hsm hmem z hz)
    hpt
  refine hmain.trans (le_of_eq ?_)
  rw [Work.FTS.Nonlinear.Pieces.rl1Pieces.sqrt_Phi_integral]
  congr 1
  ring

theorem ggRow2 {α₂ Ci Ce Cs : ℝ} (hN : Work.FTS.Nonlin.N4Norm Ci α₂) :
    ∀ {α : ℝ} {g Φs Φg : Fn},
      Work.FTS.Nonlin.GalClass α g → Work.FTS.Nonlin.StarPkg α Cs Φs →
      Work.FTS.Nonlin.EllPkgG α Ce g Φg → 0 < α → α ≤ 1 → α ≤ α₂ →
      Fa (Work.FTS.Nonlin.N2gg α g Φg)
        ≤ ENNReal.ofReal (120 * Real.sqrt (10 / α) * max Ce 0 * (Work.FTS.Nonlin.Xn α g) ^ 2) := by
  intro α g Φs Φg hgal hs hell hα hα1 hαα₂
  have hreg : Work.FTS.Nonlin.RegQ α 4 g :=
    Work.FTS.GalerkinFix.RegQ.regQ_mono hgal.reg (by norm_num)
  have hsm : Work.FTS.LocData.SmoothQuad g := hreg.1
  have hmem : Work.Spaces.HkMem α 4 g := hreg.2.1
  have hX : 0 ≤ Work.FTS.Nonlin.Xn α g := Work.Spaces.HkNorm_nonneg α 4 g
  obtain ⟨-, hUop, -⟩ := Work.FTS.Nonlinear.Pieces.rl1Tools.gPt hα hα1 hell
  have hpt : ∀ z ∈ Set.Ioi (0:ℝ), ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ),
      |Work.Spaces.K θ * Work.FTS.Nonlin.N2gg α g Φg z θ| ≤
        (60 * Real.sqrt (10 / α) * max Ce 0 * Work.FTS.Nonlin.Xn α g)
          * |Work.Spaces.Dth g z θ| := by
    intro z hz
    rw [Work.FTS.Nonlinear.Pieces.rl1Tools.restrict_Iθ_eq_Ioo]
    refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo (fun θ hθ => ?_)
    obtain ⟨hθ0, hθ1⟩ := hθ
    have hU := hUop z hz θ hθ0 hθ1
    have hK : |Work.Spaces.K θ| ≤ 3 := Work.FTS.Nonlinear.Pieces.rl1Pieces.K_abs_le_three θ
    have hspos : 0 < Real.sin (2 * θ) :=
      Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos])
    have hUabs : |Work.Construction.Uop α (Work.FTS.Nonlin.PhiTg α g Φg) z θ|
        ≤ 10 * Real.sqrt (10 / α) * max Ce 0 * Work.FTS.Nonlin.Xn α g * Real.sin (2 * θ) := by
      have h2 : |Work.Construction.Uop α (Work.FTS.Nonlin.PhiTg α g Φg) z θ|
          = |Work.Construction.Uop α (Work.FTS.Nonlin.PhiTg α g Φg) z θ / Work.Construction.s2 θ|
            * |Work.Construction.s2 θ| := by
        rw [← abs_mul, div_mul_cancel₀]
        exact ne_of_gt hspos
      rw [h2]
      have h3 : |Work.Construction.s2 θ| = Real.sin (2 * θ) := by
        rw [Work.Construction.s2_eq, abs_of_nonneg hspos.le]
      rw [h3]
      exact mul_le_mul_of_nonneg_right hU hspos.le
    have hD : |Work.Spaces.pth g z θ| = |Work.Spaces.Dth g z θ| / Real.sin (2 * θ) := by
      rw [Work.Spaces.Dth, abs_mul, abs_of_nonneg hspos.le]
      field_simp
    have hKsin : |Work.Spaces.K θ| / Real.sin (2 * θ) ≤ 3 / Real.sin (2 * θ) := by
      gcongr
    have habs : |Work.Spaces.K θ * Work.FTS.Nonlin.N2gg α g Φg z θ|
        = 2 * |Work.Spaces.K θ| * |Work.Construction.Uop α (Work.FTS.Nonlin.PhiTg α g Φg) z θ|
          * |Work.Spaces.pth g z θ| := by
      rw [show Work.FTS.Nonlin.N2gg α g Φg z θ
          = -2 * Work.Construction.Uop α (Work.FTS.Nonlin.PhiTg α g Φg) z θ
            * Work.Spaces.pth g z θ from rfl]
      simp only [abs_mul, abs_neg, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2)]
      ring
    rw [habs, hD]
    have hstep : 2 * |Work.Spaces.K θ| * |Work.Construction.Uop α (Work.FTS.Nonlin.PhiTg α g Φg) z θ|
          * (|Work.Spaces.Dth g z θ| / Real.sin (2 * θ))
        ≤ 2 * 3 * (10 * Real.sqrt (10 / α) * max Ce 0 * Work.FTS.Nonlin.Xn α g)
          * |Work.Spaces.Dth g z θ| := by
      have hC0 : 0 ≤ 10 * Real.sqrt (10 / α) * max Ce 0 * Work.FTS.Nonlin.Xn α g :=
        mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (Real.sqrt_nonneg _))
          (le_max_right _ _)) hX
      have h1 : |Work.Spaces.K θ| * |Work.Construction.Uop α (Work.FTS.Nonlin.PhiTg α g Φg) z θ|
          ≤ 3 * (10 * Real.sqrt (10 / α) * max Ce 0 * Work.FTS.Nonlin.Xn α g
            * Real.sin (2 * θ)) :=
        mul_le_mul hK hUabs (abs_nonneg _) (by positivity)
      have h2 : |Work.Spaces.K θ| * |Work.Construction.Uop α (Work.FTS.Nonlin.PhiTg α g Φg) z θ|
            / Real.sin (2 * θ)
          ≤ 3 * (10 * Real.sqrt (10 / α) * max Ce 0 * Work.FTS.Nonlin.Xn α g) := by
        rw [div_le_iff₀ hspos]
        calc |Work.Spaces.K θ| * |Work.Construction.Uop α (Work.FTS.Nonlin.PhiTg α g Φg) z θ|
            ≤ 3 * (10 * Real.sqrt (10 / α) * max Ce 0 * Work.FTS.Nonlin.Xn α g
              * Real.sin (2 * θ)) := h1
          _ = 3 * (10 * Real.sqrt (10 / α) * max Ce 0 * Work.FTS.Nonlin.Xn α g)
              * Real.sin (2 * θ) := by ring
      calc 2 * |Work.Spaces.K θ| * |Work.Construction.Uop α (Work.FTS.Nonlin.PhiTg α g Φg) z θ|
              * (|Work.Spaces.Dth g z θ| / Real.sin (2 * θ))
          = 2 * ((|Work.Spaces.K θ| * |Work.Construction.Uop α (Work.FTS.Nonlin.PhiTg α g Φg) z θ|)
              / Real.sin (2 * θ)) * |Work.Spaces.Dth g z θ| := by ring
        _ ≤ 2 * (3 * (10 * Real.sqrt (10 / α) * max Ce 0 * Work.FTS.Nonlin.Xn α g))
              * |Work.Spaces.Dth g z θ| :=
            mul_le_mul_of_nonneg_right (by linarith) (abs_nonneg _)
        _ = 2 * 3 * (10 * Real.sqrt (10 / α) * max Ce 0 * Work.FTS.Nonlin.Xn α g)
              * |Work.Spaces.Dth g z θ| := by ring
    refine le_trans hstep (le_of_eq ?_)
    ring
  have hmain := Work.FTS.Nonlinear.Pieces.rl1Pieces.ggRow_single
    (N := Work.FTS.Nonlin.N2gg α g Φg) (B := Work.Spaces.Dth g)
    (Φ := fun z => ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 g z θ)
    (S := fun z => ∫ θ in Work.Spaces.Iθ, (Work.Spaces.Dth g z θ) ^ 2)
    (c := 60 * Real.sqrt (10 / α) * max Ce 0 * Work.FTS.Nonlin.Xn α g)
    (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (Real.sqrt_nonneg _))
      (le_max_right _ _)) hX)
    (fun z _ => Work.FTS.Nonlinear.Pieces.rl1Pieces.Phi_nonneg α g z)
    (Work.FTS.Nonlinear.Pieces.rl1Pieces.Phi_int hmem)
    (fun z hz => Work.FTS.Nonlinear.Pieces.rl1Pieces.slot_Dth_fun hα hsm hmem z hz)
    (fun z _ => le_rfl)
    (fun z hz => Work.FTS.Nonlinear.Pieces.rl1Pieces.aesm_Dth_slice hsm z hz)
    (fun z hz => Work.FTS.Nonlinear.Pieces.rl1Pieces.slice_sq_int_Dth hα hsm hmem z hz)
    hpt
  refine hmain.trans (le_of_eq ?_)
  rw [Work.FTS.Nonlinear.Pieces.rl1Pieces.sqrt_Phi_integral]
  congr 1
  ring

theorem ggRow3 {α₂ Ci Ce Cs : ℝ} (hN : Work.FTS.Nonlin.N4Norm Ci α₂) :
    ∀ {α : ℝ} {g Φs Φg : Fn},
      Work.FTS.Nonlin.GalClass α g → Work.FTS.Nonlin.StarPkg α Cs Φs →
      Work.FTS.Nonlin.EllPkgG α Ce g Φg → 0 < α → α ≤ 1 → α ≤ α₂ →
      Fa (Work.FTS.Nonlin.N3gg α g Φg)
        ≤ ENNReal.ofReal (120 * α * Real.sqrt (10 / α) * max Ce 0
            * (Work.FTS.Nonlin.Xn α g) ^ 2) := by
  intro α g Φs Φg hgal hs hell hα hα1 hαα₂
  have hreg : Work.FTS.Nonlin.RegQ α 4 g :=
    Work.FTS.GalerkinFix.RegQ.regQ_mono hgal.reg (by norm_num)
  have hsm : Work.FTS.LocData.SmoothQuad g := hreg.1
  have hmem : Work.Spaces.HkMem α 4 g := hreg.2.1
  have hX : 0 ≤ Work.FTS.Nonlin.Xn α g := Work.Spaces.HkNorm_nonneg α 4 g
  obtain ⟨-, -, hVop⟩ := Work.FTS.Nonlinear.Pieces.rl1Tools.gPt hα hα1 hell
  have hpt : ∀ z ∈ Set.Ioi (0:ℝ), ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ),
      |Work.Spaces.K θ * Work.FTS.Nonlin.N3gg α g Φg z θ| ≤
        (60 * α * Real.sqrt (10 / α) * max Ce 0 * Work.FTS.Nonlin.Xn α g)
          * |Work.Spaces.Dz g z θ| := by
    intro z hz
    rw [Work.FTS.Nonlinear.Pieces.rl1Tools.restrict_Iθ_eq_Ioo]
    refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo (fun θ hθ => ?_)
    obtain ⟨hθ0, hθ1⟩ := hθ
    have hV := hVop z hz θ hθ0 hθ1
    have hK : |Work.Spaces.K θ| ≤ 3 := Work.FTS.Nonlinear.Pieces.rl1Pieces.K_abs_le_three θ
    have hC0 : 0 ≤ 10 * Real.sqrt (10 / α) * max Ce 0 * Work.FTS.Nonlin.Xn α g :=
      mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (Real.sqrt_nonneg _))
        (le_max_right _ _)) hX
    have habs : |Work.Spaces.K θ * Work.FTS.Nonlin.N3gg α g Φg z θ|
        = 2 * α * |Work.Spaces.K θ|
          * |Work.Construction.Vop (Work.FTS.Nonlin.PhiTg α g Φg) z θ|
          * |Work.Spaces.Dz g z θ| := by
      rw [show Work.FTS.Nonlin.N3gg α g Φg z θ
          = -2 * α * Work.Construction.Vop (Work.FTS.Nonlin.PhiTg α g Φg) z θ
            * Work.Spaces.Dz g z θ from rfl]
      simp only [abs_mul, abs_neg, abs_of_nonneg hα.le, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2)]
      ring
    rw [habs]
    have h1 : |Work.Spaces.K θ| * |Work.Construction.Vop (Work.FTS.Nonlin.PhiTg α g Φg) z θ|
        ≤ 3 * (10 * Real.sqrt (10 / α) * max Ce 0 * Work.FTS.Nonlin.Xn α g) :=
      mul_le_mul hK hV (abs_nonneg _) (by positivity)
    have hstep : 2 * α * |Work.Spaces.K θ|
            * |Work.Construction.Vop (Work.FTS.Nonlin.PhiTg α g Φg) z θ|
            * |Work.Spaces.Dz g z θ|
        ≤ 60 * α * Real.sqrt (10 / α) * max Ce 0 * Work.FTS.Nonlin.Xn α g
            * |Work.Spaces.Dz g z θ| := by
      calc 2 * α * |Work.Spaces.K θ| * |Work.Construction.Vop (Work.FTS.Nonlin.PhiTg α g Φg) z θ|
              * |Work.Spaces.Dz g z θ|
          = (2 * α) * (|Work.Spaces.K θ|
              * |Work.Construction.Vop (Work.FTS.Nonlin.PhiTg α g Φg) z θ|)
              * |Work.Spaces.Dz g z θ| := by ring
        _ ≤ (2 * α) * (3 * (10 * Real.sqrt (10 / α) * max Ce 0 * Work.FTS.Nonlin.Xn α g))
              * |Work.Spaces.Dz g z θ| :=
            mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left h1 (by positivity)) (abs_nonneg _)
        _ = 60 * α * Real.sqrt (10 / α) * max Ce 0 * Work.FTS.Nonlin.Xn α g
              * |Work.Spaces.Dz g z θ| := by ring
    exact le_trans hstep (le_of_eq (by ring))
  have hmain := Work.FTS.Nonlinear.Pieces.rl1Pieces.ggRow_single
    (N := Work.FTS.Nonlin.N3gg α g Φg) (B := Work.Spaces.Dz g)
    (Φ := fun z => ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 g z θ)
    (S := fun z => ∫ θ in Work.Spaces.Iθ, (Work.Spaces.Dz g z θ) ^ 2)
    (c := 60 * α * Real.sqrt (10 / α) * max Ce 0 * Work.FTS.Nonlin.Xn α g)
    (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hα.le) (Real.sqrt_nonneg _))
      (le_max_right _ _)) hX)
    (fun z _ => Work.FTS.Nonlinear.Pieces.rl1Pieces.Phi_nonneg α g z)
    (Work.FTS.Nonlinear.Pieces.rl1Pieces.Phi_int hmem)
    (fun z hz => Work.FTS.Nonlinear.Pieces.rl1Pieces.slot_Dz_fun hsm hmem z hz)
    (fun z _ => le_rfl)
    (fun z hz => Work.FTS.Nonlinear.Pieces.rl1Pieces.aesm_Dz_slice hsm z hz)
    (fun z hz => Work.FTS.Nonlinear.Pieces.rl1Pieces.slice_sq_int_Dz hsm hmem z hz)
    hpt
  refine hmain.trans (le_of_eq ?_)
  rw [Work.FTS.Nonlinear.Pieces.rl1Pieces.sqrt_Phi_integral]
  congr 1
  ring

private theorem hkSq_nonneg'' (α : ℝ) (k : ℕ) (f : ℝ → ℝ → ℝ) : 0 ≤ Work.Spaces.HkSq α k f := by
  rw [Work.Spaces.HkSq]
  exact MeasureTheory.integral_nonneg fun z =>
    MeasureTheory.integral_nonneg fun θ => Work.Spaces.HkIntegrand_nonneg α k f z θ

/-- `w z · FK(g)(z)² ≤ (9π/2) · ∫_θ HkIntegrand`. -/
private theorem fkSlot {α : ℝ} {g : ℝ → ℝ → ℝ} (hα : 0 < α)
    (hsm : Work.FTS.LocData.SmoothQuad g) (hmem : Work.Spaces.HkMem α 4 g) :
    ∀ z, 0 < z → Work.Spaces.w z * (Work.Construction.FK g z) ^ 2
      ≤ (9 * Real.pi / 2) * ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 g z θ := by
  intro z hz
  have h1 := Work.FTS.Nonlinear.Pieces.rl1Pieces.fk_pointwise_le hsm hmem z hz
  have hg0 : 0 ≤ ∫ θ in Work.Spaces.Iθ, (g z θ) ^ 2 :=
    MeasureTheory.integral_nonneg fun θ => sq_nonneg _
  have hc : (0:ℝ) ≤ 3 * Real.sqrt (Real.pi / 2) := by positivity
  have hs : (0:ℝ) ≤ Real.sqrt (∫ θ in Work.Spaces.Iθ, (g z θ) ^ 2) := Real.sqrt_nonneg _
  have h6 : (Work.Construction.FK g z) ^ 2
      ≤ (3 * Real.sqrt (Real.pi / 2)
          * Real.sqrt (∫ θ in Work.Spaces.Iθ, (g z θ) ^ 2)) ^ 2 := by
    have h := mul_self_le_mul_self (abs_nonneg (Work.Construction.FK g z)) h1
    nlinarith [h, sq_abs (Work.Construction.FK g z)]
  have hpw : (Work.Construction.FK g z) ^ 2
      ≤ (9 * Real.pi / 2) * (∫ θ in Work.Spaces.Iθ, (g z θ) ^ 2) := by
    rw [mul_pow, Real.sq_sqrt hg0] at h6
    have h3 : (3 * Real.sqrt (Real.pi / 2)) ^ 2 = 9 * Real.pi / 2 := by
      have h : (Real.sqrt (Real.pi / 2)) ^ 2 = Real.pi / 2 := Real.sq_sqrt (by positivity)
      nlinarith [h]
    rwa [h3] at h6
  have hw0 : 0 ≤ Work.Spaces.w z := Work.FTS.Nonlinear.Pieces.rl1Tools.w_nonneg z
  calc Work.Spaces.w z * (Work.Construction.FK g z) ^ 2
      ≤ Work.Spaces.w z * ((9 * Real.pi / 2)
          * (∫ θ in Work.Spaces.Iθ, (g z θ) ^ 2)) := mul_le_mul_of_nonneg_left hpw hw0
    _ = (9 * Real.pi / 2) * (Work.Spaces.w z * ∫ θ in Work.Spaces.Iθ, (g z θ) ^ 2) := by ring
    _ ≤ (9 * Real.pi / 2) * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 g z θ) :=
        mul_le_mul_of_nonneg_left
          (Work.FTS.Nonlinear.Pieces.rl1Pieces.slot_g_fun hα hsm hmem z hz) (by positivity)

/-- `∫⁻_θ |N₄^{gg}| ≤ ofReal(√S₁ · √S₂)` with `S₁ = ∫(D_θg)²`, `S₂ = FK(g)²`. -/
private theorem inner4 {α : ℝ} {g : ℝ → ℝ → ℝ} (hα : 0 < α)
    (hsm : Work.FTS.LocData.SmoothQuad g) (hmem : Work.Spaces.HkMem α 4 g) :
    ∀ z ∈ Set.Ioi (0:ℝ),
      (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal |Work.FTS.Nonlin.N4gg α g z θ|)
        ≤ ENNReal.ofReal (Real.sqrt (∫ θ in Work.Spaces.Iθ, (Work.Spaces.Dth g z θ) ^ 2)
            * Real.sqrt ((Work.Construction.FK g z) ^ 2)) := by
  intro z hz
  have hD := Work.FTS.Nonlinear.Pieces.rl1Pieces.inner_abs_lintegral_le
    (Work.FTS.Nonlinear.Pieces.rl1Pieces.aesm_Dth_slice hsm z hz)
    (Work.FTS.Nonlinear.Pieces.rl1Pieces.slice_sq_int_Dth hα hsm hmem z hz)
  have hc0 : (0:ℝ) ≤ (1/2) * |Work.Construction.FK g z| := by positivity
  have hfun : (fun θ => ENNReal.ofReal |Work.FTS.Nonlin.N4gg α g z θ|)
      = fun θ => ENNReal.ofReal ((1/2) * |Work.Construction.FK g z|)
          * ENNReal.ofReal |Work.Spaces.Dth g z θ| := by
    funext θ
    rw [show |Work.FTS.Nonlin.N4gg α g z θ|
        = (1/2) * |Work.Construction.FK g z| * |Work.Spaces.Dth g z θ| from by
      rw [show Work.FTS.Nonlin.N4gg α g z θ
          = -(1/2) * Work.Construction.FK g z * Work.Spaces.Dth g z θ from rfl]
      simp only [abs_mul, abs_neg, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 1/2)]
      try ring]
    exact ENNReal.ofReal_mul hc0
  rw [hfun, MeasureTheory.lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  calc ENNReal.ofReal ((1/2) * |Work.Construction.FK g z|)
        * (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal |Work.Spaces.Dth g z θ|)
      ≤ ENNReal.ofReal ((1/2) * |Work.Construction.FK g z|)
        * ENNReal.ofReal (2 * Real.sqrt (∫ θ in Work.Spaces.Iθ,
            (Work.Spaces.Dth g z θ) ^ 2)) := mul_le_mul_right hD _
    _ = ENNReal.ofReal ((1/2) * |Work.Construction.FK g z|
        * (2 * Real.sqrt (∫ θ in Work.Spaces.Iθ, (Work.Spaces.Dth g z θ) ^ 2))) :=
        (ENNReal.ofReal_mul hc0).symm
    _ = ENNReal.ofReal (Real.sqrt (∫ θ in Work.Spaces.Iθ, (Work.Spaces.Dth g z θ) ^ 2)
        * Real.sqrt ((Work.Construction.FK g z) ^ 2)) := by
        congr 1
        rw [Real.sqrt_sq_eq_abs]
        ring_nf

/-- `∫⁻_θ |N₅^{gg}| ≤ ofReal(√S₁ · √S₂)` with `S₁ = ∫g²`, `S₂ = FK(g)²`. -/
private theorem inner5 {α : ℝ} {g : ℝ → ℝ → ℝ}
    (hsm : Work.FTS.LocData.SmoothQuad g) (hmem : Work.Spaces.HkMem α 4 g) :
    ∀ z ∈ Set.Ioi (0:ℝ),
      (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal |Work.FTS.Nonlin.N5gg g z θ|)
        ≤ ENNReal.ofReal (2 * (Real.sqrt (∫ θ in Work.Spaces.Iθ, (g z θ) ^ 2)
            * Real.sqrt ((Work.Construction.FK g z) ^ 2))) := by
  intro z hz
  have hg := Work.FTS.Nonlinear.Pieces.rl1Pieces.inner_abs_lintegral_le
    (Work.FTS.Nonlinear.Pieces.rl1Pieces.aesm_g_slice hsm z hz)
    (Work.FTS.Nonlinear.Pieces.rl1Pieces.slice_sq_int_g hsm hmem z hz)
  have hfun : (fun θ => ENNReal.ofReal |Work.FTS.Nonlin.N5gg g z θ|)
      = fun θ => ENNReal.ofReal |Work.Construction.FK g z|
          * ENNReal.ofReal (Real.sin θ ^ 2 * |g z θ|) := by
    funext θ
    rw [show |Work.FTS.Nonlin.N5gg g z θ|
        = |Work.Construction.FK g z| * (Real.sin θ ^ 2 * |g z θ|) from by
      rw [show Work.FTS.Nonlin.N5gg g z θ
          = -Real.sin θ ^ 2 * Work.Construction.FK g z * g z θ from rfl]
      simp only [abs_mul, abs_neg, abs_of_nonneg (sq_nonneg (Real.sin θ))]
      ring]
    exact ENNReal.ofReal_mul (abs_nonneg _)
  rw [hfun, MeasureTheory.lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  have hle : (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal (Real.sin θ ^ 2 * |g z θ|))
      ≤ ∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal |g z θ| := by
    refine MeasureTheory.lintegral_mono_ae (Eventually.of_forall fun θ => ?_)
    refine ENNReal.ofReal_le_ofReal ?_
    have hs2 : Real.sin θ ^ 2 ≤ 1 := by nlinarith [Real.sin_le_one θ, Real.neg_one_le_sin θ]
    nlinarith [abs_nonneg (g z θ)]
  calc ENNReal.ofReal |Work.Construction.FK g z|
        * (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal (Real.sin θ ^ 2 * |g z θ|))
      ≤ ENNReal.ofReal |Work.Construction.FK g z|
        * (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal |g z θ|) := mul_le_mul_right hle _
    _ ≤ ENNReal.ofReal |Work.Construction.FK g z|
        * ENNReal.ofReal (2 * Real.sqrt (∫ θ in Work.Spaces.Iθ, (g z θ) ^ 2)) :=
        mul_le_mul_right hg _
    _ = ENNReal.ofReal (2 * (Real.sqrt (∫ θ in Work.Spaces.Iθ, (g z θ) ^ 2)
        * Real.sqrt ((Work.Construction.FK g z) ^ 2))) := by
        rw [← ENNReal.ofReal_mul (abs_nonneg (Work.Construction.FK g z))]
        congr 1
        rw [Real.sqrt_sq_eq_abs]
        ring

/-- The `N₄^{gg}`-row. -/
theorem ggRow4'' {α₂ Ci Ce Cs : ℝ} (hN : Work.FTS.Nonlin.N4Norm Ci α₂) :
    ∀ {α : ℝ} {g Φs Φg : Fn},
      Work.FTS.Nonlin.GalClass α g → Work.FTS.Nonlin.StarPkg α Cs Φs →
      Work.FTS.Nonlin.EllPkgG α Ce g Φg → 0 < α → α ≤ 1 → α ≤ α₂ →
      Fa (Work.FTS.Nonlin.N4gg α g)
        ≤ ENNReal.ofReal ((27 * Real.pi / 8) * (Work.FTS.Nonlin.Xn α g) ^ 2) := by
  intro α g Φs Φg hgal hs hell hα hα1 hαα₂
  have hreg : Work.FTS.Nonlin.RegQ α 4 g :=
    Work.FTS.GalerkinFix.RegQ.regQ_mono hgal.reg (by norm_num)
  have hsm : Work.FTS.LocData.SmoothQuad g := hreg.1
  have hmem : Work.Spaces.HkMem α 4 g := hreg.2.1
  have hΦ0int : MeasureTheory.IntegrableOn
      (fun z => ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 g z θ) (Set.Ioi (0:ℝ)) :=
    Work.FTS.Nonlinear.Pieces.rl1Pieces.Phi_int hmem
  have hΦ0nn : ∀ z : ℝ, 0 ≤ ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 g z θ :=
    fun z => Work.FTS.Nonlinear.Pieces.rl1Pieces.Phi_nonneg α g z
  have hbig : (1:ℝ) ≤ 9 * Real.pi / 2 := by linarith [Real.pi_gt_three]
  have hslot1 : ∀ z, 0 < z → Work.Spaces.w z
      * (∫ θ in Work.Spaces.Iθ, (Work.Spaces.Dth g z θ) ^ 2)
      ≤ (9 * Real.pi / 2) * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 g z θ) := by
    intro z hz
    have h := Work.FTS.Nonlinear.Pieces.rl1Pieces.slot_Dth_fun hα hsm hmem z hz
    nlinarith [h, hΦ0nn z, hbig]
  have hinner : ∀ z ∈ Set.Ioi (0:ℝ),
      (∫⁻ θ in Work.Spaces.Iθ,
          ENNReal.ofReal |Work.Spaces.K θ * Work.FTS.Nonlin.N4gg α g z θ|)
        ≤ ENNReal.ofReal (3 * (Real.sqrt (∫ θ in Work.Spaces.Iθ, (Work.Spaces.Dth g z θ) ^ 2)
            * Real.sqrt ((Work.Construction.FK g z) ^ 2))) := by
    intro z hz
    have hN := inner4 hα hsm hmem z hz
    have h1 : (∫⁻ θ in Work.Spaces.Iθ,
          ENNReal.ofReal |Work.Spaces.K θ * Work.FTS.Nonlin.N4gg α g z θ|)
        ≤ ∫⁻ θ in Work.Spaces.Iθ,
            ENNReal.ofReal (3 * |Work.FTS.Nonlin.N4gg α g z θ|) := by
      refine MeasureTheory.lintegral_mono_ae (Eventually.of_forall fun θ => ?_)
      refine ENNReal.ofReal_le_ofReal ?_
      rw [abs_mul]
      nlinarith [Work.FTS.Nonlinear.Pieces.rl1Pieces.K_abs_le_three θ,
        abs_nonneg (Work.FTS.Nonlin.N4gg α g z θ), abs_nonneg (Work.Spaces.K θ)]
    have h2 : (∫⁻ θ in Work.Spaces.Iθ,
          ENNReal.ofReal (3 * |Work.FTS.Nonlin.N4gg α g z θ|))
        = ENNReal.ofReal 3 * (∫⁻ θ in Work.Spaces.Iθ,
            ENNReal.ofReal |Work.FTS.Nonlin.N4gg α g z θ|) := by
      rw [show (fun θ => ENNReal.ofReal (3 * |Work.FTS.Nonlin.N4gg α g z θ|))
          = fun θ => ENNReal.ofReal 3 * ENNReal.ofReal |Work.FTS.Nonlin.N4gg α g z θ| from by
        funext θ; exact ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 3)]
      rw [MeasureTheory.lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    calc (∫⁻ θ in Work.Spaces.Iθ,
          ENNReal.ofReal |Work.Spaces.K θ * Work.FTS.Nonlin.N4gg α g z θ|)
        ≤ ∫⁻ θ in Work.Spaces.Iθ,
            ENNReal.ofReal (3 * |Work.FTS.Nonlin.N4gg α g z θ|) := h1
      _ = ENNReal.ofReal 3 * (∫⁻ θ in Work.Spaces.Iθ,
            ENNReal.ofReal |Work.FTS.Nonlin.N4gg α g z θ|) := h2
      _ ≤ ENNReal.ofReal 3 * ENNReal.ofReal (Real.sqrt (∫ θ in Work.Spaces.Iθ,
            (Work.Spaces.Dth g z θ) ^ 2) * Real.sqrt ((Work.Construction.FK g z) ^ 2)) :=
          mul_le_mul_right hN _
      _ = ENNReal.ofReal (3 * (Real.sqrt (∫ θ in Work.Spaces.Iθ, (Work.Spaces.Dth g z θ) ^ 2)
            * Real.sqrt ((Work.Construction.FK g z) ^ 2))) :=
          (ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 3)).symm
  have hmain := Work.FTS.Nonlinear.Pieces.rl1Pieces.ggRow_prod
      (N := fun z θ => Work.Spaces.K θ * Work.FTS.Nonlin.N4gg α g z θ)
      (Φ := fun z => (9 * Real.pi / 2) * ∫ θ in Work.Spaces.Iθ,
        Work.Spaces.HkIntegrand α 4 g z θ)
      (S₁ := fun z => ∫ θ in Work.Spaces.Iθ, (Work.Spaces.Dth g z θ) ^ 2)
      (S₂ := fun z => (Work.Construction.FK g z) ^ 2)
      (c := 3) (by norm_num)
      (fun z _ => mul_nonneg (by positivity) (hΦ0nn z))
      (hΦ0int.const_mul _) hslot1 (fkSlot hα hsm hmem) hinner
  show (∫⁻ z in Set.Ioi (0:ℝ), ENNReal.ofReal z⁻¹ * (∫⁻ θ in Work.Spaces.Iθ,
      ENNReal.ofReal |Work.Spaces.K θ * Work.FTS.Nonlin.N4gg α g z θ|)) ≤
      ENNReal.ofReal ((27 * Real.pi / 8) * (Work.FTS.Nonlin.Xn α g) ^ 2)
  refine hmain.trans ?_
  refine ENNReal.ofReal_le_ofReal ?_
  have hSq : Work.Spaces.HkSq α 4 g = (Work.FTS.Nonlin.Xn α g) ^ 2 := by
    rw [show Work.FTS.Nonlin.Xn α g = Work.Spaces.HkNorm α 4 g from rfl, Work.Spaces.HkNorm,
      Real.sq_sqrt (hkSq_nonneg'' α 4 g)]
  rw [MeasureTheory.integral_const_mul,
    Work.FTS.Nonlinear.Pieces.rl1Pieces.Phi_integral, hSq]
  linarith [le_refl (Real.pi * (Work.FTS.Nonlin.Xn α g) ^ 2 * (27 / 8))]

/-- The `N₅^{gg}`-row. -/
theorem ggRow5'' {α₂ Ci Ce Cs : ℝ} (hN : Work.FTS.Nonlin.N4Norm Ci α₂) :
    ∀ {α : ℝ} {g Φs Φg : Fn},
      Work.FTS.Nonlin.GalClass α g → Work.FTS.Nonlin.StarPkg α Cs Φs →
      Work.FTS.Nonlin.EllPkgG α Ce g Φg → 0 < α → α ≤ 1 → α ≤ α₂ →
      Fa (Work.FTS.Nonlin.N5gg g)
        ≤ ENNReal.ofReal ((27 * Real.pi / 4) * (Work.FTS.Nonlin.Xn α g) ^ 2) := by
  intro α g Φs Φg hgal hs hell hα hα1 hαα₂
  have hreg : Work.FTS.Nonlin.RegQ α 4 g :=
    Work.FTS.GalerkinFix.RegQ.regQ_mono hgal.reg (by norm_num)
  have hsm : Work.FTS.LocData.SmoothQuad g := hreg.1
  have hmem : Work.Spaces.HkMem α 4 g := hreg.2.1
  have hΦ0int : MeasureTheory.IntegrableOn
      (fun z => ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 g z θ) (Set.Ioi (0:ℝ)) :=
    Work.FTS.Nonlinear.Pieces.rl1Pieces.Phi_int hmem
  have hΦ0nn : ∀ z : ℝ, 0 ≤ ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 g z θ :=
    fun z => Work.FTS.Nonlinear.Pieces.rl1Pieces.Phi_nonneg α g z
  have hbig : (1:ℝ) ≤ 9 * Real.pi / 2 := by linarith [Real.pi_gt_three]
  have hslot1 : ∀ z, 0 < z → Work.Spaces.w z
      * (∫ θ in Work.Spaces.Iθ, (g z θ) ^ 2)
      ≤ (9 * Real.pi / 2) * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 g z θ) := by
    intro z hz
    have h := Work.FTS.Nonlinear.Pieces.rl1Pieces.slot_g_fun hα hsm hmem z hz
    nlinarith [h, hΦ0nn z, hbig]
  have hinner : ∀ z ∈ Set.Ioi (0:ℝ),
      (∫⁻ θ in Work.Spaces.Iθ,
          ENNReal.ofReal |Work.Spaces.K θ * Work.FTS.Nonlin.N5gg g z θ|)
        ≤ ENNReal.ofReal (6 * (Real.sqrt (∫ θ in Work.Spaces.Iθ, (g z θ) ^ 2)
            * Real.sqrt ((Work.Construction.FK g z) ^ 2))) := by
    intro z hz
    have hN := inner5 hsm hmem z hz
    have h1 : (∫⁻ θ in Work.Spaces.Iθ,
          ENNReal.ofReal |Work.Spaces.K θ * Work.FTS.Nonlin.N5gg g z θ|)
        ≤ ∫⁻ θ in Work.Spaces.Iθ,
            ENNReal.ofReal (3 * |Work.FTS.Nonlin.N5gg g z θ|) := by
      refine MeasureTheory.lintegral_mono_ae (Eventually.of_forall fun θ => ?_)
      refine ENNReal.ofReal_le_ofReal ?_
      rw [abs_mul]
      nlinarith [Work.FTS.Nonlinear.Pieces.rl1Pieces.K_abs_le_three θ,
        abs_nonneg (Work.FTS.Nonlin.N5gg g z θ), abs_nonneg (Work.Spaces.K θ)]
    have h2 : (∫⁻ θ in Work.Spaces.Iθ,
          ENNReal.ofReal (3 * |Work.FTS.Nonlin.N5gg g z θ|))
        = ENNReal.ofReal 3 * (∫⁻ θ in Work.Spaces.Iθ,
            ENNReal.ofReal |Work.FTS.Nonlin.N5gg g z θ|) := by
      rw [show (fun θ => ENNReal.ofReal (3 * |Work.FTS.Nonlin.N5gg g z θ|))
          = fun θ => ENNReal.ofReal 3 * ENNReal.ofReal |Work.FTS.Nonlin.N5gg g z θ| from by
        funext θ; exact ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 3)]
      rw [MeasureTheory.lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    calc (∫⁻ θ in Work.Spaces.Iθ,
          ENNReal.ofReal |Work.Spaces.K θ * Work.FTS.Nonlin.N5gg g z θ|)
        ≤ ∫⁻ θ in Work.Spaces.Iθ,
            ENNReal.ofReal (3 * |Work.FTS.Nonlin.N5gg g z θ|) := h1
      _ = ENNReal.ofReal 3 * (∫⁻ θ in Work.Spaces.Iθ,
            ENNReal.ofReal |Work.FTS.Nonlin.N5gg g z θ|) := h2
      _ ≤ ENNReal.ofReal 3 * ENNReal.ofReal (2 * (Real.sqrt (∫ θ in Work.Spaces.Iθ, (g z θ) ^ 2)
            * Real.sqrt ((Work.Construction.FK g z) ^ 2))) := mul_le_mul_right hN _
      _ = ENNReal.ofReal (6 * (Real.sqrt (∫ θ in Work.Spaces.Iθ, (g z θ) ^ 2)
            * Real.sqrt ((Work.Construction.FK g z) ^ 2))) := by
          rw [← ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 3)]
          congr 1
          ring
  have hmain := Work.FTS.Nonlinear.Pieces.rl1Pieces.ggRow_prod
      (N := fun z θ => Work.Spaces.K θ * Work.FTS.Nonlin.N5gg g z θ)
      (Φ := fun z => (9 * Real.pi / 2) * ∫ θ in Work.Spaces.Iθ,
        Work.Spaces.HkIntegrand α 4 g z θ)
      (S₁ := fun z => ∫ θ in Work.Spaces.Iθ, (g z θ) ^ 2)
      (S₂ := fun z => (Work.Construction.FK g z) ^ 2)
      (c := 6) (by norm_num)
      (fun z _ => mul_nonneg (by positivity) (hΦ0nn z))
      (hΦ0int.const_mul _) hslot1 (fkSlot hα hsm hmem) hinner
  show (∫⁻ z in Set.Ioi (0:ℝ), ENNReal.ofReal z⁻¹ * (∫⁻ θ in Work.Spaces.Iθ,
      ENNReal.ofReal |Work.Spaces.K θ * Work.FTS.Nonlin.N5gg g z θ|)) ≤
      ENNReal.ofReal ((27 * Real.pi / 4) * (Work.FTS.Nonlin.Xn α g) ^ 2)
  refine hmain.trans ?_
  refine ENNReal.ofReal_le_ofReal ?_
  have hSq : Work.Spaces.HkSq α 4 g = (Work.FTS.Nonlin.Xn α g) ^ 2 := by
    rw [show Work.FTS.Nonlin.Xn α g = Work.Spaces.HkNorm α 4 g from rfl, Work.Spaces.HkNorm,
      Real.sq_sqrt (hkSq_nonneg'' α 4 g)]
  rw [MeasureTheory.integral_const_mul,
    Work.FTS.Nonlinear.Pieces.rl1Pieces.Phi_integral, hSq]
  linarith [le_refl (Real.pi * (Work.FTS.Nonlin.Xn α g) ^ 2 * (27 / 8))]

/-! ## The five `gg`-rows in the envelope form -/

private theorem env_nonneg {α X : ℝ} (hα : 0 < α) (hX : 0 ≤ X) :
    0 ≤ env α X := by
  rw [env]
  have h1 : 0 ≤ α ^ 2 := sq_nonneg _
  have h2 : 0 ≤ Real.sqrt α * X := mul_nonneg (Real.sqrt_nonneg _) hX
  have h3 : 0 ≤ α ^ (-(3 / 2 : ℝ)) * X ^ 2 :=
    mul_nonneg (Real.rpow_nonneg hα.le _) (sq_nonneg _)
  linarith

private theorem sqrt_div_eq {α : ℝ} (hα : 0 < α) :
    Real.sqrt (10 / α) = Real.sqrt 10 * α ^ (-(1 / 2 : ℝ)) := by
  rw [Real.sqrt_eq_rpow, Real.div_rpow (by norm_num : (0:ℝ) ≤ 10) hα.le,
    ← Real.sqrt_eq_rpow, Real.rpow_neg hα.le, ← Real.sqrt_eq_rpow, div_eq_mul_inv]

private theorem env_ge_rpow {α X : ℝ} (hα : 0 < α) (hX : 0 ≤ X) :
    α ^ (-(3 / 2 : ℝ)) * X ^ 2 ≤ env α X := by
  rw [env]
  have h1 : 0 ≤ α ^ 2 := sq_nonneg _
  have h2 : 0 ≤ Real.sqrt α * X := mul_nonneg (Real.sqrt_nonneg _) hX
  linarith

/-- The five `gg`-rows of `N` in the a-priori envelope `K·(α² + √αX + α^{-3/2}X²)`,
`X = Xn α g`. -/
theorem ggEnv {α₂ Ci Ce Cs : ℝ} :
    ∃ K : ℝ, 0 < K ∧ ∀ {α : ℝ} {g Φs Φg : Fn},
      0 < α → α ≤ 1 → α ≤ α₂ → Work.FTS.Nonlin.N4Norm Ci α₂ →
      Work.FTS.Nonlin.GalClass α g → Work.FTS.Nonlin.StarPkg α Cs Φs →
      Work.FTS.Nonlin.EllPkgG α Ce g Φg →
      Fa (Work.FTS.Nonlin.N1gg α g Φg)
          ≤ ENNReal.ofReal (K * env α (Work.FTS.Nonlin.Xn α g)) ∧
      Fa (Work.FTS.Nonlin.N2gg α g Φg)
          ≤ ENNReal.ofReal (K * env α (Work.FTS.Nonlin.Xn α g)) ∧
      Fa (Work.FTS.Nonlin.N3gg α g Φg)
          ≤ ENNReal.ofReal (K * env α (Work.FTS.Nonlin.Xn α g)) ∧
      Fa (Work.FTS.Nonlin.N4gg α g)
          ≤ ENNReal.ofReal (K * env α (Work.FTS.Nonlin.Xn α g)) ∧
      Fa (Work.FTS.Nonlin.N5gg g)
          ≤ ENNReal.ofReal (K * env α (Work.FTS.Nonlin.Xn α g)) := by
  refine ⟨120 * Real.sqrt 10 * max Ce 0 + 27 * Real.pi / 4 + 1, ?_, ?_⟩
  · have h1 : (0:ℝ) ≤ 120 * Real.sqrt 10 * max Ce 0 := by
      have := le_max_right Ce 0
      positivity
    linarith [Real.pi_pos]
  · intro α g Φs Φg hα hα1 hαα₂ hN hgal hs hell
    have hX : 0 ≤ Work.FTS.Nonlin.Xn α g := Work.Spaces.HkNorm_nonneg α 4 g
    have hc0 : 0 ≤ 120 * Real.sqrt 10 * max Ce 0 := by
      have := le_max_right Ce 0
      positivity
    have henvnn := env_nonneg hα hX
    have henv := env_ge_rpow hα hX
    have hs10 := sqrt_div_eq hα
    have h13 : α ^ (-(1 / 2 : ℝ)) ≤ α ^ (-(3 / 2 : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_ge hα hα1 (by norm_num)
    have hh3 : α ^ (1 / 2 : ℝ) ≤ α ^ (-(3 / 2 : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_ge hα hα1 (by norm_num)
    have hone : (1:ℝ) ≤ α ^ (-(3 / 2 : ℝ)) := by
      have h := Real.rpow_le_rpow_of_exponent_ge hα hα1 (show -(3 / 2 : ℝ) ≤ 0 by norm_num)
      rwa [Real.rpow_zero] at h
    have hαr : α * α ^ (-(1 / 2 : ℝ)) = α ^ (1 / 2 : ℝ) := by
      have h2 : α ^ (1 : ℝ) * α ^ (-(1 / 2 : ℝ)) = α ^ ((1:ℝ) + -(1 / 2 : ℝ)) :=
        (Real.rpow_add hα 1 (-(1 / 2 : ℝ))).symm
      rw [Real.rpow_one] at h2
      have h3 : (1:ℝ) + -(1 / 2 : ℝ) = 1 / 2 := by norm_num
      rw [h3] at h2
      exact h2
    have key : ∀ c : ℝ, c ≤ 120 * Real.sqrt 10 * max Ce 0 →
        c * env α (Work.FTS.Nonlin.Xn α g)
          ≤ (120 * Real.sqrt 10 * max Ce 0 + 27 * Real.pi / 4 + 1)
            * env α (Work.FTS.Nonlin.Xn α g) := by
      intro c hc
      refine mul_le_mul_of_nonneg_right ?_ henvnn
      linarith [Real.pi_pos]
    have key2 : (27 * Real.pi / 4) * env α (Work.FTS.Nonlin.Xn α g)
        ≤ (120 * Real.sqrt 10 * max Ce 0 + 27 * Real.pi / 4 + 1)
          * env α (Work.FTS.Nonlin.Xn α g) := by
      have hmax : 0 ≤ 120 * Real.sqrt 10 * max Ce 0 := by
        have := le_max_right Ce 0
        positivity
      exact mul_le_mul_of_nonneg_right (by linarith [Real.pi_pos, hmax]) henvnn
    constructor
    · refine (ggRow1 (α₂ := α₂) (Ci := Ci) (Ce := Ce) (Cs := Cs) hN
        hgal hs hell hα hα1 hαα₂).trans (ENNReal.ofReal_le_ofReal ?_)
      calc 120 * Real.sqrt (10 / α) * max Ce 0 * (Work.FTS.Nonlin.Xn α g) ^ 2
          = 120 * Real.sqrt 10 * max Ce 0
              * (α ^ (-(1 / 2 : ℝ)) * (Work.FTS.Nonlin.Xn α g) ^ 2) := by
            rw [hs10]; ring
        _ ≤ 120 * Real.sqrt 10 * max Ce 0
              * (α ^ (-(3 / 2 : ℝ)) * (Work.FTS.Nonlin.Xn α g) ^ 2) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h13 (sq_nonneg _)) hc0
        _ ≤ 120 * Real.sqrt 10 * max Ce 0 * env α
              (Work.FTS.Nonlin.Xn α g) := mul_le_mul_of_nonneg_left henv hc0
        _ ≤ (120 * Real.sqrt 10 * max Ce 0 + 27 * Real.pi / 4 + 1)
              * env α (Work.FTS.Nonlin.Xn α g) := key _ le_rfl
    constructor
    · refine (ggRow2 (α₂ := α₂) (Ci := Ci) (Ce := Ce) (Cs := Cs) hN
        hgal hs hell hα hα1 hαα₂).trans (ENNReal.ofReal_le_ofReal ?_)
      calc 120 * Real.sqrt (10 / α) * max Ce 0 * (Work.FTS.Nonlin.Xn α g) ^ 2
          = 120 * Real.sqrt 10 * max Ce 0
              * (α ^ (-(1 / 2 : ℝ)) * (Work.FTS.Nonlin.Xn α g) ^ 2) := by
            rw [hs10]; ring
        _ ≤ 120 * Real.sqrt 10 * max Ce 0
              * (α ^ (-(3 / 2 : ℝ)) * (Work.FTS.Nonlin.Xn α g) ^ 2) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h13 (sq_nonneg _)) hc0
        _ ≤ 120 * Real.sqrt 10 * max Ce 0 * env α
              (Work.FTS.Nonlin.Xn α g) := mul_le_mul_of_nonneg_left henv hc0
        _ ≤ (120 * Real.sqrt 10 * max Ce 0 + 27 * Real.pi / 4 + 1)
              * env α (Work.FTS.Nonlin.Xn α g) := key _ le_rfl
    constructor
    · refine (ggRow3 (α₂ := α₂) (Ci := Ci) (Ce := Ce) (Cs := Cs) hN
        hgal hs hell hα hα1 hαα₂).trans (ENNReal.ofReal_le_ofReal ?_)
      calc 120 * α * Real.sqrt (10 / α) * max Ce 0 * (Work.FTS.Nonlin.Xn α g) ^ 2
          = 120 * Real.sqrt 10 * max Ce 0
              * (α ^ (1 / 2 : ℝ) * (Work.FTS.Nonlin.Xn α g) ^ 2) := by
            rw [hs10]
            rw [show 120 * α * (Real.sqrt 10 * α ^ (-(1 / 2 : ℝ))) * max Ce 0
                  * (Work.FTS.Nonlin.Xn α g) ^ 2
                = 120 * Real.sqrt 10 * max Ce 0
                  * ((α * α ^ (-(1 / 2 : ℝ))) * (Work.FTS.Nonlin.Xn α g) ^ 2) from by ring]
            rw [hαr]
        _ ≤ 120 * Real.sqrt 10 * max Ce 0
              * (α ^ (-(3 / 2 : ℝ)) * (Work.FTS.Nonlin.Xn α g) ^ 2) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hh3 (sq_nonneg _)) hc0
        _ ≤ 120 * Real.sqrt 10 * max Ce 0 * env α
              (Work.FTS.Nonlin.Xn α g) := mul_le_mul_of_nonneg_left henv hc0
        _ ≤ (120 * Real.sqrt 10 * max Ce 0 + 27 * Real.pi / 4 + 1)
              * env α (Work.FTS.Nonlin.Xn α g) := key _ le_rfl
    constructor
    · refine (ggRow4'' (α₂ := α₂) (Ci := Ci) (Ce := Ce) (Cs := Cs) hN
        hgal hs hell hα hα1 hαα₂).trans (ENNReal.ofReal_le_ofReal ?_)
      calc (27 * Real.pi / 8) * (Work.FTS.Nonlin.Xn α g) ^ 2
          ≤ (27 * Real.pi / 4) * (Work.FTS.Nonlin.Xn α g) ^ 2 := by
            nlinarith [sq_nonneg (Work.FTS.Nonlin.Xn α g), Real.pi_pos]
        _ ≤ (27 * Real.pi / 4) * (α ^ (-(3 / 2 : ℝ)) * (Work.FTS.Nonlin.Xn α g) ^ 2) :=
            mul_le_mul_of_nonneg_left
              (by nlinarith [hone, sq_nonneg (Work.FTS.Nonlin.Xn α g)]) (by positivity)
        _ ≤ (27 * Real.pi / 4) * env α (Work.FTS.Nonlin.Xn α g) :=
            mul_le_mul_of_nonneg_left henv (by positivity)
        _ ≤ (120 * Real.sqrt 10 * max Ce 0 + 27 * Real.pi / 4 + 1)
              * env α (Work.FTS.Nonlin.Xn α g) := key2
    · refine (ggRow5'' (α₂ := α₂) (Ci := Ci) (Ce := Ce) (Cs := Cs) hN
        hgal hs hell hα hα1 hαα₂).trans (ENNReal.ofReal_le_ofReal ?_)
      calc (27 * Real.pi / 4) * (Work.FTS.Nonlin.Xn α g) ^ 2
          ≤ (27 * Real.pi / 4) * (α ^ (-(3 / 2 : ℝ)) * (Work.FTS.Nonlin.Xn α g) ^ 2) :=
            mul_le_mul_of_nonneg_left
              (by nlinarith [hone, sq_nonneg (Work.FTS.Nonlin.Xn α g)]) (by positivity)
        _ ≤ (27 * Real.pi / 4) * env α (Work.FTS.Nonlin.Xn α g) :=
            mul_le_mul_of_nonneg_left henv (by positivity)
        _ ≤ (120 * Real.sqrt 10 * max Ce 0 + 27 * Real.pi / 4 + 1)
              * env α (Work.FTS.Nonlin.Xn α g) := key2

/-- **`rl1`** — the second zero-mode estimate of design §3.5: the bound
`|L₁₂(N α (F_* + g) (Φ_s + Φ_g))(0)| ≤ K(α² + √α·X + α^{-3/2}X²)`, `X = Xn α g`. -/
theorem rl1Main {α₂ Ci Ce Cs : ℝ} (hN : Work.FTS.Nonlin.N4Norm Ci α₂) :
    ∃ K : ℝ, 0 < K ∧ ∀ {α : ℝ} {g Φs Φg : Work.FTS.Galerkin.Fn},
      Work.FTS.Nonlin.GalClass α g → Work.FTS.Nonlin.StarPkg α Cs Φs →
      Work.FTS.Nonlin.EllPkgG α Ce g Φg → 0 < α → α ≤ 1 → α ≤ α₂ →
      |Work.Construction.L12 (Work.Construction.N α (Work.Construction.Ftot α g)
        (fun z θ => Φs z θ + Φg z θ)) 0|
      ≤ K * (α ^ 2 + Real.sqrt α * Work.FTS.Nonlin.Xn α g
          + α ^ (-(3 / 2 : ℝ)) * Work.FTS.Nonlin.Xn α g ^ 2) := by
  obtain ⟨K1, hK1, hP1⟩ := ggEnv (α₂ := α₂) (Ci := Ci) (Ce := Ce) (Cs := Cs)
  obtain ⟨K2, hK2, hP2⟩ := Work.FTS.Nonlinear.Pieces.rl1Pieces.Pgs
    (α₂ := α₂) (Ci := Ci) (Ce := Ce) (Cs := Cs)
  obtain ⟨K3, hK3, hP3⟩ := Work.FTS.Nonlinear.Pieces.rl1Pieces.PsgEnv
    (α₂ := α₂) (Ci := Ci) (Ce := Ce) (Cs := Cs)
  obtain ⟨K4, hK4, hP4⟩ := Work.FTS.Nonlinear.Pieces.rl1Pieces.Pss
    (α₂ := α₂) (Ci := Ci) (Ce := Ce) (Cs := Cs)
  refine ⟨5 * (K1 + K2 + K3 + K4) + 1, by linarith, ?_⟩
  intro α g Φs Φg hgal hs hell hα hα1 hαα₂
  have hb1 := hP1 hα hα1 hαα₂ hN hgal hs hell
  have hb2 := hP2 hα hα1 hαα₂ hN hgal hs hell
  have hb3 := hP3 hα hα1 hαα₂ hN hgal hs hell
  have hb4 := hP4 hα hα1 hαα₂ hN hgal hs hell
  have hXn0 : 0 ≤ Work.FTS.Nonlin.Xn α g := Work.Spaces.HkNorm_nonneg α 4 g
  have hL12g : ∀ z : ℝ, 0 < z →
      DifferentiableAt ℝ (fun z' => Work.Construction.L12 g z') z :=
    fun z hz => hN.l12diff α ⟨hα, hαα₂⟩ g hgal.reg.1
      (Work.FTS.GalerkinFix.RegQ.regQ_mono hgal.reg (by norm_num)).2.1 z hz
  have hsp := Work.FTS.Nonlinear.Pieces.rl1Tools.Nsplit hα hα1 hgal.reg.1 hs.smooth hell.smooth
    (fun z hz => (Work.FTS.Nonlinear.Pieces.L12FK_add_ge0 hα hα1 hgal).1 z hz.le)
    (fun z hz => (Work.FTS.Nonlinear.Pieces.L12FK_add_ge0 hα hα1 hgal).2 z hz.le) hL12g
  have hsplit : ∀ r θ : ℝ, (r, θ) ∈ Work.Construction.Qd →
      Work.Construction.N α (Work.Construction.Ftot α g)
        (fun z θ => Φs z θ + Φg z θ) r θ
        = ∑ k : Fin 20, Work.FTS.Nonlinear.Pieces.rl1Tools.pv α g Φs Φg k r θ := by
    intro r θ hq
    rw [hsp r θ hq]
    simp only [Work.FTS.Nonlinear.Pieces.rl1Tools.pv, Fin.sum_univ_succ, Matrix.cons_val_zero,
      Matrix.cons_val_succ, Fin.reduceFinMk]
    ring
  have hmeas := Work.FTS.Nonlinear.Pieces.rl1Tools.PvecMeas (α := α) (Ce := Ce) (Cs := Cs)
    hgal hs hell
  have htri := Work.FTS.Nonlinear.Pieces.rl1Tools.FaSumAE
    (N := Work.Construction.N α (Work.Construction.Ftot α g) (fun z θ => Φs z θ + Φg z θ))
    (p := Work.FTS.Nonlinear.Pieces.rl1Tools.pv α g Φs Φg) hsplit hmeas.2.1 hmeas.2.2
  have hpiece : ∀ k : Fin 20, Fa (Work.FTS.Nonlinear.Pieces.rl1Tools.pv α g Φs Φg k)
      ≤ ENNReal.ofReal (Mv K1 K2 K3 K4 α (Work.FTS.Nonlin.Xn α g) k) := by
    intro k
    fin_cases k <;>
      simp only [Work.FTS.Nonlinear.Pieces.rl1Tools.pv, Mv, env, Fa, Matrix.cons_val_zero,
        Matrix.cons_val_succ, Fin.reduceFinMk] <;>
      first
        | exact hb1.1 | exact hb1.2.1 | exact hb1.2.2.1 | exact hb1.2.2.2.1 | exact hb1.2.2.2.2
        | exact hb2.1 | exact hb2.2.1 | exact hb2.2.2.1 | exact hb2.2.2.2.1 | exact hb2.2.2.2.2
        | exact hb3.1 | exact hb3.2.1 | exact hb3.2.2.1 | exact hb3.2.2.2.1 | exact hb3.2.2.2.2
        | exact hb4.1 | exact hb4.2.1 | exact hb4.2.2.1 | exact hb4.2.2.2.1 | exact hb4.2.2.2.2
  have hMvnn : ∀ k : Fin 20, 0 ≤ Mv K1 K2 K3 K4 α (Work.FTS.Nonlin.Xn α g) k :=
    Mv_nonneg hK1 hK2 hK3 hK4 hα hXn0
  have hbig := Mv_sum_le hK1 hK2 hK3 hK4 hα hα1 hXn0
  rw [env] at hbig
  have hFa : Fa (Work.Construction.N α (Work.Construction.Ftot α g)
      (fun z θ => Φs z θ + Φg z θ))
      ≤ ENNReal.ofReal ((5 * (K1 + K2 + K3 + K4) + 1)
        * (α ^ 2 + Real.sqrt α * Work.FTS.Nonlin.Xn α g
          + α ^ (-(3 / 2 : ℝ)) * Work.FTS.Nonlin.Xn α g ^ 2)) := by
    refine le_trans htri ?_
    refine le_trans (Finset.sum_le_sum (fun k _ => hpiece k)) ?_
    rw [(ENNReal.ofReal_sum_of_nonneg (fun k _ => hMvnn k)).symm]
    exact ENNReal.ofReal_le_ofReal hbig
  have hglue := ofReal_L12_le (Work.Construction.N α
    (Work.Construction.Ftot α g) (fun z θ => Φs z θ + Φg z θ))
  refine (ENNReal.ofReal_le_ofReal_iff ?_).mp (le_trans hglue hFa)
  refine mul_nonneg (by linarith) ?_
  have ha : (0 : ℝ) ≤ α ^ 2 := by positivity
  have hq : (0 : ℝ) ≤ Real.sqrt α * Work.FTS.Nonlin.Xn α g :=
    mul_nonneg (Real.sqrt_nonneg α) hXn0
  have hr : (0 : ℝ) ≤ α ^ (-(3 / 2 : ℝ)) * Work.FTS.Nonlin.Xn α g ^ 2 :=
    mul_nonneg (Real.rpow_nonneg hα.le _) (sq_nonneg _)
  linarith

end
end Work.FTS.Nonlinear.Pieces.Rl1
