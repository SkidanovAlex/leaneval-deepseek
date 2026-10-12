import ChallengeDeps
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Submission.Work.BoseBogFS.W1_tail_log_le
import Submission.Work.BoseBogFS.betaScTailIntegrableAndEq
import Submission.Work.BoseBogFS.bogKappa_mul_log_le
import Submission.Work.BoseBogFS.honestFsCutoffRows
import Submission.Work.BoseBogFS.psiScTailPointwise
import Submission.Work.BoseBogFS.sqrtRhoaBogTMulALeOne
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBogFS.psiSc_tail_integral_le` — the tail row of FS `lem:BogIntegral`

The target is the estimate

    ∫_{‖t‖ > bogT} psiSc v h ρ μ t dt ≤ C · lhyEps (a v) R …

for the *tail beyond FS's momentum cutoff* `T = bogT v R μ = 10⁶(1+log D^{-1})/ε`, where
`D = μ(a v)³` is the diluteness and `ε = lhyEps` is FS's error of `eq:LebesgueError-Total`.

## The mathematics

* **Pointwise** (`psiSc_tail_pointwise`): with `r = ‖t‖`, `τ = tauScRad v ρ μ r`,
  `b = betaSc v h ρ μ t`, `κ = bogKappa v ρ μ`, writing `L = (τ+b) + √((τ+b)²−b²)` one has
  `psiSc = b²/L − b²/(2r²) = b²·r(2r²−L)/(2r³L)` and
  `2r² − L = 2(r²−τ) − 2b + b²/L`.
  Hence, whenever `τ ≥ r²/8`, `r² − τ ≤ 3κr` and `|b| ≤ B ≤ r²/16`,

      psiSc t ≤ 48κb²/r³ + 16Bb²/r⁴ + 128B²b²/r⁶ .

  (The deficit bound `r²−τ ≤ 3κr` supplies the sharp `κb²/r³`; the extra terms are
  integrable against `r^{-4}` and `r^{-6}`.)
* **Substitution** `p = √(ρa)·t`: since `β(t) = (a v)⁻¹Ŵ₁(√(ρa)t)` and the integrand is
  homogeneous of degree `−3`, the leading term turns into FS's tail

      ∫_{‖t‖>T} β(t)²/‖t‖³ dt = (a v)⁻² ∫_{‖p‖>√(ρa)T} Ŵ₁(p)²/‖p‖³ dp ,

  which `W1_tail_log_le` bounds by `10⁶(1+log(1/(P₀·a v)))`; and
  `bogKappa_mul_log_le` turns `κ(1+log(1/(P₀av)))` into `10⁸·lhyEps`.
* **The two remainder terms** are dominated by `16·(16π)³∫_{‖t‖>T}‖t‖^{-4}` and
  `128·(16π)⁴∫‖t‖^{-6}`, i.e. by `const/T` and `const/T³`, and `T·lhyEps ≥ 10⁶`
  (`Core.hTdef`, `Core.hL1`) pays for them.
* All regime rows (`T ≥ 10⁶/4`, `c₁ ≤ 1`, `P₀·a v ≤ 1`, `|β| ≤ 16π`, …) come from the
  `Core` structure and `FsI1Regime`.

## Imported siblings

`psiSc_tail_le.lean` (the *pointwise* tail row, whose `psiSc_tail_alg_local` is the
sharp sibling of `psiSc_tail_pointwise`), `W1_tail_log_le`, `bogKappa_mul_log_le`,
`honestFsCore` (`Core`).
-/

namespace Work.BoseBogFS

noncomputable section

open scoped Real Topology BigOperators

open MeasureTheory Filter Metric

open _root_.BoseGases Submission.BoseGases Work.UBB Work.BoseBox Work.BoseBoxFix Work.BoseFixR

set_option autoImplicit false
set_option maxHeartbeats 4000000

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-! ## 1. Regime rows from `Core`

These are the elementary consequences of FS's parameter block that the tail estimate
consumes: positivity of `ℓ`, `c₁`, `c₂`, `κ`, of FS's error, the bound `c₁ ≤ 1`,
`T·ε ≥ 10⁶` and `|β| ≤ 16π`.
-/

/-- `lhyEpsX` is strictly positive: its first summand `(μa)^{1/4}√R` is. -/
lemma lhyEpsX_pos {v : E3 → ℝ} {R μ : ℝ} (hR : 0 < R)
    (hav : 0 < _root_.BoseGases.a v) (hμ : 0 < μ) (hD0 : 0 < Work.BoseFixR.dil v μ)
    (hD1 : Work.BoseFixR.dil v μ ≤ 1) :
    0 < lhyEpsX v R μ := by
  have hL0 : 0 ≤ bogL v μ := by
    rw [bogL, one_div]
    exact Real.log_nonneg ((one_le_inv₀ hD0).mpr hD1)
  have h1 : 0 < (μ * _root_.BoseGases.a v) ^ ((1 : ℝ) / 4) * Real.sqrt R :=
    mul_pos (Real.rpow_pos_of_pos (mul_pos hμ hav) _) (Real.sqrt_pos.mpr hR)
  have h2 : 0 ≤ (Work.BoseFixR.dil v μ) ^ ((23 : ℝ) / 1292) := Real.rpow_nonneg hD0.le _
  have h3 : 0 ≤ (Work.BoseFixR.dil v μ) ^ ((1 : ℝ) / 646)
      * (1 + ((162 : ℝ) / 323) * bogL v μ) :=
    mul_nonneg (Real.rpow_nonneg hD0.le _) (by linarith)
  have h4 : 0 ≤ (Work.BoseFixR.dil v μ) ^ ((1 : ℝ) / 1292)
      * (1 + ((156 : ℝ) / 323) * bogL v μ) :=
    mul_nonneg (Real.rpow_nonneg hD0.le _) (by linarith)
  simp only [lhyEpsX]
  simp only [bogL] at h3 h4
  linarith

/-- **`T·ε ≥ 10⁶`**, from the definitional identity `T = 10⁶(1+log D^{-1})/ε`
(`Core.hTdef`) and `log D^{-1} ≥ 0`. -/
lemma bogT_mul_lhyEps_ge {v : E3 → ℝ} {R μ ρ : ℝ} (hR : 0 < R)
    (hav : 0 < _root_.BoseGases.a v) (hC : Core v R μ ρ) :
    10 ^ 6 ≤ bogT v R μ * Work.BoseB6.lhyEps (_root_.BoseGases.a v) R
        (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).eT
        (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).Kl
        (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).s
        (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d μ := by
  have hpos : 0 < lhyEpsX v R μ := lhyEpsX_pos hR hav hC.hμ hC.hD0 hC.hD1
  rw [hC.hEeq, hC.hTdef, div_mul_cancel₀ _ (ne_of_gt hpos)]
  linarith [hC.hL0]

/-- `0 ≤ lhyEps` at the honest data. -/
lemma lhyEps_nonneg_of_core {v : E3 → ℝ} {R μ ρ : ℝ} (hC : Core v R μ ρ) :
    0 ≤ Work.BoseB6.lhyEps (_root_.BoseGases.a v) R
        (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).eT
        (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).Kl
        (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).s
        (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d μ := by
  rw [hC.hEeq]; exact hC.hE0

/-- `0 < ℓ = ell v μ`. -/
lemma ell_pos_of_core {v : E3 → ℝ} {R μ ρ : ℝ}
    (hav : 0 < _root_.BoseGases.a v) (hC : Core v R μ ρ) : 0 < ell v μ := by
  rw [ell_eq_boxSide]
  have h1 : 0 < (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).Kl := by
    rw [paramsAt_Kl]
    exact Real.rpow_pos_of_pos hC.hD0 _
  have h2 : 0 < (μ * _root_.BoseGases.a v) ^ (-(1 / 2 : ℝ)) :=
    Real.rpow_pos_of_pos (mul_pos hC.hμ hav) _
  exact mul_pos h1 h2

/-- `0 < c₁ = bogC1 v ρ μ`. -/
lemma bogC1_pos_of_core {v : E3 → ℝ} {R μ ρ : ℝ}
    (hav : 0 < _root_.BoseGases.a v) (hC : Core v R μ ρ) : 0 < bogC1 v ρ μ := by
  rw [bogC1_eq v ρ μ hav hC.hμ hC.hρ0]
  have h1 : 0 < ((Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).Kl
      * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).s)⁻¹ := by
    refine inv_pos.mpr (mul_pos ?_ ?_)
    · rw [paramsAt_Kl]; exact Real.rpow_pos_of_pos hC.hD0 _
    · rw [paramsAt_s]; exact Real.rpow_pos_of_pos hC.hD0 _
  have h2 : 0 < Real.sqrt (μ / ρ) := Real.sqrt_pos.mpr (div_pos hC.hμ hC.hρ0)
  positivity

/-- `0 < c₂ = bogC2 v ρ μ`. -/
lemma bogC2_pos_of_core {v : E3 → ℝ} {R μ ρ : ℝ}
    (hav : 0 < _root_.BoseGases.a v) (hC : Core v R μ ρ) : 0 < bogC2 v ρ μ := by
  rw [bogC2_eq v ρ μ hav hC.hμ hC.hρ0]
  have h1 : 0 < ((Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).Kl
      * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d
      * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).s)⁻¹ := by
    refine inv_pos.mpr (mul_pos (mul_pos ?_ ?_) ?_)
    · rw [paramsAt_Kl]; exact Real.rpow_pos_of_pos hC.hD0 _
    · rw [paramsAt_d]; exact Real.rpow_pos_of_pos hC.hD0 _
    · rw [paramsAt_s]; exact Real.rpow_pos_of_pos hC.hD0 _
  have h2 : 0 < Real.sqrt (μ / ρ) := Real.sqrt_pos.mpr (div_pos hC.hμ hC.hρ0)
  positivity

/-- `c₁ ≤ 1`: `c₁ = ½D^{1/646}√(μ/ρ) ≤ ½·1·2`. -/
lemma bogC1_le_one_of_core {v : E3 → ℝ} {R μ ρ : ℝ}
    (hav : 0 < _root_.BoseGases.a v) (hC : Core v R μ ρ) : bogC1 v ρ μ ≤ 1 := by
  rw [bogC1_eq_dil v ρ μ hav hC.hμ hC.hρ0 hC.hD0]
  have h1 : (Work.BoseFixR.dil v μ) ^ ((1 : ℝ) / 646) ≤ 1 :=
    Real.rpow_le_one hC.hD0.le hC.hD1 (by norm_num)
  have h2 : (0 : ℝ) ≤ Real.sqrt (μ / ρ) := Real.sqrt_nonneg _
  nlinarith [h1, h2, hC.hρsqrt]

/-- `0 ≤ κ = bogKappa v ρ μ`. -/
lemma bogKappa_nonneg_of_core {v : E3 → ℝ} {R μ ρ : ℝ}
    (hav : 0 < _root_.BoseGases.a v) (hC : Core v R μ ρ) : 0 ≤ bogKappa v ρ μ := by
  have h1 : 0 ≤ bogC1 v ρ μ := (bogC1_pos_of_core hav hC).le
  have h2 : 0 ≤ bogC2 v ρ μ := (bogC2_pos_of_core hav hC).le
  have h3 : 0 ≤ (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).eT :=
    Real.rpow_nonneg hC.hD0.le _
  have h4 : (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).eT ≤ 1 := by
    rw [paramsAt_eT]
    exact Real.rpow_le_one hC.hD0.le hC.hD1 (by norm_num)
  rw [bogKappa]
  nlinarith

/-- **`|β| ≤ 16π`** for every momentum (FS `eq:WSestimate`). -/
lemma abs_betaSc_le_sixteen_pi {v : E3 → ℝ} {h : Work.UBB.ScatSol v} {R ρ μ : ℝ}
    (hR : 0 < R) (hℓ : 0 < ell v μ)
    (hv : ∀ x : E3, 0 ≤ v x) (hvrad : _root_.BoseGases.IsRadial v)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : E3) R)
    (hav : 0 < _root_.BoseGases.a v) (hρ : 0 < ρ)
    (hRℓ : R ≤ ell v μ * Submission.BoseGases.chiR0) (t : E3) :
    |betaSc v h ρ μ t| ≤ 16 * Real.pi := by
  rw [betaSc_eq v hρ.ne' hav.ne' t, abs_mul,
    abs_of_nonneg (inv_nonneg.mpr hav.le)]
  have h1 := Work.BoseB7AK.W1rows.W1hat_abs_le hR hℓ hv hvrad hv_supp h hRℓ
    (Real.sqrt (ρ * _root_.BoseGases.a v) • t)
  have h2 : (0 : ℝ) < _root_.BoseGases.a v := hav
  calc (_root_.BoseGases.a v)⁻¹
        * |Work.BoseFixR.chat (Work.BoseFixR.W1fun v h (ell v μ))
            (Real.sqrt (ρ * _root_.BoseGases.a v) • t)|
      ≤ (_root_.BoseGases.a v)⁻¹ * (16 * Real.pi * _root_.BoseGases.a v) :=
        mul_le_mul_of_nonneg_left h1 (inv_nonneg.mpr hav.le)
    _ = 16 * Real.pi := by field_simp

/-- `β = betaSc` is continuous (it is `a⁻¹·Ŵ₁(√(ρa)·)`, and `Ŵ₁` is a Fourier
transform of an `L¹` function). -/
lemma continuous_betaSc {v : E3 → ℝ} {h : Work.UBB.ScatSol v} {R ρ μ : ℝ}
    (hR : 0 < R) (hℓ : 0 < ell v μ)
    (hv : ∀ x : E3, 0 ≤ v x) (hvrad : _root_.BoseGases.IsRadial v)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : E3) R)
    (hav : 0 < _root_.BoseGases.a v) (hρ : 0 < ρ)
    (hRℓ : R ≤ ell v μ * Submission.BoseGases.chiR0) :
    Continuous (fun t : E3 => betaSc v h ρ μ t) := by
  have hW : MeasureTheory.Integrable (Work.BoseFixR.W1fun v h (ell v μ)) :=
    Submission.BoseGases.wScaled_g0_integrable hR hv_supp h hℓ hRℓ
  have hc : Continuous (fun q : E3 => Work.BoseFixR.chat (Work.BoseFixR.W1fun v h (ell v μ)) q) :=
    Work.BoseFixR.continuous_chat _ hW
  have hcomp : Continuous (fun t : E3 =>
      Work.BoseFixR.chat (Work.BoseFixR.W1fun v h (ell v μ))
        (Real.sqrt (ρ * _root_.BoseGases.a v) • t)) :=
    hc.comp (continuous_const_smul (Real.sqrt (ρ * _root_.BoseGases.a v)))
  have hEq : (fun t : E3 => betaSc v h ρ μ t) = fun t : E3 => (_root_.BoseGases.a v)⁻¹
      * Work.BoseFixR.chat (Work.BoseFixR.W1fun v h (ell v μ))
          (Real.sqrt (ρ * _root_.BoseGases.a v) • t) := by
    funext t; rw [betaSc_eq v hρ.ne' hav.ne' t]
  rw [hEq]; exact continuous_const.mul hcomp

/-- **`1/T = ε/(10⁶(1+log D^{-1}))`**: the definitional identity of `bogT`, with `ε = lhyEps`
unfolded to `lhyEpsX`. -/
lemma one_div_bogT_eq {v : E3 → ℝ} {R μ ρ : ℝ} (hR : 0 < R)
    (hav : 0 < _root_.BoseGases.a v) (hC : Core v R μ ρ) :
    1 / bogT v R μ = Work.BoseB6.lhyEps (_root_.BoseGases.a v) R
        (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).eT
        (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).Kl
        (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).s
        (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d μ
      / (10 ^ 6 * (1 + bogL v μ)) := by
  have hpos : 0 < lhyEpsX v R μ := lhyEpsX_pos hR hav hC.hμ hC.hD0 hC.hD1
  rw [hC.hEeq, hC.hTdef, one_div_div]

/-- **`ε ≤ 4(1+log D^{-1})`** (`Core.hEup` and `log D^{-1} ≥ 0`). -/
lemma lhyEps_le_four {v : E3 → ℝ} {R μ ρ : ℝ} (hC : Core v R μ ρ) :
    Work.BoseB6.lhyEps (_root_.BoseGases.a v) R
        (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).eT
        (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).Kl
        (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).s
        (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d μ
      ≤ 4 * (1 + bogL v μ) := by
  rw [hC.hEeq]; linarith [hC.hEup, hC.hL0]



theorem psiSc_tail_integral_le :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {v : EuclideanSpace ℝ (Fin 3) → ℝ} {h : Work.UBB.ScatSol v} {R ρ μ : ℝ},
      0 < R → 0 < _root_.BoseGases.a v → (∀ x, 0 ≤ v x) → _root_.BoseGases.IsRadial v →
      tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R →
      Work.BoseBogFS.Core v R μ ρ →
      Work.BoseB6Est.FsI1Regime (Work.BoseBogFS.bogKernel v R ρ μ)
        (_root_.BoseGases.a v) R ρ μ
        (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).eT
        (Work.BoseBogFS.bogC1 v ρ μ) (Work.BoseBogFS.bogC2 v ρ μ)
        (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).Kl
        (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).s
        (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d →
      R ≤ Work.BoseFixR.ell v μ * Submission.BoseGases.chiR0 →
      Work.BoseBogFS.chiTC * (R / Work.BoseFixR.ell v μ) ^ 2 ≤ 1 / 2 →
      R / Work.BoseFixR.ell v μ ≤ Work.BoseBogFS.chiTR1 →
      MeasureTheory.Integrable (fun t : EuclideanSpace ℝ (Fin 3) =>
        Work.BoseBogFS.psiSc v h ρ μ t) →
      (∫ t in {t : EuclideanSpace ℝ (Fin 3) | Work.BoseBogFS.bogT v R μ < ‖t‖},
          Work.BoseBogFS.psiSc v h ρ μ t)
        ≤ C * Work.BoseB6.lhyEps (_root_.BoseGases.a v) R
            (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).eT
            (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).Kl
            (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).s
            (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d μ := by
  obtain ⟨CW, hCW0, hCW⟩ := W1_tail_log_le
  refine ⟨10 ^ 10 * CW + 10 ^ 9, ?_, ?_⟩
  · have h : (0 : ℝ) ≤ 10 ^ 10 * CW := mul_nonneg (by norm_num) hCW0
    linarith
  intro v h R ρ μ hR hav hv hvrad hv_supp hC hreg hR0 hchi hR1 hint
  let T : ℝ := bogT v R μ
  let E : ℝ := Work.BoseB6.lhyEps (_root_.BoseGases.a v) R
      (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).eT
      (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).Kl
      (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).s
      (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d μ
  let S : Set E3 := {t : E3 | T < ‖t‖}
  have hSmeas : MeasurableSet S := (isOpen_lt continuous_const continuous_norm).measurableSet
  -- ### regime rows
  have hEl : 0 < ell v μ := ell_pos_of_core hav hC
  have hc1 : 0 < bogC1 v ρ μ := bogC1_pos_of_core hav hC
  have hc2 : 0 < bogC2 v ρ μ := bogC2_pos_of_core hav hC
  have hc1le : bogC1 v ρ μ ≤ 1 := bogC1_le_one_of_core hav hC
  have hκnn : 0 ≤ bogKappa v ρ μ := bogKappa_nonneg_of_core hav hC
  have hP : 0 < ρ * _root_.BoseGases.a v := mul_pos hC.hρ0 hav
  have heT0 : 0 ≤ (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).eT :=
    Real.rpow_nonneg hC.hD0.le _
  have heT1 : (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).eT ≤ 1 := by
    rw [paramsAt_eT]
    exact Real.rpow_le_one hC.hD0.le hC.hD1 (by norm_num)
  have heT12 : (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).eT ≤ 1 / 2 := by
    rw [paramsAt_eT]
    have h23 : (Work.BoseFixR.dil v μ) ^ ((23 : ℝ) / 1292)
        ≤ (Work.BoseFixR.dil v μ) ^ ((1 : ℝ) / 1292) :=
      Real.rpow_le_rpow_of_exponent_ge hC.hD0 hC.hD1 (by norm_num)
    linarith [h23, hC.hDs]
  have hTlow : 10 ^ 6 / 4 ≤ T := hC.hTlow
  have hTpos : 0 < T := hC.hTpos
  have hE0 : 0 ≤ E := lhyEps_nonneg_of_core hC
  have hβle : ∀ t : E3, |betaSc v h ρ μ t| ≤ 16 * Real.pi :=
    fun t => abs_betaSc_le_sixteen_pi hR hEl hv hvrad hv_supp hav hC.hρ0 hR0 t
  -- ### the pointwise bound on the tail
  have hpoint : ∀ t ∈ S, psiSc v h ρ μ t
      ≤ (48 * bogKappa v ρ μ) * ((betaSc v h ρ μ t) ^ 2 / ‖t‖ ^ 3)
        + (16 * (16 * Real.pi)) * ((betaSc v h ρ μ t) ^ 2 / ‖t‖ ^ 4)
        + (128 * (16 * Real.pi) ^ 2) * ((betaSc v h ρ μ t) ^ 2 / ‖t‖ ^ 6) := by
    intro t ht
    have ht' : T < ‖t‖ := ht
    have h4c1 : 4 * bogC1 v ρ μ ≤ ‖t‖ := by
      have h1 : (4 : ℝ) * bogC1 v ρ μ ≤ 4 := by linarith
      linarith [hTlow, ht']
    have hdef : ‖t‖ ^ 2 - tauScRad v ρ μ ‖t‖ ≤ 3 * bogKappa v ρ μ * ‖t‖ :=
      tauScRad_deficit v hP hc1 hc2 heT0 heT1 (norm_nonneg t)
    have hBr : 16 * (16 * Real.pi) ≤ ‖t‖ ^ 2 := by
      have h1 : (10 ^ 6 / 4 : ℝ) ≤ ‖t‖ := by linarith [hTlow, ht']
      have h2 : (10 ^ 6 / 4 : ℝ) ^ 2 ≤ ‖t‖ ^ 2 := pow_le_pow_left₀ (by norm_num) h1 2
      nlinarith [Real.pi_le_four]
    have hp := psiScTailPointwise (v := v) (h := h) (ρ := ρ) (μ := μ)
      (B := 16 * Real.pi) (t := t) hP heT0 heT12 hc1 hc2 hκnn h4c1 hdef (hβle t) hBr
    refine le_trans hp (le_of_eq ?_)
    rw [mul_div_assoc, mul_div_assoc, mul_div_assoc]
  -- ### integrability of the three pieces on the tail
  have hI3 : IntegrableOn (fun t : E3 => (betaSc v h ρ μ t) ^ 2 / ‖t‖ ^ 3) S :=
    (betaScTailIntegrableAndEq (v := v) (h := h) (R := R) (ρ := ρ) (μ := μ) (T := T)
      hR hEl hv hvrad hv_supp hav hC.hρ0 hTpos hR0).1
  have hg4 : IntegrableOn (fun t : E3 => (16 * Real.pi) ^ 2 * ((‖t‖ : ℝ) ^ 4)⁻¹) S :=
    ((euclTailInvPow.1 hTpos).1).const_mul _
  have hg6 : IntegrableOn (fun t : E3 => (16 * Real.pi) ^ 2 * ((‖t‖ : ℝ) ^ 6)⁻¹) S :=
    ((euclTailInvPow.2 hTpos).1).const_mul _
  have hI4 : IntegrableOn (fun t : E3 => (betaSc v h ρ μ t) ^ 2 / ‖t‖ ^ 4) S := by
    refine hg4.mono' ?_ ?_
    · have h1 : AEStronglyMeasurable (fun t : E3 => (betaSc v h ρ μ t) ^ 2)
          (volume.restrict S) :=
        ((continuous_betaSc hR hEl hv hvrad hv_supp hav hC.hρ0 hR0).pow 2).aestronglyMeasurable
      have h2 : AEStronglyMeasurable (fun t : E3 => ((‖t‖ : ℝ) ^ 4)⁻¹)
          (volume.restrict S) :=
        ((measurable_norm.pow_const 4).inv).aestronglyMeasurable
      exact h1.mul h2
    · filter_upwards with t
      have hβ := hβle t
      have hsq : (betaSc v h ρ μ t) ^ 2 ≤ (16 * Real.pi) ^ 2 := by
        rw [← sq_abs (betaSc v h ρ μ t)]
        exact pow_le_pow_left₀ (abs_nonneg _) hβ 2
      have h4nn : (0 : ℝ) ≤ (‖t‖ : ℝ) ^ 4 := by positivity
      rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (sq_nonneg _) h4nn), div_eq_mul_inv]
      exact mul_le_mul_of_nonneg_right hsq (inv_nonneg.mpr h4nn)
  have hI6 : IntegrableOn (fun t : E3 => (betaSc v h ρ μ t) ^ 2 / ‖t‖ ^ 6) S := by
    refine hg6.mono' ?_ ?_
    · have h1 : AEStronglyMeasurable (fun t : E3 => (betaSc v h ρ μ t) ^ 2)
          (volume.restrict S) :=
        ((continuous_betaSc hR hEl hv hvrad hv_supp hav hC.hρ0 hR0).pow 2).aestronglyMeasurable
      have h2 : AEStronglyMeasurable (fun t : E3 => ((‖t‖ : ℝ) ^ 6)⁻¹)
          (volume.restrict S) :=
        ((measurable_norm.pow_const 6).inv).aestronglyMeasurable
      exact h1.mul h2
    · filter_upwards with t
      have hβ := hβle t
      have hsq : (betaSc v h ρ μ t) ^ 2 ≤ (16 * Real.pi) ^ 2 := by
        rw [← sq_abs (betaSc v h ρ μ t)]
        exact pow_le_pow_left₀ (abs_nonneg _) hβ 2
      have h6nn : (0 : ℝ) ≤ (‖t‖ : ℝ) ^ 6 := by positivity
      rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (sq_nonneg _) h6nn), div_eq_mul_inv]
      exact mul_le_mul_of_nonneg_right hsq (inv_nonneg.mpr h6nn)
  -- ### the majorant and the monotonicity step
  have hI1c : IntegrableOn (fun t : E3 =>
      (48 * bogKappa v ρ μ) * ((betaSc v h ρ μ t) ^ 2 / ‖t‖ ^ 3)) S := hI3.const_mul _
  have hI2c : IntegrableOn (fun t : E3 =>
      (16 * (16 * Real.pi)) * ((betaSc v h ρ μ t) ^ 2 / ‖t‖ ^ 4)) S := hI4.const_mul _
  have hI6c : IntegrableOn (fun t : E3 =>
      (128 * (16 * Real.pi) ^ 2) * ((betaSc v h ρ μ t) ^ 2 / ‖t‖ ^ 6)) S := hI6.const_mul _
  have hI12 : IntegrableOn (fun t : E3 =>
      (48 * bogKappa v ρ μ) * ((betaSc v h ρ μ t) ^ 2 / ‖t‖ ^ 3)
        + (16 * (16 * Real.pi)) * ((betaSc v h ρ μ t) ^ 2 / ‖t‖ ^ 4)) S :=
    (hI1c.add hI2c).congr (Filter.Eventually.of_forall (fun t => rfl))
  have hmaj : IntegrableOn (fun t : E3 =>
      (48 * bogKappa v ρ μ) * ((betaSc v h ρ μ t) ^ 2 / ‖t‖ ^ 3)
        + (16 * (16 * Real.pi)) * ((betaSc v h ρ μ t) ^ 2 / ‖t‖ ^ 4)
        + (128 * (16 * Real.pi) ^ 2) * ((betaSc v h ρ μ t) ^ 2 / ‖t‖ ^ 6)) S :=
    (hI12.add hI6c).congr (Filter.Eventually.of_forall (fun t => rfl))
  have hmono : (∫ t in S, psiSc v h ρ μ t) ≤ ∫ t in S,
      ((48 * bogKappa v ρ μ) * ((betaSc v h ρ μ t) ^ 2 / ‖t‖ ^ 3)
        + (16 * (16 * Real.pi)) * ((betaSc v h ρ μ t) ^ 2 / ‖t‖ ^ 4)
        + (128 * (16 * Real.pi) ^ 2) * ((betaSc v h ρ μ t) ^ 2 / ‖t‖ ^ 6)) :=
    setIntegral_mono_on hint.integrableOn hmaj hSmeas hpoint
  have hsplit : (∫ t in S,
      ((48 * bogKappa v ρ μ) * ((betaSc v h ρ μ t) ^ 2 / ‖t‖ ^ 3)
        + (16 * (16 * Real.pi)) * ((betaSc v h ρ μ t) ^ 2 / ‖t‖ ^ 4)
        + (128 * (16 * Real.pi) ^ 2) * ((betaSc v h ρ μ t) ^ 2 / ‖t‖ ^ 6)))
      = (48 * bogKappa v ρ μ) * (∫ t in S, (betaSc v h ρ μ t) ^ 2 / ‖t‖ ^ 3)
        + (16 * (16 * Real.pi)) * (∫ t in S, (betaSc v h ρ μ t) ^ 2 / ‖t‖ ^ 4)
        + (128 * (16 * Real.pi) ^ 2) * (∫ t in S, (betaSc v h ρ μ t) ^ 2 / ‖t‖ ^ 6) := by
    rw [integral_add (f := fun t : E3 => (48 * bogKappa v ρ μ)
          * ((betaSc v h ρ μ t) ^ 2 / ‖t‖ ^ 3)
          + (16 * (16 * Real.pi)) * ((betaSc v h ρ μ t) ^ 2 / ‖t‖ ^ 4))
        (g := fun t : E3 => (128 * (16 * Real.pi) ^ 2)
          * ((betaSc v h ρ μ t) ^ 2 / ‖t‖ ^ 6)) hI12 hI6c,
      integral_add (f := fun t : E3 => (48 * bogKappa v ρ μ)
          * ((betaSc v h ρ μ t) ^ 2 / ‖t‖ ^ 3))
        (g := fun t : E3 => (16 * (16 * Real.pi))
          * ((betaSc v h ρ μ t) ^ 2 / ‖t‖ ^ 4)) hI1c hI2c,
      integral_const_mul, integral_const_mul, integral_const_mul]
  -- ### the three integral estimates
  have hP0A : Real.sqrt (ρ * _root_.BoseGases.a v) * T * _root_.BoseGases.a v ≤ 1 :=
    sqrtRhoaBogTMulALeOne hav hC
  have hP0pos : 0 < Real.sqrt (ρ * _root_.BoseGases.a v) * T :=
    mul_pos (Real.sqrt_pos.mpr hP) hTpos
  have hA3 : (∫ t in S, (betaSc v h ρ μ t) ^ 2 / ‖t‖ ^ 3)
      ≤ CW * (1 + Real.log
          (1 / (Real.sqrt (ρ * _root_.BoseGases.a v) * T * _root_.BoseGases.a v))) := by
    have hdeq := (betaScTailIntegrableAndEq (v := v) (h := h) (R := R) (ρ := ρ) (μ := μ)
      (T := T) hR hEl hv hvrad hv_supp hav hC.hρ0 hTpos hR0).2
    rw [hdeq]
    have hlt := hCW (v := v) (h := h) (R := R) (ℓ := ell v μ)
      (P₀ := Real.sqrt (ρ * _root_.BoseGases.a v) * T)
      hR hEl hv hvrad hv_supp hR0 hP0pos hP0A
    have hcoe : (0 : ℝ) ≤ ((_root_.BoseGases.a v) ^ 2)⁻¹ :=
      inv_nonneg.mpr (sq_nonneg _)
    have h1 : ((_root_.BoseGases.a v) ^ 2)⁻¹
          * (∫ p in {p : E3 | Real.sqrt (ρ * _root_.BoseGases.a v) * T < ‖p‖},
              (Work.BoseFixR.chat (Work.BoseFixR.W1fun v h (ell v μ)) p) ^ 2 / ‖p‖ ^ 3)
        ≤ ((_root_.BoseGases.a v) ^ 2)⁻¹
          * (CW * (_root_.BoseGases.a v) ^ 2
              * (1 + Real.log (1 / (Real.sqrt (ρ * _root_.BoseGases.a v) * T
                  * _root_.BoseGases.a v)))) :=
      mul_le_mul_of_nonneg_left hlt hcoe
    have h2 : ((_root_.BoseGases.a v) ^ 2)⁻¹
          * (CW * (_root_.BoseGases.a v) ^ 2
              * (1 + Real.log (1 / (Real.sqrt (ρ * _root_.BoseGases.a v) * T
                  * _root_.BoseGases.a v))))
        = CW * (1 + Real.log (1 / (Real.sqrt (ρ * _root_.BoseGases.a v) * T
            * _root_.BoseGases.a v))) := by
      field_simp
    linarith [h1, h2.le, h2.ge]
  have hκlog : bogKappa v ρ μ
      * (1 + Real.log (1 / (Real.sqrt (ρ * _root_.BoseGases.a v) * T
          * _root_.BoseGases.a v))) ≤ 10 ^ 8 * E :=
    bogKappa_mul_log_le (v := v) (R := R) (ρ := ρ) (μ := μ) hR hav hC.hρ0 hreg
  have hA : (48 * bogKappa v ρ μ) * (∫ t in S, (betaSc v h ρ μ t) ^ 2 / ‖t‖ ^ 3)
      ≤ (48 * CW * 10 ^ 8) * E := by
    have h1 : (48 * bogKappa v ρ μ) * (∫ t in S, (betaSc v h ρ μ t) ^ 2 / ‖t‖ ^ 3)
        ≤ (48 * bogKappa v ρ μ)
          * (CW * (1 + Real.log (1 / (Real.sqrt (ρ * _root_.BoseGases.a v) * T
              * _root_.BoseGases.a v)))) :=
      mul_le_mul_of_nonneg_left hA3 (by linarith [hκnn])
    have h2 : (48 * bogKappa v ρ μ)
          * (CW * (1 + Real.log (1 / (Real.sqrt (ρ * _root_.BoseGases.a v) * T
              * _root_.BoseGases.a v))))
        = 48 * CW * (bogKappa v ρ μ
            * (1 + Real.log (1 / (Real.sqrt (ρ * _root_.BoseGases.a v) * T
                * _root_.BoseGases.a v)))) := by ring
    have h3 : 48 * CW * (bogKappa v ρ μ
          * (1 + Real.log (1 / (Real.sqrt (ρ * _root_.BoseGases.a v) * T
              * _root_.BoseGases.a v))))
        ≤ 48 * CW * (10 ^ 8 * E) :=
      mul_le_mul_of_nonneg_left hκlog (mul_nonneg (by norm_num) hCW0)
    have h4 : 48 * CW * (10 ^ 8 * E) = (48 * CW * 10 ^ 8) * E := by ring
    linarith [h1, h2.le, h2.ge, h3, h4.le, h4.ge]
  have h4v : (∫ t in S, ((‖t‖ : ℝ) ^ 4)⁻¹) = 4 * Real.pi / T :=
    (euclTailInvPow.1 hTpos).2
  have h6v : (∫ t in S, ((‖t‖ : ℝ) ^ 6)⁻¹) = 4 * Real.pi / (3 * T ^ 3) :=
    (euclTailInvPow.2 hTpos).2
  have hβ4 : (∫ t in S, (betaSc v h ρ μ t) ^ 2 / ‖t‖ ^ 4)
      ≤ (16 * Real.pi) ^ 2 * (4 * Real.pi / T) := by
    have hm4 : (∫ t in S, (betaSc v h ρ μ t) ^ 2 / ‖t‖ ^ 4)
        ≤ ∫ t in S, (16 * Real.pi) ^ 2 * ((‖t‖ : ℝ) ^ 4)⁻¹ :=
      setIntegral_mono_on hI4 hg4 hSmeas (fun t _ => by
        have hsq : (betaSc v h ρ μ t) ^ 2 ≤ (16 * Real.pi) ^ 2 := by
          rw [← sq_abs (betaSc v h ρ μ t)]
          exact pow_le_pow_left₀ (abs_nonneg _) (hβle t) 2
        have h4nn : (0 : ℝ) ≤ (‖t‖ : ℝ) ^ 4 := by positivity
        rw [div_eq_mul_inv]
        exact mul_le_mul_of_nonneg_right hsq (inv_nonneg.mpr h4nn))
    calc (∫ t in S, (betaSc v h ρ μ t) ^ 2 / ‖t‖ ^ 4)
        ≤ ∫ t in S, (16 * Real.pi) ^ 2 * ((‖t‖ : ℝ) ^ 4)⁻¹ := hm4
      _ = (16 * Real.pi) ^ 2 * (4 * Real.pi / T) := by rw [integral_const_mul, h4v]
  have hβ6 : (∫ t in S, (betaSc v h ρ μ t) ^ 2 / ‖t‖ ^ 6)
      ≤ (16 * Real.pi) ^ 2 * (4 * Real.pi / (3 * T ^ 3)) := by
    have hm6 : (∫ t in S, (betaSc v h ρ μ t) ^ 2 / ‖t‖ ^ 6)
        ≤ ∫ t in S, (16 * Real.pi) ^ 2 * ((‖t‖ : ℝ) ^ 6)⁻¹ :=
      setIntegral_mono_on hI6 hg6 hSmeas (fun t _ => by
        have hsq : (betaSc v h ρ μ t) ^ 2 ≤ (16 * Real.pi) ^ 2 := by
          rw [← sq_abs (betaSc v h ρ μ t)]
          exact pow_le_pow_left₀ (abs_nonneg _) (hβle t) 2
        have h6nn : (0 : ℝ) ≤ (‖t‖ : ℝ) ^ 6 := by positivity
        rw [div_eq_mul_inv]
        exact mul_le_mul_of_nonneg_right hsq (inv_nonneg.mpr h6nn))
    calc (∫ t in S, (betaSc v h ρ μ t) ^ 2 / ‖t‖ ^ 6)
        ≤ ∫ t in S, (16 * Real.pi) ^ 2 * ((‖t‖ : ℝ) ^ 6)⁻¹ := hm6
      _ = (16 * Real.pi) ^ 2 * (4 * Real.pi / (3 * T ^ 3)) := by rw [integral_const_mul, h6v]
  have hTinv : 1 / T = E / (10 ^ 6 * (1 + bogL v μ)) := one_div_bogT_eq hR hav hC
  have hEle : E ≤ 4 * (1 + bogL v μ) := lhyEps_le_four hC
  have hL1 : (0 : ℝ) < 1 + bogL v μ := by linarith [hC.hL0]
  have hB : (16 * (16 * Real.pi)) * (∫ t in S, (betaSc v h ρ μ t) ^ 2 / ‖t‖ ^ 4)
      ≤ 100 * E := by
    have h1 := mul_le_mul_of_nonneg_left hβ4 (by positivity : (0 : ℝ) ≤ 16 * (16 * Real.pi))
    have h2 : (16 * (16 * Real.pi)) * ((16 * Real.pi) ^ 2 * (4 * Real.pi / T))
        = (64 * Real.pi * (16 * Real.pi) ^ 3) * (1 / T) := by
      rw [div_eq_mul_inv]; ring
    rw [h2] at h1
    have h3 : (1 / T) ≤ E / 10 ^ 6 := by
      rw [hTinv]
      refine div_le_div_of_nonneg_left hE0 (by norm_num) ?_
      nlinarith [hC.hL0]
    have h4 : (64 * Real.pi * (16 * Real.pi) ^ 3) * (1 / T)
        ≤ (64 * Real.pi * (16 * Real.pi) ^ 3) * (E / 10 ^ 6) :=
      mul_le_mul_of_nonneg_left h3 (by positivity)
    have h5 : (64 * Real.pi * (16 * Real.pi) ^ 3) * (E / 10 ^ 6) ≤ 100 * E := by
      have hπ4 : Real.pi ^ 4 ≤ 256 := by
        have h := pow_le_pow_left₀ (Real.pi_pos.le) Real.pi_le_four 4
        have h4 : ((4 : ℝ)) ^ 4 = 256 := by norm_num
        rwa [h4] at h
      nlinarith [hπ4, hE0, Real.pi_pos]
    linarith [h1, h4, h5]
  have hC6 : (128 * (16 * Real.pi) ^ 2) * (∫ t in S, (betaSc v h ρ μ t) ^ 2 / ‖t‖ ^ 6)
      ≤ 1 * E := by
    have h1 := mul_le_mul_of_nonneg_left hβ6
      (by positivity : (0 : ℝ) ≤ 128 * (16 * Real.pi) ^ 2)
    have h2 : (128 * (16 * Real.pi) ^ 2) * ((16 * Real.pi) ^ 2 * (4 * Real.pi / (3 * T ^ 3)))
        = (512 * Real.pi * (16 * Real.pi) ^ 4 / 3) * (1 / T) ^ 3 := by
      rw [div_pow, div_eq_mul_inv]; ring
    rw [h2] at h1
    have h3 : (1 / T) ^ 3 ≤ 16 * E / 10 ^ 18 := by
      have hEL : E / (1 + bogL v μ) ≤ 4 := by
        rw [div_le_iff₀ hL1]
        nlinarith [hEle]
      have hEL0 : 0 ≤ E / (1 + bogL v μ) := div_nonneg hE0 hL1.le
      have hsq : (E / (1 + bogL v μ)) ^ 2 ≤ 16 := by nlinarith [hEL, hEL0]
      have hkey : (1 / T) ^ 3
          = E * (E / (1 + bogL v μ)) ^ 2 / (10 ^ 18 * (1 + bogL v μ)) := by
        rw [hTinv, div_pow]
        field_simp
      rw [hkey]
      have h1L : (1 : ℝ) ≤ 1 + bogL v μ := by linarith [hC.hL0]
      rw [div_le_iff₀ (by positivity : (0 : ℝ) < 10 ^ 18 * (1 + bogL v μ))]
      nlinarith [hsq, hE0, h1L]
    have h4 : (512 * Real.pi * (16 * Real.pi) ^ 4 / 3) * (1 / T) ^ 3
        ≤ (512 * Real.pi * (16 * Real.pi) ^ 4 / 3) * (16 * E / 10 ^ 18) :=
      mul_le_mul_of_nonneg_left h3 (by positivity)
    have h5 : (512 * Real.pi * (16 * Real.pi) ^ 4 / 3) * (16 * E / 10 ^ 18) ≤ 1 * E := by
      have hπ5 : Real.pi ^ 5 ≤ 1024 := by
        have h := pow_le_pow_left₀ (Real.pi_pos.le) Real.pi_le_four 5
        have h4 : ((4 : ℝ)) ^ 5 = 1024 := by norm_num
        rwa [h4] at h
      nlinarith [hπ5, hE0, Real.pi_pos]
    linarith [h1, h4, h5]
  have hfin : (∫ t in S, psiSc v h ρ μ t)
      ≤ (48 * CW * 10 ^ 8) * E + 100 * E + 1 * E := by
    calc (∫ t in S, psiSc v h ρ μ t)
        ≤ ∫ t in S,
            ((48 * bogKappa v ρ μ) * ((betaSc v h ρ μ t) ^ 2 / ‖t‖ ^ 3)
              + (16 * (16 * Real.pi)) * ((betaSc v h ρ μ t) ^ 2 / ‖t‖ ^ 4)
              + (128 * (16 * Real.pi) ^ 2) * ((betaSc v h ρ μ t) ^ 2 / ‖t‖ ^ 6)) := hmono
      _ = (48 * bogKappa v ρ μ) * (∫ t in S, (betaSc v h ρ μ t) ^ 2 / ‖t‖ ^ 3)
            + (16 * (16 * Real.pi)) * (∫ t in S, (betaSc v h ρ μ t) ^ 2 / ‖t‖ ^ 4)
            + (128 * (16 * Real.pi) ^ 2) * (∫ t in S, (betaSc v h ρ μ t) ^ 2 / ‖t‖ ^ 6) := hsplit
      _ ≤ (48 * CW * 10 ^ 8) * E + 100 * E + 1 * E := add_le_add (add_le_add hA hB) hC6
  have hlast : (48 * CW * 10 ^ 8) * E + 100 * E + 1 * E
      ≤ (10 ^ 10 * CW + 10 ^ 9) * E := by
    nlinarith [hE0, hCW0]
  linarith [hfin, hlast]

end

end Work.BoseBogFS
