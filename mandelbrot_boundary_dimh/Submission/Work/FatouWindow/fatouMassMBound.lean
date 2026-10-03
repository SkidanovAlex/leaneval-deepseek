import Mathlib
import Submission.Work.FatouL1.wStripBoundDefs
import Submission.Work.FatouWindow.fatouDerivSetup
import Submission.Work.FatouL1.ballSubsetQreg
import Submission.Work.FatouWindow.fatouU_apriori_bound
import Submission.Work.FatouWindow.fatouDerivBoundedStrip
import Submission.Work.FatouL1.massFatouDerivSubInv
import Submission.Work.FatouL1.massDefectWide
import Submission.Work.FatouL1.shiftEpsMass
import Submission.Work.Fatou.Qreg.InjGeom

/-!
# `Work.FatouWindow.fatouMassMBound`: the line mass of `fatouM = Δ₁ (Φ' - 1)` is bounded

For a near-translation `F` of Shishikura's region `𝒬 = Qreg b₁ b₂` satisfying the `L¹` condition
`∫_line ‖F' - 1‖ ≤ 1/64` (`MandelDim.NearTranslationL1`), for the canonical Fatou coordinate
`Φ = fatouCoord hadm hF` of `Work.FatouL1.fatouDerivSetup`, and for every vertical line
`Re = x`, `x ∈ (wsA x₀, wsB x₀) = (x₀ - 1, x₀ + 2)`, the unit-shift defect of `Φ' - 1`,

`fatouM z = (Φ' (z+1) - 1) - (Φ' z - 1)`,

is integrable along that line and has line mass bounded independently of `x`.

## The proof

Split the Fatou derivative as `Φ' = (Φ' - (F - id)⁻¹) + (F - id)⁻¹`, i.e.
`fatouM z = [D (z+1) - D z] + [R (z+1) - R z]` with

* `D = fatouDefect F Φ = Φ' - (F - id)⁻¹` (the *defect* of Shishikura's Lemma A.2.4(i)), and
* `R = (F - id)⁻¹ = 1/(1 + ε)`, `ε = F - id - 1` (so `‖ε‖ ≤ 1/32` on `Qreg`).

The two pieces are bounded separately, on the triangle inequality:

* `∫⁻_line ‖D‖` is finite and uniformly bounded for the lines of `(x₀-1, x₀+3)` — this is exactly
  what makes the *shifted* line `Re = x + 1` accessible, and it is `massDefectWide`, the widening
  of `massFatouDerivSubInv` (whose proof is Shishikura A.2.4(i) + the deep-channel ball
  `ball_subset_Qreg_chan` + the `L¹` hypothesis for the tail);
* `w ↦ 1/(1+w)` is Lipschitz with constant `(32/31)²` on `‖w‖ ≤ 1/32`, so
  `‖R (z+1) - R z‖ ≤ (32/31)² ‖ε (z+1) - ε z‖`, and `ε (z+1) - ε z = ∫_0^1 (F' - 1) (z + t) dt`
  by the fundamental theorem of calculus; Tonelli (`lintegral_interval_le`) and the `L¹`
  hypothesis (on the lines `Re = x + t`, `t ∈ [0,1]`, each of which lies in `Qreg` because
  `x ∈ (x₀-1, x₀+2)`) give line mass `≤ (32/31)² · 1/64` for this piece (`shiftEpsMass` plus the
  Lipschitz step).

This is the input the Cauchy–Heine solver needs: with `m := ∫_line ‖fatouM‖`, `fatouM` is the data
`Δ₁ (Φ' - 1)` whose line mass controls `Φ''` on the strip `wStrip x₀`.
-/

open MandelDim Set MeasureTheory
open scoped Topology ENNReal

namespace Work.FatouWindow

open Work.FatouL1

noncomputable section

variable {b₁ b₂ : Option ℂ} {F : ℂ → ℂ} {x₀ : ℝ}

/-- The displacement defect `F z - z - 1` of a near-translation. -/
def fatouEps (F : ℂ → ℂ) (z : ℂ) : ℂ := F z - z - 1

lemma fatouEps_add_one (F : ℂ → ℂ) (z : ℂ) : fatouEps F z + 1 = F z - z := by
  simp only [fatouEps]; ring

lemma fatouM_eq_defect (hadm : MandelDim.QAdm b₁ b₂)
    (hF : MandelDim.NearTranslationL1 F (MandelDim.Qreg b₁ b₂)) (z : ℂ) :
    fatouM hadm hF z =
      (fatouDefect F (fatouCoord hadm hF) (z + 1) - fatouDefect F (fatouCoord hadm hF) z) +
      (((F (z + 1) - (z + 1))⁻¹) - ((F z - z)⁻¹)) := by
  simp only [fatouM, fatouU, fatouDefect]
  ring

lemma norm_inv_shift_le (hF : MandelDim.NearTranslationL1 F (MandelDim.Qreg b₁ b₂)) {z : ℂ}
    (hz : z ∈ MandelDim.Qreg b₁ b₂) (hz1 : z + 1 ∈ MandelDim.Qreg b₁ b₂) :
    ‖((F (z + 1) - (z + 1))⁻¹) - ((F z - z)⁻¹)‖
      ≤ (32 / 31 : ℝ) ^ 2 * ‖fatouEps F (z + 1) - fatouEps F z‖ := by
  have h₁ : ‖fatouEps F z‖ ≤ 1 / 32 := by
    have h := (hF.1.2 z hz).1
    have he : F z - (z + 1) = fatouEps F z := by simp only [fatouEps]; ring
    rwa [he] at h
  have h₂ : ‖fatouEps F (z + 1)‖ ≤ 1 / 32 := by
    have h := (hF.1.2 (z + 1) hz1).1
    have he : F (z + 1) - ((z + 1) + 1) = fatouEps F (z + 1) := by simp only [fatouEps]; ring
    rwa [he] at h
  have hw : (F z - z) = 1 + fatouEps F z := by simp only [fatouEps]; ring
  have hw' : (F (z + 1) - (z + 1)) = 1 + fatouEps F (z + 1) := by
    simp only [fatouEps]; ring
  have hb₁ : (31 / 32 : ℝ) ≤ ‖F z - z‖ := by
    have h := norm_add_le (1 + fatouEps F z) (-(fatouEps F z))
    have h' : (1 : ℝ) ≤ ‖1 + fatouEps F z‖ + ‖fatouEps F z‖ := by simpa using h
    rw [hw]; linarith
  have hb₂ : (31 / 32 : ℝ) ≤ ‖F (z + 1) - (z + 1)‖ := by
    have h := norm_add_le (1 + fatouEps F (z + 1)) (-(fatouEps F (z + 1)))
    have h' : (1 : ℝ) ≤ ‖1 + fatouEps F (z + 1)‖ + ‖fatouEps F (z + 1)‖ := by simpa using h
    rw [hw']; linarith
  have hne₁ : F z - z ≠ 0 := by
    intro h0; rw [h0, norm_zero] at hb₁; norm_num at hb₁
  have hne₂ : F (z + 1) - (z + 1) ≠ 0 := by
    intro h0; rw [h0, norm_zero] at hb₂; norm_num at hb₂
  have hM0 : (0 : ℝ) < 31 / 32 := by norm_num
  have hdiff : (F z - z) - (F (z + 1) - (z + 1)) = -(fatouEps F (z + 1) - fatouEps F z) := by
    simp only [fatouEps]; ring
  calc ‖((F (z + 1) - (z + 1))⁻¹) - ((F z - z)⁻¹)‖
      = ‖(F z - z) - (F (z + 1) - (z + 1))‖ / (‖F (z + 1) - (z + 1)‖ * ‖F z - z‖) := by
        rw [inv_sub_inv hne₂ hne₁, norm_div, norm_mul]
    _ = ‖fatouEps F (z + 1) - fatouEps F z‖ / (‖F (z + 1) - (z + 1)‖ * ‖F z - z‖) := by
        rw [hdiff, norm_neg]
    _ ≤ ‖fatouEps F (z + 1) - fatouEps F z‖ / ((31 / 32) * (31 / 32)) := by
        apply div_le_div_of_nonneg_left (norm_nonneg _) (by norm_num)
        exact mul_le_mul hb₂ hb₁ (by norm_num) (norm_nonneg _)
    _ = (32 / 31 : ℝ) ^ 2 * ‖fatouEps F (z + 1) - fatouEps F z‖ := by
        rw [div_eq_mul_inv, mul_comm]
        congr 1
        norm_num

lemma norm_fatouM_le_defect (hadm : MandelDim.QAdm b₁ b₂)
    (hF : MandelDim.NearTranslationL1 F (MandelDim.Qreg b₁ b₂)) {z : ℂ}
    (hz : z ∈ MandelDim.Qreg b₁ b₂) (hz1 : z + 1 ∈ MandelDim.Qreg b₁ b₂) :
    ‖fatouM hadm hF z‖ ≤
      ‖fatouDefect F (fatouCoord hadm hF) (z + 1)‖ + ‖fatouDefect F (fatouCoord hadm hF) z‖
        + (32 / 31 : ℝ) ^ 2 * ‖fatouEps F (z + 1) - fatouEps F z‖ := by
  rw [fatouM_eq_defect hadm hF z]
  refine le_trans (norm_add_le _ _) ?_
  have h1 := norm_inv_shift_le (F := F) hF hz hz1
  have h2 := norm_sub_le (fatouDefect F (fatouCoord hadm hF) (z + 1))
    (fatouDefect F (fatouCoord hadm hF) z)
  linarith

/-! ## Continuity -/

lemma continuousOn_fatouDefect (hF : MandelDim.NearTranslationL1 F (MandelDim.Qreg b₁ b₂))
    {Φ : ℂ → ℂ} (hΦ : MandelDim.IsFatouCoordOn F Φ (MandelDim.Qreg b₁ b₂)) :
    ContinuousOn (fatouDefect F Φ) (MandelDim.Qreg b₁ b₂) := by
  have hQopen : IsOpen (MandelDim.Qreg b₁ b₂) := Work.Fatou.Qreg.isOpen_Qreg b₁ b₂
  have hvne : ∀ z ∈ MandelDim.Qreg b₁ b₂, F z - z ≠ 0 := by
    intro z hz h0
    have h := (hF.1.2 z hz).1
    have hz' : F z = z := sub_eq_zero.mp h0
    have h1 : F z - (z + 1) = -1 := by rw [hz']; ring
    rw [h1, norm_neg, norm_one] at h
    norm_num at h
  have hd : DifferentiableOn ℂ (fatouDefect F Φ) (MandelDim.Qreg b₁ b₂) :=
    (hΦ.1.deriv hQopen).sub ((hF.1.1.sub differentiableOn_id).inv hvne)
  exact hd.continuousOn

lemma continuousOn_inv_sub (hF : MandelDim.NearTranslationL1 F (MandelDim.Qreg b₁ b₂)) :
    ContinuousOn (fun z : ℂ => (F z - z)⁻¹) (MandelDim.Qreg b₁ b₂) := by
  have hvne : ∀ z ∈ MandelDim.Qreg b₁ b₂, F z - z ≠ 0 := by
    intro z hz h0
    have h := (hF.1.2 z hz).1
    have hz' : F z = z := sub_eq_zero.mp h0
    have h1 : F z - (z + 1) = -1 := by rw [hz']; ring
    rw [h1, norm_neg, norm_one] at h
    norm_num at h
  exact ((hF.1.1.sub differentiableOn_id).continuousOn).inv₀ hvne

/-- The strip `(x₀-1, x₀+3)` lies in `Qreg b₁ b₂`. -/
lemma mem_Qreg_of_ws_wide (h₁ : ∀ a ∈ b₁, a.re + 1 < x₀) (h₂ : ∀ b ∈ b₂, x₀ + 3 < b.re)
    {z : ℂ} (hz₁ : x₀ - 1 < z.re) (hz₂ : z.re < x₀ + 3) : z ∈ MandelDim.Qreg b₁ b₂ :=
  mem_Qreg_of_re_strip h₁ h₂ hz₁ hz₂

/-- A point of the strip `(x₀-1, x₀+3)` lies in `Qreg b₁ b₂`. -/
lemma mem_Qreg_of_line (h₁ : ∀ a ∈ b₁, a.re + 1 < x₀) (h₂ : ∀ b ∈ b₂, x₀ + 3 < b.re)
    {x y : ℝ} (hx₁ : x₀ - 1 < x) (hx₂ : x < x₀ + 3) :
    ((x : ℂ) + y * Complex.I) ∈ MandelDim.Qreg b₁ b₂ :=
  mem_Qreg_of_re_strip h₁ h₂ (by simpa using hx₁) (by simpa using hx₂)

theorem fatouMassMBound {b₁ b₂ : Option ℂ} {F : ℂ → ℂ} {x₀ : ℝ}
    (hadm : MandelDim.QAdm b₁ b₂) (hF : MandelDim.NearTranslationL1 F (MandelDim.Qreg b₁ b₂))
    (h₁ : ∀ a ∈ b₁, a.re + 1 < x₀) (h₂ : ∀ b ∈ b₂, x₀ + 3 < b.re) :
    ∃ m₀ : ℝ, ∀ x ∈ Set.Ioo (Work.FatouL1.wsA x₀) (Work.FatouL1.wsB x₀),
      MeasureTheory.Integrable (fun y : ℝ => Work.FatouWindow.fatouM hadm hF ((x : ℂ) + y * Complex.I)) ∧
      ∫⁻ y : ℝ, ENNReal.ofReal ‖Work.FatouWindow.fatouM hadm hF ((x : ℂ) + y * Complex.I)‖
        ≤ ENNReal.ofReal m₀ := by
  obtain ⟨m, hm⟩ := massDefectWide hadm hF h₁ h₂ (fatouCoord_spec hadm hF)
  have hB : ∀ x ∈ Set.Ioo (x₀ - 1) (x₀ + 2),
      ∫⁻ y : ℝ, ENNReal.ofReal
        ‖(F ((x : ℂ) + 1 + y * Complex.I) - ((x : ℂ) + 1 + y * Complex.I) - 1)
          - (F ((x : ℂ) + y * Complex.I) - ((x : ℂ) + y * Complex.I) - 1)‖
        ≤ ENNReal.ofReal (1 / 64) :=
    shiftEpsMass (F := F) hF h₁ h₂
  obtain ⟨M, hM0, hM⟩ : ∃ M : ℝ, 0 ≤ M ∧ ∀ x ∈ Set.Ioo (x₀ - 1) (x₀ + 3),
      ∫⁻ y : ℝ, ENNReal.ofReal
        ‖fatouDefect F (fatouCoord hadm hF) ((x : ℂ) + y * Complex.I)‖ ≤ ENNReal.ofReal M :=
    ⟨max m 0, le_max_right _ _,
      fun x hx => le_trans (hm x hx) (ENNReal.ofReal_le_ofReal (le_max_left _ _))⟩
  have hΦ : MandelDim.IsFatouCoordOn F (fatouCoord hadm hF) (MandelDim.Qreg b₁ b₂) :=
    fatouCoord_spec hadm hF
  have hcDef : ContinuousOn (fatouDefect F (fatouCoord hadm hF)) (MandelDim.Qreg b₁ b₂) :=
    continuousOn_fatouDefect hF hΦ
  have hcInv : ContinuousOn (fun z : ℂ => (F z - z)⁻¹) (MandelDim.Qreg b₁ b₂) :=
    continuousOn_inv_sub hF
  refine ⟨2 * M + (32 / 31 : ℝ) ^ 2 * (1 / 64), ?_⟩
  intro x hx
  simp only [wsA, wsB] at hx
  have hx3 : x ∈ Set.Ioo (x₀ - 1) (x₀ + 3) := ⟨hx.1, by linarith [hx.2]⟩
  have hx1 : x + 1 ∈ Set.Ioo (x₀ - 1) (x₀ + 3) := ⟨by linarith [hx.1], by linarith [hx.2]⟩
  have hxS : x ∈ Set.Ioo (x₀ - 1) (x₀ + 2) := hx
  -- the shifted point `(x:ℂ) + 1 + y * I` written in the `(x+1)` form
  have hpt_eq : ∀ y : ℝ, ((x : ℂ) + 1 + y * Complex.I) = (((x + 1 : ℝ)) : ℂ) + y * Complex.I := by
    intro y; push_cast; ring
  -- continuity of the four line functions
  have hcD : Continuous fun y : ℝ => fatouDefect F (fatouCoord hadm hF) ((x : ℂ) + y * Complex.I) :=
    hcDef.comp_continuous (by fun_prop) fun y => mem_Qreg_of_line h₁ h₂ hx3.1 hx3.2
  have hcD1 : Continuous fun y : ℝ =>
      fatouDefect F (fatouCoord hadm hF) ((x : ℂ) + 1 + y * Complex.I) := by
    rw [show (fun y : ℝ => fatouDefect F (fatouCoord hadm hF) ((x : ℂ) + 1 + y * Complex.I))
        = fun y : ℝ => fatouDefect F (fatouCoord hadm hF) ((((x + 1 : ℝ)) : ℂ) + y * Complex.I)
      from funext fun y => by rw [hpt_eq y]]
    exact hcDef.comp_continuous (by fun_prop) fun y =>
      mem_Qreg_of_line (x := x + 1) (y := y) h₁ h₂ (by linarith [hx.1]) (by linarith [hx.2])
  have hcR : Continuous fun y : ℝ => ((F ((x : ℂ) + y * Complex.I) - ((x : ℂ) + y * Complex.I))⁻¹) :=
    hcInv.comp_continuous (by fun_prop) fun y => mem_Qreg_of_line h₁ h₂ hx3.1 hx3.2
  have hcR1 : Continuous fun y : ℝ =>
      ((F ((x : ℂ) + 1 + y * Complex.I) - ((x : ℂ) + 1 + y * Complex.I))⁻¹) := by
    rw [show (fun y : ℝ => ((F ((x : ℂ) + 1 + y * Complex.I) - ((x : ℂ) + 1 + y * Complex.I))⁻¹))
        = fun y : ℝ => ((F ((((x + 1 : ℝ)) : ℂ) + y * Complex.I) - ((((x + 1 : ℝ)) : ℂ) + y * Complex.I))⁻¹)
      from funext fun y => by rw [hpt_eq y]]
    exact hcInv.comp_continuous (by fun_prop) fun y =>
      mem_Qreg_of_line (x := x + 1) (y := y) h₁ h₂ (by linarith [hx.1]) (by linarith [hx.2])
  -- the pointwise bound
  have hpt : ∀ y : ℝ, ENNReal.ofReal ‖fatouM hadm hF ((x : ℂ) + y * Complex.I)‖ ≤
      ENNReal.ofReal ‖fatouDefect F (fatouCoord hadm hF) ((x : ℂ) + 1 + y * Complex.I)‖
      + ENNReal.ofReal ‖fatouDefect F (fatouCoord hadm hF) ((x : ℂ) + y * Complex.I)‖
      + ENNReal.ofReal ((32 / 31 : ℝ) ^ 2 *
          ‖fatouEps F ((x : ℂ) + 1 + y * Complex.I) - fatouEps F ((x : ℂ) + y * Complex.I)‖) := by
    intro y
    have hzw : ((x : ℂ) + y * Complex.I) + 1 = ((x : ℂ) + 1) + y * Complex.I := by ring
    have h1 : ‖fatouM hadm hF ((x : ℂ) + y * Complex.I)‖ ≤
        ‖fatouDefect F (fatouCoord hadm hF) (((x : ℂ) + y * Complex.I) + 1)‖
        + ‖fatouDefect F (fatouCoord hadm hF) ((x : ℂ) + y * Complex.I)‖
        + (32 / 31 : ℝ) ^ 2 *
          ‖fatouEps F (((x : ℂ) + y * Complex.I) + 1) - fatouEps F ((x : ℂ) + y * Complex.I)‖ :=
      norm_fatouM_le_defect hadm hF
        (mem_Qreg_of_line h₁ h₂ hx3.1 hx3.2)
        (by rw [hzw, hpt_eq y]
            exact mem_Qreg_of_line (x := x + 1) (y := y) h₁ h₂ (by linarith [hx.1]) (by linarith [hx.2]))
    rw [hzw] at h1
    have h2 := ENNReal.ofReal_le_ofReal h1
    rw [ENNReal.ofReal_add (by positivity) (by positivity),
      ENNReal.ofReal_add (by positivity) (by positivity)] at h2
    exact h2
  -- measurability of the summands
  have hmeas1 : Measurable fun y : ℝ =>
      ENNReal.ofReal ‖fatouDefect F (fatouCoord hadm hF) ((x : ℂ) + 1 + y * Complex.I)‖ :=
    (hcD1.norm.measurable).ennreal_ofReal
  have hmeas2 : Measurable fun y : ℝ =>
      ENNReal.ofReal ‖fatouDefect F (fatouCoord hadm hF) ((x : ℂ) + y * Complex.I)‖ :=
    (hcD.norm.measurable).ennreal_ofReal
  -- the three line-mass bounds
  have hBD : ∫⁻ y : ℝ, ENNReal.ofReal
        ‖fatouDefect F (fatouCoord hadm hF) ((x : ℂ) + 1 + y * Complex.I)‖ ≤ ENNReal.ofReal M := by
    have hshift : ∫⁻ y : ℝ, ENNReal.ofReal
          ‖fatouDefect F (fatouCoord hadm hF) ((x : ℂ) + 1 + y * Complex.I)‖
        = ∫⁻ y : ℝ, ENNReal.ofReal
          ‖fatouDefect F (fatouCoord hadm hF) ((((x + 1 : ℝ)) : ℂ) + y * Complex.I)‖ := by
      apply lintegral_congr
      intro y
      rw [hpt_eq y]
    rw [hshift]
    exact hM (x + 1) hx1
  have hB1 : ∫⁻ y : ℝ, ENNReal.ofReal
        ‖fatouDefect F (fatouCoord hadm hF) ((x : ℂ) + y * Complex.I)‖ ≤ ENNReal.ofReal M :=
    hM x hx3
  have hBeps : ∫⁻ y : ℝ, ENNReal.ofReal ((32 / 31 : ℝ) ^ 2 *
        ‖fatouEps F ((x : ℂ) + 1 + y * Complex.I) - fatouEps F ((x : ℂ) + y * Complex.I)‖)
      ≤ ENNReal.ofReal ((32 / 31 : ℝ) ^ 2 * (1 / 64)) := by
    have h43 : (0 : ℝ) ≤ (32 / 31 : ℝ) ^ 2 := by positivity
    have h1 : ∫⁻ y : ℝ, ENNReal.ofReal ((32 / 31 : ℝ) ^ 2 *
          ‖fatouEps F ((x : ℂ) + 1 + y * Complex.I) - fatouEps F ((x : ℂ) + y * Complex.I)‖)
        = ENNReal.ofReal ((32 / 31 : ℝ) ^ 2) *
          ∫⁻ y : ℝ, ENNReal.ofReal
            ‖fatouEps F ((x : ℂ) + 1 + y * Complex.I) - fatouEps F ((x : ℂ) + y * Complex.I)‖ := by
      rw [← lintegral_const_mul' (ENNReal.ofReal ((32 / 31 : ℝ) ^ 2)) _ ENNReal.ofReal_ne_top]
      apply lintegral_congr
      intro y
      rw [ENNReal.ofReal_mul h43]
    rw [h1]
    have h2 : ∫⁻ y : ℝ, ENNReal.ofReal
          ‖fatouEps F ((x : ℂ) + 1 + y * Complex.I) - fatouEps F ((x : ℂ) + y * Complex.I)‖
        ≤ ENNReal.ofReal (1 / 64) := by
      have hbb := hB x hxS
      simpa only [fatouEps] using hbb
    calc ENNReal.ofReal ((32 / 31 : ℝ) ^ 2) *
          ∫⁻ y : ℝ, ENNReal.ofReal
            ‖fatouEps F ((x : ℂ) + 1 + y * Complex.I) - fatouEps F ((x : ℂ) + y * Complex.I)‖
        ≤ ENNReal.ofReal ((32 / 31 : ℝ) ^ 2) * ENNReal.ofReal (1 / 64) :=
          mul_le_mul_right h2 _
      _ = ENNReal.ofReal ((32 / 31 : ℝ) ^ 2 * (1 / 64)) := by
          rw [← ENNReal.ofReal_mul h43]
  -- split the lintegral of the three-term sum
  have hadd : ∫⁻ y : ℝ, (ENNReal.ofReal
            ‖fatouDefect F (fatouCoord hadm hF) ((x : ℂ) + 1 + y * Complex.I)‖
          + ENNReal.ofReal ‖fatouDefect F (fatouCoord hadm hF) ((x : ℂ) + y * Complex.I)‖
          + ENNReal.ofReal ((32 / 31 : ℝ) ^ 2 *
              ‖fatouEps F ((x : ℂ) + 1 + y * Complex.I) - fatouEps F ((x : ℂ) + y * Complex.I)‖))
      = ((∫⁻ y : ℝ, ENNReal.ofReal
            ‖fatouDefect F (fatouCoord hadm hF) ((x : ℂ) + 1 + y * Complex.I)‖)
          + (∫⁻ y : ℝ, ENNReal.ofReal
            ‖fatouDefect F (fatouCoord hadm hF) ((x : ℂ) + y * Complex.I)‖))
          + (∫⁻ y : ℝ, ENNReal.ofReal ((32 / 31 : ℝ) ^ 2 *
              ‖fatouEps F ((x : ℂ) + 1 + y * Complex.I) - fatouEps F ((x : ℂ) + y * Complex.I)‖)) := by
    have h₁ : ∫⁻ y : ℝ, (ENNReal.ofReal
            ‖fatouDefect F (fatouCoord hadm hF) ((x : ℂ) + 1 + y * Complex.I)‖
          + ENNReal.ofReal ‖fatouDefect F (fatouCoord hadm hF) ((x : ℂ) + y * Complex.I)‖
          + ENNReal.ofReal ((32 / 31 : ℝ) ^ 2 *
              ‖fatouEps F ((x : ℂ) + 1 + y * Complex.I) - fatouEps F ((x : ℂ) + y * Complex.I)‖))
        = ∫⁻ y : ℝ, ((ENNReal.ofReal
            ‖fatouDefect F (fatouCoord hadm hF) ((x : ℂ) + 1 + y * Complex.I)‖
          + ENNReal.ofReal ‖fatouDefect F (fatouCoord hadm hF) ((x : ℂ) + y * Complex.I)‖)
          + ENNReal.ofReal ((32 / 31 : ℝ) ^ 2 *
              ‖fatouEps F ((x : ℂ) + 1 + y * Complex.I) - fatouEps F ((x : ℂ) + y * Complex.I)‖)) :=
      rfl
    have h₂ : ∫⁻ y : ℝ, ((ENNReal.ofReal
            ‖fatouDefect F (fatouCoord hadm hF) ((x : ℂ) + 1 + y * Complex.I)‖
          + ENNReal.ofReal ‖fatouDefect F (fatouCoord hadm hF) ((x : ℂ) + y * Complex.I)‖)
          + ENNReal.ofReal ((32 / 31 : ℝ) ^ 2 *
              ‖fatouEps F ((x : ℂ) + 1 + y * Complex.I) - fatouEps F ((x : ℂ) + y * Complex.I)‖))
        = (∫⁻ y : ℝ, (ENNReal.ofReal
            ‖fatouDefect F (fatouCoord hadm hF) ((x : ℂ) + 1 + y * Complex.I)‖
          + ENNReal.ofReal ‖fatouDefect F (fatouCoord hadm hF) ((x : ℂ) + y * Complex.I)‖))
          + ∫⁻ y : ℝ, ENNReal.ofReal ((32 / 31 : ℝ) ^ 2 *
              ‖fatouEps F ((x : ℂ) + 1 + y * Complex.I) - fatouEps F ((x : ℂ) + y * Complex.I)‖)
        :=
      lintegral_add_left (μ := volume)
        (f := fun y : ℝ => ENNReal.ofReal
            ‖fatouDefect F (fatouCoord hadm hF) ((x : ℂ) + 1 + y * Complex.I)‖
          + ENNReal.ofReal ‖fatouDefect F (fatouCoord hadm hF) ((x : ℂ) + y * Complex.I)‖)
        (g := fun y : ℝ => ENNReal.ofReal ((32 / 31 : ℝ) ^ 2 *
              ‖fatouEps F ((x : ℂ) + 1 + y * Complex.I) - fatouEps F ((x : ℂ) + y * Complex.I)‖))
        (hmeas1.add hmeas2)
    have h₃ : ∫⁻ y : ℝ, (ENNReal.ofReal
            ‖fatouDefect F (fatouCoord hadm hF) ((x : ℂ) + 1 + y * Complex.I)‖
          + ENNReal.ofReal ‖fatouDefect F (fatouCoord hadm hF) ((x : ℂ) + y * Complex.I)‖)
        = (∫⁻ y : ℝ, ENNReal.ofReal
            ‖fatouDefect F (fatouCoord hadm hF) ((x : ℂ) + 1 + y * Complex.I)‖)
          + (∫⁻ y : ℝ, ENNReal.ofReal
            ‖fatouDefect F (fatouCoord hadm hF) ((x : ℂ) + y * Complex.I)‖) :=
      lintegral_add_left (μ := volume)
        (f := fun y : ℝ => ENNReal.ofReal
            ‖fatouDefect F (fatouCoord hadm hF) ((x : ℂ) + 1 + y * Complex.I)‖)
        (g := fun y : ℝ => ENNReal.ofReal
            ‖fatouDefect F (fatouCoord hadm hF) ((x : ℂ) + y * Complex.I)‖) hmeas1
    rw [h₁, h₂, h₃]
  have hkey : ∫⁻ y : ℝ, ENNReal.ofReal ‖fatouM hadm hF ((x : ℂ) + y * Complex.I)‖
      ≤ ENNReal.ofReal M + ENNReal.ofReal M + ENNReal.ofReal ((32 / 31 : ℝ) ^ 2 * (1 / 64)) := by
    refine le_trans (lintegral_mono hpt) ?_
    rw [hadd]
    exact add_le_add (add_le_add hBD hB1) hBeps
  have hkey2 : ∫⁻ y : ℝ, ENNReal.ofReal ‖fatouM hadm hF ((x : ℂ) + y * Complex.I)‖
      ≤ ENNReal.ofReal (2 * M + (32 / 31 : ℝ) ^ 2 * (1 / 64)) := by
    have heq : ENNReal.ofReal M + ENNReal.ofReal M
        + ENNReal.ofReal ((32 / 31 : ℝ) ^ 2 * (1 / 64))
        = ENNReal.ofReal (2 * M + (32 / 31 : ℝ) ^ 2 * (1 / 64)) := by
      rw [← ENNReal.ofReal_add hM0 hM0,
        ← ENNReal.ofReal_add (by positivity) (by positivity)]
      congr 1
      ring
    rwa [heq] at hkey
  -- continuity of `fatouM` along the line
  have hcontM : Continuous fun y : ℝ => fatouM hadm hF ((x : ℂ) + y * Complex.I) := by
    have hzw : ∀ y : ℝ, ((x : ℂ) + y * Complex.I) + 1 = ((x : ℂ) + 1) + y * Complex.I :=
      fun y => by ring
    have hfun : (fun y : ℝ => fatouM hadm hF ((x : ℂ) + y * Complex.I))
        = fun y : ℝ =>
            (fatouDefect F (fatouCoord hadm hF) ((x : ℂ) + 1 + y * Complex.I)
              - fatouDefect F (fatouCoord hadm hF) ((x : ℂ) + y * Complex.I))
            + (((F ((x : ℂ) + 1 + y * Complex.I) - ((x : ℂ) + 1 + y * Complex.I))⁻¹)
              - ((F ((x : ℂ) + y * Complex.I) - ((x : ℂ) + y * Complex.I))⁻¹)) := by
      funext y
      rw [fatouM_eq_defect hadm hF ((x : ℂ) + y * Complex.I)]
      rw [hzw y]
    rw [hfun]
    exact ((hcD1.sub (hcD)).add (hcR1.sub hcR))
  refine ⟨⟨hcontM.aestronglyMeasurable, ?_⟩, hkey2⟩
  rw [MeasureTheory.hasFiniteIntegral_iff_norm]
  exact lt_of_le_of_lt hkey2 ENNReal.ofReal_lt_top

end

end Work.FatouWindow
