import Mathlib
import Submission.Work.Serre.CellStep.Model
import Submission.Work.Serre.CellStep.Geom
import Submission.Work.RatHurewicz.ExcisionSetup

set_option synthInstance.maxHeartbeats 400000


/-!
# Radial compressions inside the model cell

Two elementary compression facts (`Work.RatHurewicz.CompressRel`), used to reduce the *per-cell*
statement of the cell step over the open model cell to the disc statement:

* the open shell `csSh = {3/4 < ‖x‖ < 1}` deforms radially onto the sphere `{‖x‖ = 7/8}`;
* the open model cell `csB = {‖x‖ < 1}` deforms radially onto the closed ball `{‖x‖ ≤ 7/8}`.

Both deformations fix their target pointwise, so `Work.RatHurewicz.compressRel_of_deformation`
applies.
-/

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

open scoped Topology unitInterval

namespace Work.Serre.SPC

noncomputable section

open Work.RatHurewicz

/-- The scalar of the radial deformation of the ray `(0,∞)` of moduli onto the level `r₀`:
`c(r,t) = ((1-t)·r + t·r₀)/r`. -/
def radCoeff (r r₀ t : ℝ) : ℝ := ((1 - t) * r + t * r₀) / r

theorem radCoeff_mul {r r₀ t : ℝ} (hr : r ≠ 0) : radCoeff r r₀ t * r = (1 - t) * r + t * r₀ := by
  rw [radCoeff, div_mul_cancel₀ _ hr]

theorem radCoeff_nonneg {r r₀ t : ℝ} (hr : 0 < r) (hr₀ : 0 ≤ r₀) (h0 : 0 ≤ t) (h1 : t ≤ 1) :
    0 ≤ radCoeff r r₀ t := by
  rw [radCoeff]
  apply div_nonneg _ (le_of_lt hr)
  have : (0:ℝ) ≤ 1 - t := by linarith
  nlinarith

theorem radCoeff_zero {r r₀ : ℝ} (hr : r ≠ 0) : radCoeff r r₀ 0 = 1 := by
  rw [radCoeff]
  have h : (1 - (0:ℝ)) * r + 0 * r₀ = r := by ring
  rw [h, div_self hr]

theorem radCoeff_one {r r₀ : ℝ} (_hr : r ≠ 0) : radCoeff r r₀ 1 = r₀ / r := by
  rw [radCoeff]
  have h : (1 - (1:ℝ)) * r + 1 * r₀ = r₀ := by ring
  rw [h]

/-! ## The radial deformation of the open shell -/

/-- **The open shell `{3/4 < ‖x‖ < 1}` deforms onto the sphere `{‖x‖ = 7/8}`**, fixing that
sphere pointwise. -/
def shellDeform (n : ℕ) : C(↥(cellShellSet n (3/4) 1) × I, ↥(cellShellSet n (3/4) 1)) where
  toFun z := by
    have hy : 0 < ‖(((z.1 : ↥(cellShellSet n (3/4) 1)) : cellDisk n) : CellVec n)‖ :=
      lt_trans (by norm_num) z.1.2.1
    have hy1 : ‖(((z.1 : ↥(cellShellSet n (3/4) 1)) : cellDisk n) : CellVec n)‖ < 1 := z.1.2.2
    have hyu : 3/4 < ‖(((z.1 : ↥(cellShellSet n (3/4) 1)) : cellDisk n) : CellVec n)‖ := z.1.2.1
    have ht0 : (0:ℝ) ≤ (z.2 : I) := z.2.2.1
    have ht1 : ((z.2 : I) : ℝ) ≤ 1 := z.2.2.2
    have hc : 0 ≤ radCoeff ‖(((z.1 : ↥(cellShellSet n (3/4) 1)) : cellDisk n) : CellVec n)‖
        (7/8) ((z.2 : I) : ℝ) := radCoeff_nonneg hy (by norm_num) ht0 ht1
    have hval : ‖radCoeff ‖(((z.1 : ↥(cellShellSet n (3/4) 1)) : cellDisk n) : CellVec n)‖
        (7/8) ((z.2 : I) : ℝ) • (((z.1 : ↥(cellShellSet n (3/4) 1)) : cellDisk n) : CellVec n)‖
        = (1 - ((z.2 : I) : ℝ)) * ‖(((z.1 : ↥(cellShellSet n (3/4) 1)) : cellDisk n) :
            CellVec n)‖ + ((z.2 : I) : ℝ) * (7/8) := by
      rw [norm_smul, Real.norm_of_nonneg hc, radCoeff_mul (ne_of_gt hy)]
    refine ⟨⟨radCoeff ‖(((z.1 : ↥(cellShellSet n (3/4) 1)) : cellDisk n) : CellVec n)‖
        (7/8) ((z.2 : I) : ℝ) • (((z.1 : ↥(cellShellSet n (3/4) 1)) : cellDisk n) : CellVec n), ?_⟩, ?_⟩
    · rw [Metric.mem_closedBall, dist_eq_norm, sub_zero, hval]
      nlinarith
    · rw [mem_cellShellSet, hval]
      constructor <;> nlinarith
  continuous_toFun := by
    refine Continuous.subtype_mk ?_ _
    refine Continuous.subtype_mk ?_ _
    have h2 : Continuous (fun z : ↥(cellShellSet n (3/4) 1) × I =>
        (((z.1 : ↥(cellShellSet n (3/4) 1)) : cellDisk n) : CellVec n)) :=
      continuous_subtype_val.comp (continuous_subtype_val.comp continuous_fst)
    have h3 : Continuous (fun z : ↥(cellShellSet n (3/4) 1) × I => ((z.2 : I) : ℝ)) :=
      continuous_subtype_val.comp continuous_snd
    have hne : ∀ z : ↥(cellShellSet n (3/4) 1) × I,
        ‖(((z.1 : ↥(cellShellSet n (3/4) 1)) : cellDisk n) : CellVec n)‖ ≠ 0 := fun z =>
      ne_of_gt (lt_trans (by norm_num) z.1.2.1)
    have h4 : Continuous (fun z : ↥(cellShellSet n (3/4) 1) × I =>
        radCoeff ‖(((z.1 : ↥(cellShellSet n (3/4) 1)) : cellDisk n) : CellVec n)‖ (7/8)
          ((z.2 : I) : ℝ)) := by
      rw [show (fun z : ↥(cellShellSet n (3/4) 1) × I =>
          radCoeff ‖(((z.1 : ↥(cellShellSet n (3/4) 1)) : cellDisk n) : CellVec n)‖ (7/8)
            ((z.2 : I) : ℝ))
          = fun z => (((1 - ((z.2 : I) : ℝ)) *
                ‖(((z.1 : ↥(cellShellSet n (3/4) 1)) : cellDisk n) : CellVec n)‖
              + ((z.2 : I) : ℝ) * (7/8))
            / ‖(((z.1 : ↥(cellShellSet n (3/4) 1)) : cellDisk n) : CellVec n)‖) from rfl]
      exact Continuous.div (((continuous_const.sub h3).mul (continuous_norm.comp h2)).add
        (h3.mul continuous_const)) (continuous_norm.comp h2) (fun z => hne z)
    exact h4.smul h2

theorem shellDeform_zero (n : ℕ) (y : ↥(cellShellSet n (3/4) 1)) :
    shellDeform n (y, 0) = y := by
  apply Subtype.ext
  apply Subtype.ext
  show radCoeff ‖((y : cellDisk n) : CellVec n)‖ (7/8) 0
      • (((y : cellDisk n)) : CellVec n) = ((y : cellDisk n) : CellVec n)
  have hy : ‖((y : cellDisk n) : CellVec n)‖ ≠ 0 := ne_of_gt (lt_trans (by norm_num) y.2.1)
  rw [radCoeff_zero hy, one_smul]

theorem shellDeform_one (n : ℕ) (y : ↥(cellShellSet n (3/4) 1)) :
    ‖(((shellDeform n (y, 1) : ↥(cellShellSet n (3/4) 1)) : cellDisk n) : CellVec n)‖ = 7/8 := by
  have hy : 0 < ‖((y : cellDisk n) : CellVec n)‖ := lt_trans (by norm_num) y.2.1
  have hc : 0 ≤ radCoeff ‖((y : cellDisk n) : CellVec n)‖ (7/8) (1:ℝ) :=
    radCoeff_nonneg hy (by norm_num) (by norm_num) (by norm_num)
  show ‖radCoeff ‖((y : cellDisk n) : CellVec n)‖ (7/8) (1:ℝ)
      • (((y : cellDisk n)) : CellVec n)‖ = 7/8
  rw [norm_smul, Real.norm_of_nonneg hc, radCoeff_mul (ne_of_gt hy)]
  ring

theorem shellDeform_fix (n : ℕ) (y : ↥(cellShellSet n (3/4) 1))
    (hy : ‖((y : cellDisk n) : CellVec n)‖ = 7/8) (t : I) :
    shellDeform n (y, t) = y := by
  apply Subtype.ext
  apply Subtype.ext
  show radCoeff ‖((y : cellDisk n) : CellVec n)‖ (7/8) ((t : I) : ℝ)
      • (((y : cellDisk n)) : CellVec n) = ((y : cellDisk n) : CellVec n)
  have hne : ‖((y : cellDisk n) : CellVec n)‖ ≠ 0 := by rw [hy]; norm_num
  have h1 : radCoeff ‖((y : cellDisk n) : CellVec n)‖ (7/8) ((t : I) : ℝ) = 1 := by
    rw [radCoeff, hy]
    have h : (1 - ((t : I) : ℝ)) * (7/8) + ((t : I) : ℝ) * (7/8) = 7/8 := by ring
    rw [h, div_self]
    norm_num
  rw [h1, one_smul]

/-- The sphere of radius `7/8` inside the open shell. -/
abbrev sphereShell (n : ℕ) : Set ↥(cellShellSet n (3/4) 1) :=
  {x | ‖((x : cellDisk n) : CellVec n)‖ = 7/8}

/-- **The open shell compresses onto the sphere of radius `7/8`.** -/
theorem compressRel_csSh_csS (n : ℕ) :
    ∀ d, CompressRel ↥(cellShellSet n (3/4) 1) (sphereShell n) d :=
  fun d => compressRel_of_deformation (A := sphereShell n) (shellDeform n)
    (shellDeform_zero n)
    (fun y => by
      show ((shellDeform n) (y, 1) : ↥(cellShellSet n (3/4) 1)) ∈ sphereShell n
      simpa [sphereShell] using shellDeform_one n y)
    (fun y hy t => shellDeform_fix n y hy t) d

/-! ## The linear contractions onto the centre -/

/-- The linear contraction of the closed model ball of radius `7/8` onto its centre, fixing the
centre pointwise. -/
def ballClosedDeform (n : ℕ) :
    C(↥(cellBallSet n (7/8)) × I, ↥(cellBallSet n (7/8))) where
  toFun z := by
    have ht0 : (0:ℝ) ≤ (z.2 : I) := z.2.2.1
    have ht1 : ((z.2 : I) : ℝ) ≤ 1 := z.2.2.2
    have hy : ‖(((z.1 : ↥(cellBallSet n (7/8))) : cellDisk n) : CellVec n)‖ ≤ 7/8 := z.1.2
    have hval : ‖(1 - ((z.2 : I) : ℝ)) •
        (((z.1 : ↥(cellBallSet n (7/8))) : cellDisk n) : CellVec n)‖
        = |1 - ((z.2 : I) : ℝ)| *
          ‖(((z.1 : ↥(cellBallSet n (7/8))) : cellDisk n) : CellVec n)‖ := norm_smul _ _
    refine ⟨⟨(1 - ((z.2 : I) : ℝ)) •
      (((z.1 : ↥(cellBallSet n (7/8))) : cellDisk n) : CellVec n), ?_⟩, ?_⟩
    · rw [Metric.mem_closedBall, dist_eq_norm, sub_zero, hval]
      have h1 : |1 - ((z.2 : I) : ℝ)| ≤ 1 := abs_le.mpr ⟨by linarith, by linarith⟩
      calc |1 - ((z.2 : I) : ℝ)| *
            ‖(((z.1 : ↥(cellBallSet n (7/8))) : cellDisk n) : CellVec n)‖
          ≤ 1 * (7/8) := mul_le_mul_of_nonneg h1 hy (abs_nonneg _) (by norm_num)
        _ ≤ 1 := by norm_num
    · rw [mem_cellBallSet, hval]
      have h1 : |1 - ((z.2 : I) : ℝ)| ≤ 1 := abs_le.mpr ⟨by linarith, by linarith⟩
      calc |1 - ((z.2 : I) : ℝ)| *
            ‖(((z.1 : ↥(cellBallSet n (7/8))) : cellDisk n) : CellVec n)‖
          ≤ 1 * (7/8) := mul_le_mul_of_nonneg h1 hy (abs_nonneg _) (by norm_num)
        _ = 7/8 := by norm_num
  continuous_toFun := by
    refine Continuous.subtype_mk ?_ _
    refine Continuous.subtype_mk ?_ _
    have h2 : Continuous (fun z : ↥(cellBallSet n (7/8)) × I =>
        (((z.1 : ↥(cellBallSet n (7/8))) : cellDisk n) : CellVec n)) :=
      continuous_subtype_val.comp (continuous_subtype_val.comp continuous_fst)
    have h3 : Continuous (fun z : ↥(cellBallSet n (7/8)) × I => ((z.2 : I) : ℝ)) :=
      continuous_subtype_val.comp continuous_snd
    exact (continuous_const.sub h3).smul h2

theorem ballClosedDeform_zero (n : ℕ) (y : ↥(cellBallSet n (7/8))) :
    ballClosedDeform n (y, 0) = y := by
  apply Subtype.ext
  apply Subtype.ext
  show (1 - (0:ℝ)) • (((y : cellDisk n)) : CellVec n) = ((y : cellDisk n) : CellVec n)
  rw [sub_zero, one_smul]

theorem ballClosedDeform_one (n : ℕ) (y : ↥(cellBallSet n (7/8))) :
    (((ballClosedDeform n (y, 1) : ↥(cellBallSet n (7/8))) : cellDisk n) : CellVec n) = 0 := by
  show (1 - (1:ℝ)) • (((y : cellDisk n)) : CellVec n) = 0
  rw [sub_self, zero_smul]

theorem ballClosedDeform_fix (n : ℕ) (y : ↥(cellBallSet n (7/8)))
    (hy : (((y : cellDisk n)) : CellVec n) = 0) (t : I) :
    ballClosedDeform n (y, t) = y := by
  apply Subtype.ext
  apply Subtype.ext
  show (1 - ((t : I) : ℝ)) • (((y : cellDisk n)) : CellVec n) = ((y : cellDisk n) : CellVec n)
  rw [hy, smul_zero]

/-- **The closed model ball of radius `7/8` compresses onto its centre.** -/
theorem compressRel_ballClosed_centre (n : ℕ) :
    ∀ d, CompressRel ↥(cellBallSet n (7/8))
      {x : ↥(cellBallSet n (7/8)) | (((x : cellDisk n)) : CellVec n) = 0} d :=
  fun d => compressRel_of_deformation
    (A := {x : ↥(cellBallSet n (7/8)) | (((x : cellDisk n)) : CellVec n) = 0})
    (ballClosedDeform n) (ballClosedDeform_zero n)
    (fun y => by
      show ((ballClosedDeform n) (y, 1) : ↥(cellBallSet n (7/8)))
        ∈ {x : ↥(cellBallSet n (7/8)) | (((x : cellDisk n)) : CellVec n) = 0}
      exact ballClosedDeform_one n y)
    (fun y hy t => ballClosedDeform_fix n y hy t) d

/-- The linear contraction of the open model cell onto its centre, fixing the centre pointwise. -/
def ballOpenDeform (n : ℕ) : C(↥(cellInner n) × I, ↥(cellInner n)) where
  toFun z := by
    have ht0 : (0:ℝ) ≤ (z.2 : I) := z.2.2.1
    have ht1 : ((z.2 : I) : ℝ) ≤ 1 := z.2.2.2
    have hy : ‖(((z.1 : ↥(cellInner n)) : cellDisk n) : CellVec n)‖ < 1 := z.1.2
    have hval : ‖(1 - ((z.2 : I) : ℝ)) •
        (((z.1 : ↥(cellInner n)) : cellDisk n) : CellVec n)‖
        = |1 - ((z.2 : I) : ℝ)| *
          ‖(((z.1 : ↥(cellInner n)) : cellDisk n) : CellVec n)‖ := norm_smul _ _
    refine ⟨⟨(1 - ((z.2 : I) : ℝ)) •
      (((z.1 : ↥(cellInner n)) : cellDisk n) : CellVec n), ?_⟩, ?_⟩
    · rw [Metric.mem_closedBall, dist_eq_norm, sub_zero, hval]
      have h1 : |1 - ((z.2 : I) : ℝ)| ≤ 1 := abs_le.mpr ⟨by linarith, by linarith⟩
      calc |1 - ((z.2 : I) : ℝ)| *
            ‖(((z.1 : ↥(cellInner n)) : cellDisk n) : CellVec n)‖
          ≤ 1 * 1 := mul_le_mul_of_nonneg' h1 (le_of_lt hy) (norm_nonneg _) (by norm_num)
        _ = 1 := by norm_num
    · change ‖(1 - ((z.2 : I) : ℝ)) •
        (((z.1 : ↥(cellInner n)) : cellDisk n) : CellVec n)‖ < 1
      rw [hval]
      have h1 : |1 - ((z.2 : I) : ℝ)| ≤ 1 := abs_le.mpr ⟨by linarith, by linarith⟩
      calc |1 - ((z.2 : I) : ℝ)| *
            ‖(((z.1 : ↥(cellInner n)) : cellDisk n) : CellVec n)‖
          ≤ 1 * ‖(((z.1 : ↥(cellInner n)) : cellDisk n) : CellVec n)‖ :=
            mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
        _ = ‖(((z.1 : ↥(cellInner n)) : cellDisk n) : CellVec n)‖ := one_mul _
        _ < 1 := hy
  continuous_toFun := by
    refine Continuous.subtype_mk ?_ _
    refine Continuous.subtype_mk ?_ _
    have h2 : Continuous (fun z : ↥(cellInner n) × I =>
        (((z.1 : ↥(cellInner n)) : cellDisk n) : CellVec n)) :=
      continuous_subtype_val.comp (continuous_subtype_val.comp continuous_fst)
    have h3 : Continuous (fun z : ↥(cellInner n) × I => ((z.2 : I) : ℝ)) :=
      continuous_subtype_val.comp continuous_snd
    exact (continuous_const.sub h3).smul h2

theorem ballOpenDeform_zero (n : ℕ) (y : ↥(cellInner n)) : ballOpenDeform n (y, 0) = y := by
  apply Subtype.ext
  apply Subtype.ext
  show (1 - (0:ℝ)) • (((y : cellDisk n)) : CellVec n) = ((y : cellDisk n) : CellVec n)
  rw [sub_zero, one_smul]

theorem ballOpenDeform_one (n : ℕ) (y : ↥(cellInner n)) :
    (((ballOpenDeform n (y, 1) : ↥(cellInner n)) : cellDisk n) : CellVec n) = 0 := by
  show (1 - (1:ℝ)) • (((y : cellDisk n)) : CellVec n) = 0
  rw [sub_self, zero_smul]

theorem ballOpenDeform_fix (n : ℕ) (y : ↥(cellInner n))
    (hy : (((y : cellDisk n)) : CellVec n) = 0) (t : I) : ballOpenDeform n (y, t) = y := by
  apply Subtype.ext
  apply Subtype.ext
  show (1 - ((t : I) : ℝ)) • (((y : cellDisk n)) : CellVec n) = ((y : cellDisk n) : CellVec n)
  rw [hy, smul_zero]

/-- **The open model cell compresses onto its centre.** -/
theorem compressRel_csB_centre (n : ℕ) :
    ∀ d, CompressRel ↥(cellInner n)
      {x : ↥(cellInner n) | (((x : cellDisk n)) : CellVec n) = 0} d :=
  fun d => compressRel_of_deformation
    (A := {x : ↥(cellInner n) | (((x : cellDisk n)) : CellVec n) = 0})
    (ballOpenDeform n) (ballOpenDeform_zero n)
    (fun y => by
      show ((ballOpenDeform n) (y, 1) : ↥(cellInner n))
        ∈ {x : ↥(cellInner n) | (((x : cellDisk n)) : CellVec n) = 0}
      exact ballOpenDeform_one n y)
    (fun y hy t => ballOpenDeform_fix n y hy t) d

/-! ## The closed shell -/

/-- The closed shell `{lo ≤ ‖x‖}` of the model cell. -/
abbrev cellClosedShell (n : ℕ) (lo : ℝ) : Set (cellDisk n) :=
  {x | lo ≤ ‖(x : CellVec n)‖}

/-- **The closed shell `{lo ≤ ‖x‖}` deforms radially onto the sphere of radius `r₀`**, fixing that
sphere pointwise (for `0 < lo < r₀ ≤ 1`). -/
def closedShellDeform (n : ℕ) (lo r₀ : ℝ) (hlo0 : 0 < lo) (hlo : lo ≤ r₀) (hr₀ : r₀ ≤ 1) :
    C(↥(cellClosedShell n lo) × I, ↥(cellClosedShell n lo)) where
  toFun z := by
    have hy : lo ≤ ‖(((z.1 : ↥(cellClosedShell n lo)) : cellDisk n) : CellVec n)‖ := z.1.2
    have hr : ‖(((z.1 : ↥(cellClosedShell n lo)) : cellDisk n) : CellVec n)‖ ≤ 1 :=
      norm_coe_le_one _
    have ht0 : (0:ℝ) ≤ (z.2 : I) := z.2.2.1
    have ht1 : ((z.2 : I) : ℝ) ≤ 1 := z.2.2.2
    have hpos : 0 < ‖(((z.1 : ↥(cellClosedShell n lo)) : cellDisk n) : CellVec n)‖ :=
      lt_of_lt_of_le hlo0 hy
    have hc : 0 ≤ radCoeff ‖(((z.1 : ↥(cellClosedShell n lo)) : cellDisk n) : CellVec n)‖
        r₀ ((z.2 : I) : ℝ) :=
      radCoeff_nonneg hpos (le_trans (le_of_lt hlo0) hlo) ht0 ht1
    have hval : ‖radCoeff ‖(((z.1 : ↥(cellClosedShell n lo)) : cellDisk n) : CellVec n)‖
        r₀ ((z.2 : I) : ℝ) • (((z.1 : ↥(cellClosedShell n lo)) : cellDisk n) : CellVec n)‖
        = (1 - ((z.2 : I) : ℝ)) *
            ‖(((z.1 : ↥(cellClosedShell n lo)) : cellDisk n) : CellVec n)‖
          + ((z.2 : I) : ℝ) * r₀ := by
      rw [norm_smul, Real.norm_of_nonneg hc, radCoeff_mul (ne_of_gt hpos)]
    refine ⟨⟨radCoeff ‖(((z.1 : ↥(cellClosedShell n lo)) : cellDisk n) : CellVec n)‖
      r₀ ((z.2 : I) : ℝ) • (((z.1 : ↥(cellClosedShell n lo)) : cellDisk n) : CellVec n), ?_⟩, ?_⟩
    · rw [Metric.mem_closedBall, dist_eq_norm, sub_zero, hval]
      nlinarith
    · change lo ≤ ‖radCoeff ‖(((z.1 : ↥(cellClosedShell n lo)) : cellDisk n) : CellVec n)‖
        r₀ ((z.2 : I) : ℝ) • (((z.1 : ↥(cellClosedShell n lo)) : cellDisk n) : CellVec n)‖
      rw [hval]
      nlinarith
  continuous_toFun := by
    refine Continuous.subtype_mk ?_ _
    refine Continuous.subtype_mk ?_ _
    have h2 : Continuous (fun z : ↥(cellClosedShell n lo) × I =>
        (((z.1 : ↥(cellClosedShell n lo)) : cellDisk n) : CellVec n)) :=
      continuous_subtype_val.comp (continuous_subtype_val.comp continuous_fst)
    have h3 : Continuous (fun z : ↥(cellClosedShell n lo) × I => ((z.2 : I) : ℝ)) :=
      continuous_subtype_val.comp continuous_snd
    have hne : ∀ z : ↥(cellClosedShell n lo) × I,
        ‖(((z.1 : ↥(cellClosedShell n lo)) : cellDisk n) : CellVec n)‖ ≠ 0 := fun z =>
      ne_of_gt (lt_of_lt_of_le hlo0 z.1.2)
    have h4 : Continuous (fun z : ↥(cellClosedShell n lo) × I =>
        radCoeff ‖(((z.1 : ↥(cellClosedShell n lo)) : cellDisk n) : CellVec n)‖ r₀
          ((z.2 : I) : ℝ)) := by
      rw [show (fun z : ↥(cellClosedShell n lo) × I =>
          radCoeff ‖(((z.1 : ↥(cellClosedShell n lo)) : cellDisk n) : CellVec n)‖ r₀
            ((z.2 : I) : ℝ))
          = fun z => (((1 - ((z.2 : I) : ℝ)) *
                ‖(((z.1 : ↥(cellClosedShell n lo)) : cellDisk n) : CellVec n)‖
              + ((z.2 : I) : ℝ) * r₀)
            / ‖(((z.1 : ↥(cellClosedShell n lo)) : cellDisk n) : CellVec n)‖) from rfl]
      exact Continuous.div (((continuous_const.sub h3).mul (continuous_norm.comp h2)).add
        (h3.mul continuous_const)) (continuous_norm.comp h2) (fun z => hne z)
    exact h4.smul h2

/-- The value of `closedShellDeform` on a point, in coordinates. -/
theorem closedShellDeform_coe (n : ℕ) (lo r₀ : ℝ) (hlo0 : 0 < lo) (hlo : lo ≤ r₀)
    (hr₀ : r₀ ≤ 1) (z : ↥(cellClosedShell n lo) × I) :
    (((closedShellDeform n lo r₀ hlo0 hlo hr₀ z : ↥(cellClosedShell n lo)) : cellDisk n) :
        CellVec n)
      = radCoeff ‖(((z.1 : ↥(cellClosedShell n lo)) : cellDisk n) : CellVec n)‖ r₀
          ((z.2 : I) : ℝ) • (((z.1 : ↥(cellClosedShell n lo)) : cellDisk n) : CellVec n) := rfl

theorem closedShellDeform_zero (n : ℕ) (lo r₀ : ℝ) (hlo0 : 0 < lo) (hlo : lo ≤ r₀)
    (hr₀ : r₀ ≤ 1) (y : ↥(cellClosedShell n lo)) :
    closedShellDeform n lo r₀ hlo0 hlo hr₀ (y, 0) = y := by
  apply Subtype.ext
  apply Subtype.ext
  rw [closedShellDeform_coe]
  simp only [Prod.fst, Prod.snd]
  change radCoeff ‖((y : cellDisk n) : CellVec n)‖ r₀ (0:ℝ)
    • (((y : cellDisk n)) : CellVec n) = (((y : cellDisk n)) : CellVec n)
  have hne : ‖((y : cellDisk n) : CellVec n)‖ ≠ 0 := ne_of_gt (lt_of_lt_of_le hlo0 y.2)
  rw [radCoeff_zero hne, one_smul]

theorem closedShellDeform_one (n : ℕ) (lo r₀ : ℝ) (hlo0 : 0 < lo) (hlo : lo ≤ r₀)
    (hr₀ : r₀ ≤ 1) (y : ↥(cellClosedShell n lo)) :
    ‖(((closedShellDeform n lo r₀ hlo0 hlo hr₀ (y, 1) : ↥(cellClosedShell n lo)) : cellDisk n) :
        CellVec n)‖ = r₀ := by
  have hpos : 0 < ‖((y : cellDisk n) : CellVec n)‖ := lt_of_lt_of_le hlo0 y.2
  have hc : 0 ≤ radCoeff ‖((y : cellDisk n) : CellVec n)‖ r₀ (1:ℝ) :=
    radCoeff_nonneg hpos (le_trans (le_of_lt hlo0) hlo) (by norm_num) (by norm_num)
  rw [closedShellDeform_coe]
  simp only [Prod.fst, Prod.snd]
  change ‖radCoeff ‖((y : cellDisk n) : CellVec n)‖ r₀ (1:ℝ)
      • (((y : cellDisk n)) : CellVec n)‖ = r₀
  rw [norm_smul, Real.norm_of_nonneg hc, radCoeff_mul (ne_of_gt hpos)]
  ring

theorem closedShellDeform_fix (n : ℕ) (lo r₀ : ℝ) (hlo0 : 0 < lo) (hlo : lo ≤ r₀)
    (hr₀ : r₀ ≤ 1) (y : ↥(cellClosedShell n lo))
    (hy : ‖((y : cellDisk n) : CellVec n)‖ = r₀) (t : I) :
    closedShellDeform n lo r₀ hlo0 hlo hr₀ (y, t) = y := by
  apply Subtype.ext
  apply Subtype.ext
  rw [closedShellDeform_coe]
  simp only [Prod.fst, Prod.snd]
  change radCoeff ‖((y : cellDisk n) : CellVec n)‖ r₀ ((t : I) : ℝ)
    • (((y : cellDisk n)) : CellVec n) = (((y : cellDisk n)) : CellVec n)
  have h1 : radCoeff ‖((y : cellDisk n) : CellVec n)‖ r₀ ((t : I) : ℝ) = 1 := by
    rw [radCoeff, hy]
    have h : (1 - ((t : I) : ℝ)) * r₀ + ((t : I) : ℝ) * r₀ = r₀ := by ring
    rw [h, div_self]
    exact ne_of_gt (lt_of_lt_of_le hlo0 hlo)
  rw [h1, one_smul]

/-- **The closed shell `{7/8 ≤ ‖x‖}` compresses onto the sphere of radius `7/8`.** -/
theorem compressRel_csQ_csS (n : ℕ) :
    ∀ d, CompressRel ↥(cellClosedShell n (7/8))
      (fun x : ↥(cellClosedShell n (7/8)) => ‖((x : cellDisk n) : CellVec n)‖ = 7/8) d :=
  fun d => compressRel_of_deformation
    (A := fun x : ↥(cellClosedShell n (7/8)) => ‖((x : cellDisk n) : CellVec n)‖ = 7/8)
    (closedShellDeform n (7/8) (7/8) (by norm_num) (by norm_num) (by norm_num))
    (closedShellDeform_zero n (7/8) (7/8) (by norm_num) (by norm_num) (by norm_num))
    (fun y => closedShellDeform_one n (7/8) (7/8) (by norm_num) (by norm_num) (by norm_num) y)
    (fun y hy t =>
      closedShellDeform_fix n (7/8) (7/8) (by norm_num) (by norm_num) (by norm_num) y hy t) d

/-- **The closed shell `{7/8 ≤ ‖x‖}` compresses onto the sphere of radius `1`** (the boundary of the
model cell). -/
theorem compressRel_csQ_cellSphere (n : ℕ) :
    ∀ d, CompressRel ↥(cellClosedShell n (7/8))
      (fun x : ↥(cellClosedShell n (7/8)) => ‖((x : cellDisk n) : CellVec n)‖ = 1) d :=
  fun d => compressRel_of_deformation
    (A := fun x : ↥(cellClosedShell n (7/8)) => ‖((x : cellDisk n) : CellVec n)‖ = 1)
    (closedShellDeform n (7/8) 1 (by norm_num) (by norm_num) (by norm_num))
    (closedShellDeform_zero n (7/8) 1 (by norm_num) (by norm_num) (by norm_num))
    (fun y => closedShellDeform_one n (7/8) 1 (by norm_num) (by norm_num) (by norm_num) y)
    (fun y hy t =>
      closedShellDeform_fix n (7/8) 1 (by norm_num) (by norm_num) (by norm_num) y hy t) d

/-! ## The contraction of the whole model cell -/

/-- The linear contraction of the closed model cell onto its centre. -/
def diskDeform (n : ℕ) : C(cellDisk n × I, cellDisk n) where
  toFun z := by
    have ht0 : (0:ℝ) ≤ (z.2 : I) := z.2.2.1
    have ht1 : ((z.2 : I) : ℝ) ≤ 1 := z.2.2.2
    have hy : ‖((z.1 : cellDisk n) : CellVec n)‖ ≤ 1 := norm_coe_le_one _
    have hval : ‖(1 - ((z.2 : I) : ℝ)) • ((z.1 : cellDisk n) : CellVec n)‖
        = |1 - ((z.2 : I) : ℝ)| * ‖((z.1 : cellDisk n) : CellVec n)‖ := norm_smul _ _
    refine ⟨(1 - ((z.2 : I) : ℝ)) • ((z.1 : cellDisk n) : CellVec n), ?_⟩
    rw [Metric.mem_closedBall, dist_eq_norm, sub_zero, hval]
    have h1 : |1 - ((z.2 : I) : ℝ)| ≤ 1 := abs_le.mpr ⟨by linarith, by linarith⟩
    calc |1 - ((z.2 : I) : ℝ)| * ‖((z.1 : cellDisk n) : CellVec n)‖
        ≤ 1 * 1 := mul_le_mul_of_nonneg' h1 hy (norm_nonneg _) (by norm_num)
      _ = 1 := by norm_num
  continuous_toFun := by
    refine Continuous.subtype_mk ?_ _
    have h2 : Continuous (fun z : cellDisk n × I => ((z.1 : cellDisk n) : CellVec n)) :=
      continuous_subtype_val.comp continuous_fst
    have h3 : Continuous (fun z : cellDisk n × I => ((z.2 : I) : ℝ)) :=
      continuous_subtype_val.comp continuous_snd
    exact (continuous_const.sub h3).smul h2

theorem diskDeform_zero (n : ℕ) (y : cellDisk n) : diskDeform n (y, 0) = y := by
  apply Subtype.ext
  show (1 - (0:ℝ)) • ((y : cellDisk n) : CellVec n) = ((y : cellDisk n) : CellVec n)
  rw [sub_zero, one_smul]

theorem diskDeform_one (n : ℕ) (y : cellDisk n) :
    (((diskDeform n (y, 1) : cellDisk n)) : CellVec n) = 0 := by
  show (1 - (1:ℝ)) • ((y : cellDisk n) : CellVec n) = 0
  rw [sub_self, zero_smul]

theorem diskDeform_fix (n : ℕ) (y : cellDisk n) (hy : ((y : cellDisk n) : CellVec n) = 0)
    (t : I) : diskDeform n (y, t) = y := by
  apply Subtype.ext
  show (1 - ((t : I) : ℝ)) • ((y : cellDisk n) : CellVec n) = ((y : cellDisk n) : CellVec n)
  rw [hy, smul_zero]

/-- **The closed model cell compresses onto its centre.** -/
theorem compressRel_cellDisk_centre (n : ℕ) :
    ∀ d, CompressRel (cellDisk n) {y : cellDisk n | ((y : cellDisk n) : CellVec n) = 0} d :=
  fun d => compressRel_of_deformation
    (A := {y : cellDisk n | ((y : cellDisk n) : CellVec n) = 0})
    (diskDeform n) (diskDeform_zero n)
    (fun y => by
      show ((diskDeform n) (y, 1) : cellDisk n)
        ∈ {y : cellDisk n | ((y : cellDisk n) : CellVec n) = 0}
      exact diskDeform_one n y)
    (fun y hy t => diskDeform_fix n y hy t) d

end

end Work.Serre.SPC
