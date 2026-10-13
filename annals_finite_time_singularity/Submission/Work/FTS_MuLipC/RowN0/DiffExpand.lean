/-
# `Submission/Work/FTS_MuLipC/RowN0/DiffExpand.lean` — the telescoping of the difference of `N₀`

The pointwise identity `Sn0_sub_expand` and the elementary angular/weight bounds used by the
difference row `Work.FTS_MuLipC.RowN0.diffRow0`.  See `diffRow0.lean` for the route.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.FTS_MuLipC.Defs
import Submission.Work.FTS.GalFields.RHS.SharpAux.Core
import Submission.Work.FTS.StrongEps.EComparison.EllPkgClsSliceAux
import Submission.Work.FTS.NonlinRows.Rl1.splitOpen
import Submission.Work.FTS.ClassC.A1

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS_MuLipC.RowN0

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false
set_option maxHeartbeats 1600000

local notation "N0" => Work.Construction.N0
local notation "L12" => Work.Construction.L12
local notation "Fstar" => Work.Construction.Fstar
local notation "Ftot" => Work.Construction.Ftot
local notation "Dz" => Work.Spaces.Dz
local notation "Dth" => Work.Spaces.Dth
local notation "c2m" => Work.Construction.c2m
local notation "Sn0" => Work.FTS_MuLipC.Sn0
local notation "Hk" => Work.Spaces.HkIntegrand

/-! ## The pointwise telescoping of the difference -/

/-- **The pointwise telescoping of `Sn0` along the difference `d = f - f'`.**  On the open
quadrant the difference of the two fields splits into three groups of three terms each:
`D₁ = L₁₂(f)(z)·E₁/α`, `D₂ = L₁₂(d)(z)·E₂/α` and `D₃ = L₁₂(d)(z)·E₃/α − c₂·L₁₂(F_*)(z)·D_zd`,
where `E₁ = d + (3/2)D_θd − αc₂D_zd` and `E₂`, `E₃` are the analogues for `f'` and `F_*`. -/
theorem Sn0_sub_expand {α : ℝ} {f f' d : Fn}
    (hf : Work.FTS.EllipticEst.SmoothOpen f) (hf' : Work.FTS.EllipticEst.SmoothOpen f')
    (hd : Work.FTS.EllipticEst.SmoothOpen d)
    (hmf : Work.Spaces.HkMem α 4 f) (hmf' : Work.Spaces.HkMem α 4 f')
    (hmd : Work.Spaces.HkMem α 4 d)
    (hddef : ∀ z θ, d z θ = f z θ - f' z θ) :
    ∀ z θ : ℝ, 0 < z → 0 < θ → θ < π / 2 →
      Sn0 α f z θ - Sn0 α f' z θ
        = (L12 f z) * (d z θ / α + (3 / (2 * α)) * Dth d z θ - c2m θ * Dz d z θ)
          + (L12 d z) * (f' z θ / α + (3 / (2 * α)) * Dth f' z θ - c2m θ * Dz f' z θ)
          + (L12 d z) * ((3 / (2 * α)) * Dth (Fstar α) z θ - c2m θ * Dz (Fstar α) z θ)
          - c2m θ * (L12 (Fstar α) z) * Dz d z θ := by
  intro z θ hz h1 h2
  have hF : Work.FTS.EllipticEst.SmoothOpen (Fstar α) :=
    Work.FTS.OpenPkg.smoothOpen_of_smoothQuad (Work.FTS.LocData.SmoothQuad_Fstar α)
  have hL : L12 f z = L12 d z + L12 f' z :=
    Work.FTS.GalFields.RHS.Sharp.L12_sub_ge0 hf hf' hd hmf hmf' hmd hddef hz.le
  have hpth : Work.Spaces.pth (Ftot α f) z θ
      = Work.Spaces.pth (Fstar α) z θ + Work.Spaces.pth f z θ :=
    Work.FTS.NonlinRows.Rl1.openSlice_pth_add hF hf hz ⟨h1, h2⟩
  have hpth' : Work.Spaces.pth (Ftot α f') z θ
      = Work.Spaces.pth (Fstar α) z θ + Work.Spaces.pth f' z θ :=
    Work.FTS.NonlinRows.Rl1.openSlice_pth_add hF hf' hz ⟨h1, h2⟩
  have hDz : Dz (Ftot α f) z θ = Dz (Fstar α) z θ + Dz f z θ :=
    Work.FTS.Nonlinear.Pieces.Dz_add_of_diff
      (Work.FTS.NonlinRows.Rl1.openSlice_pz_add hF hf hz ⟨h1, h2⟩)
  have hDz' : Dz (Ftot α f') z θ = Dz (Fstar α) z θ + Dz f' z θ :=
    Work.FTS.Nonlinear.Pieces.Dz_add_of_diff
      (Work.FTS.NonlinRows.Rl1.openSlice_pz_add hF hf' hz ⟨h1, h2⟩)
  have hpthd : Work.Spaces.pth d z θ = Work.Spaces.pth f z θ - Work.Spaces.pth f' z θ := by
    rw [Work.FTS.PhiStar.CoreAux.pth_congr_Q0 (f := d) (g := fun z θ => f z θ - f' z θ)
      (fun z θ _ _ _ => hddef z θ) z θ hz h1 h2]
    exact Work.FTS.StrongEps.EComparison.pth_sub hf hf' hz h1 h2
  have hpzd : Work.Spaces.pz d z θ = Work.Spaces.pz f z θ - Work.Spaces.pz f' z θ := by
    rw [Work.FTS.GalFields.RHS.Sharp.pz_congr_Q0 (f := d) (g := fun z θ => f z θ - f' z θ)
      (fun z θ _ _ _ => hddef z θ) z θ hz h1 h2]
    exact Work.FTS.StrongEps.EComparison.pz_sub hf hf' hz h1 h2
  have hDzd : Dz d z θ = Dz f z θ - Dz f' z θ := by
    simp only [Work.Spaces.Dz]
    rw [hpzd]
    ring
  simp only [Work.FTS_MuLipC.Sn0, Work.Construction.N0, Work.Construction.Ftot,
    Work.Construction.s2, Work.Spaces.Dth]
  rw [hpth, hpth', hDz, hDz', hL, hpthd, hDzd, hddef z θ]
  ring

/-! ## Elementary bounds -/

/-- The identity `(r/(1+r)²)²·w(r) = (1/(1+r))²` for `r > 0`. -/
theorem sq_div_shape_eq {r : ℝ} (hr : 0 < r) :
    (r / (1 + r) ^ 2) ^ 2 * Work.Spaces.w r = (1 / (1 + r)) ^ 2 := by
  rw [Work.Spaces.w]
  field_simp

/-- `w(r) ≥ 1` for `r > 0`. -/
theorem one_le_w {r : ℝ} (hr : 0 < r) : 1 ≤ Work.Spaces.w r := by
  rw [Work.Spaces.w, one_le_div (by positivity)]
  nlinarith

/-- `w(r) > 0` for `r > 0`. -/
theorem w_pos {r : ℝ} (hr : 0 < r) : 0 < Work.Spaces.w r :=
  lt_of_lt_of_le one_pos (one_le_w hr)

/-- `|cos 2θ - sin²θ| ≤ 2`. -/
theorem abs_c2m_le (θ : ℝ) : |c2m θ| ≤ 2 := by
  have hs1 : Real.sin θ ^ 2 ≤ 1 := by
    nlinarith [Real.sin_le_one θ, Real.neg_one_le_sin θ, sq_nonneg (Real.sin θ)]
  rw [Work.Construction.c2m, abs_le]
  constructor
  · nlinarith [Real.neg_one_le_cos (2 * θ), hs1]
  · nlinarith [Real.cos_le_one (2 * θ), sq_nonneg (Real.sin θ)]

/-- `|K θ| ≤ 3` on `Iθ`. -/
theorem abs_K_le (θ : ℝ) : |Work.Spaces.K θ| ≤ 3 := by
  have h1 : |Real.sin θ| ≤ 1 := abs_le.mpr ⟨Real.neg_one_le_sin θ, Real.sin_le_one θ⟩
  have h2 : |Real.cos θ| ≤ 1 := abs_le.mpr ⟨Real.neg_one_le_cos θ, Real.cos_le_one θ⟩
  have h3 : |Real.cos θ * Real.cos θ| ≤ 1 := by
    nlinarith [h2, abs_nonneg (Real.cos θ), abs_mul (Real.cos θ) (Real.cos θ)]
  have hK : Work.Spaces.K θ = 3 * Real.sin θ * (Real.cos θ * Real.cos θ) := by
    rw [Work.Spaces.K]; ring
  rw [hK, abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 3)]
  nlinarith [h1, h3, abs_nonneg (Real.sin θ), abs_nonneg (Real.cos θ * Real.cos θ)]

/-- The `θ`-slices of the `L₁₂`-density of a square-integrable slice are integrable. -/
theorem integrableOn_K_mul_div {X : Fn} {r : ℝ} (hr : 0 < r)
    (haesm : MeasureTheory.AEStronglyMeasurable (fun θ => X r θ)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ))
    (hsq : MeasureTheory.IntegrableOn (fun θ => (X r θ) ^ 2) Work.Spaces.Iθ) :
    MeasureTheory.IntegrableOn (fun θ => Work.Spaces.K θ * X r θ / r) Work.Spaces.Iθ := by
  have hK : Continuous (fun θ : ℝ => Work.Spaces.K θ) := by
    change Continuous fun θ : ℝ => 3 * Real.sin θ * Real.cos θ ^ 2
    fun_prop
  have haesm2 : MeasureTheory.AEStronglyMeasurable
      (fun θ => Work.Spaces.K θ * X r θ / r) (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
    ((((hK.aemeasurable).mul haesm.aemeasurable)).div_const r).aestronglyMeasurable
  have hgint : MeasureTheory.IntegrableOn
      (fun θ => (3 / (2 * r)) * ((X r θ) ^ 2 + 1)) Work.Spaces.Iθ := by
    refine (hsq.add (MeasureTheory.integrableOn_const ?_)).const_mul ((3 : ℝ) / (2 * r))
    rw [Work.Spaces.Iθ, Real.volume_Icc]
    exact ENNReal.ofReal_ne_top
  refine MeasureTheory.Integrable.mono' hgint haesm2 ?_
  filter_upwards with θ
  rw [Real.norm_eq_abs]
  have hK3 := abs_K_le θ
  have h2 : |X r θ| ≤ ((X r θ) ^ 2 + 1) / 2 := by
    nlinarith [abs_nonneg (X r θ), sq_abs (X r θ), sq_nonneg (|X r θ| - 1)]
  have h1 : |Work.Spaces.K θ| * |X r θ| ≤ 3 * (((X r θ) ^ 2 + 1) / 2) :=
    mul_le_mul hK3 h2 (abs_nonneg _) (by norm_num)
  have h3 : (3 / (2 * r)) * ((X r θ) ^ 2 + 1) = 3 * (((X r θ) ^ 2 + 1) / 2) / r := by
    field_simp
  rw [abs_div, abs_mul, abs_of_pos hr, h3]
  exact div_le_div_of_nonneg_right h1 hr.le

end Work.FTS_MuLipC.RowN0
