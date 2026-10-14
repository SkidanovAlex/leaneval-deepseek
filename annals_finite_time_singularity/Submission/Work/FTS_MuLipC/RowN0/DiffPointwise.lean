import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS.Nonlinear.Pieces.rowsAux
import Submission.Work.FTS_MuLamOK.Rows.Rl2Open
import Submission.Work.FTS_RegExport.RXR1.slice_diff_weighted

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

local notation "L12" => Work.Construction.L12
local notation "Fstar" => Work.Construction.Fstar
local notation "Dz" => Work.Spaces.Dz
local notation "Dth" => Work.Spaces.Dth
local notation "c2m" => Work.Construction.c2m
local notation "Sn0" => Work.FTS_MuLipC.Sn0
local notation "Xn" => Work.FTS.Nonlin.Xn
local notation "Hk" => Work.Spaces.HkIntegrand

/-- The pointwise majorant of the Hardy-weighted square of the difference field. -/
def DiffMaj (α C₀ Xd : ℝ) (d f' : Fn) (r θ : ℝ) : ℝ :=
  3 * (((351 : ℝ) / 4 * C₀ ^ 2 * α ^ 2 + 108 * C₀ ^ 2 * α ^ 4 + 32 * α ^ 2)
        * Hk α 4 d r θ
      + ((351 : ℝ) / 4 * (Xd ^ 2 / α ^ 2) + 108 * Xd ^ 2) * Hk α 4 f' r θ
      + 352800 * α ^ 2 * Xd ^ 2 * (1 / (1 + r)) ^ 2)

/-- The first group: `L₁₂(f)(r)·E₁/α`. -/
theorem diffGroup1_le {α C₀ : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) (hC₀ : 0 ≤ C₀)
    {f d : Fn} (hf : Work.FTS.EllipticEst.SmoothOpen f) (hmf : Work.Spaces.HkMem α 4 f)
    (hXf : Xn α f ≤ C₀ * α ^ 2) {r θ : ℝ} (hr : 0 < r)
    (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    ((L12 f r) * (d r θ / α + (3 / (2 * α)) * Dth d r θ - c2m θ * Dz d r θ)) ^ 2
        * Work.Spaces.w r
      ≤ ((351 : ℝ) / 4 * C₀ ^ 2 * α ^ 2 + 108 * C₀ ^ 2 * α ^ 4) * Hk α 4 d r θ := by
  have hLf : |L12 f r| ≤ 3 * C₀ * α ^ 2 := by
    have h := Work.FTS.StrongPersist.H6Pair6Aux.l12_supAbs_open hα hα1 hf hmf r hr.le
    have h2 : 3 * Xn α f ≤ 3 * (C₀ * α ^ 2) := by linarith
    linarith [h, h2]
  have hw1 : 1 ≤ Work.Spaces.w r := one_le_w hr
  have hw0 : 0 ≤ Work.Spaces.w r := le_trans zero_le_one hw1
  have hslot0w : (d r θ) ^ 2 * Work.Spaces.w r ≤ Hk α 4 d r θ := by
    have h := Work.FTS.Nonlinear.Pieces.g_sq_mul_w_sq_le_HkIntegrand α d hr hθ
    have hw2 : (d r θ) ^ 2 * Work.Spaces.w r
        ≤ (d r θ) ^ 2 * Work.Spaces.w r * Work.Spaces.w r := by
      have := mul_le_mul_of_nonneg_left hw1 (mul_nonneg (sq_nonneg (d r θ)) hw0)
      linarith [this]
    linarith [h, hw2]
  have hslot1w : (Dth d r θ) ^ 2 * Work.Spaces.w r ≤ Hk α 4 d r θ :=
    Work.FTS.Nonlinear.Pieces.dth_sq_mul_w_le_HkIntegrand α d hα hr hθ
  have hslot2w : (Dz d r θ) ^ 2 * Work.Spaces.w r ≤ Hk α 4 d r θ :=
    Work.FTS.Nonlinear.Pieces.dz_sq_mul_w_le_HkIntegrand α d hr hθ
  have hslot1 : (Dth d r θ) ^ 2 ≤ Hk α 4 d r θ := by nlinarith [hslot1w, hw1]
  have hslot2 : (Dz d r θ) ^ 2 ≤ Hk α 4 d r θ := by nlinarith [hslot2w, hw1]
  have hc2 : (c2m θ) ^ 2 ≤ 4 := by
    nlinarith [abs_c2m_le θ, abs_nonneg (c2m θ), sq_abs (c2m θ)]
  set E : ℝ := d r θ + (3 / 2) * Dth d r θ - α * c2m θ * Dz d r θ with hE
  have hEsq : E ^ 2 ≤ 3 * ((d r θ) ^ 2 + (9 / 4) * (Dth d r θ) ^ 2
      + α ^ 2 * (c2m θ) ^ 2 * (Dz d r θ) ^ 2) := by
    have h := sq_nonneg (d r θ - (3 / 2) * Dth d r θ)
    have h2 := sq_nonneg ((3 / 2) * Dth d r θ + α * c2m θ * Dz d r θ)
    have h3 := sq_nonneg (α * c2m θ * Dz d r θ + d r θ)
    rw [hE]
    nlinarith [h, h2, h3]
  have hEsqW : E ^ 2 * Work.Spaces.w r
      ≤ 3 * (Hk α 4 d r θ + (9 / 4) * Hk α 4 d r θ + 4 * α ^ 2 * Hk α 4 d r θ) := by
    have h3 : E ^ 2 * Work.Spaces.w r
        ≤ 3 * ((d r θ) ^ 2 * Work.Spaces.w r
            + (9 / 4) * ((Dth d r θ) ^ 2 * Work.Spaces.w r)
            + α ^ 2 * (c2m θ) ^ 2 * ((Dz d r θ) ^ 2 * Work.Spaces.w r)) := by
      have h4 := mul_le_mul_of_nonneg_right hEsq hw0
      nlinarith [h4]
    have hb0 : (d r θ) ^ 2 * Work.Spaces.w r ≤ Hk α 4 d r θ := hslot0w
    have hb1 : (9 / 4) * ((Dth d r θ) ^ 2 * Work.Spaces.w r)
        ≤ (9 / 4) * Hk α 4 d r θ := mul_le_mul_of_nonneg_left hslot1w (by norm_num)
    have hb2 : α ^ 2 * (c2m θ) ^ 2 * ((Dz d r θ) ^ 2 * Work.Spaces.w r)
        ≤ 4 * α ^ 2 * Hk α 4 d r θ := by
      have h2 : α ^ 2 * (c2m θ) ^ 2 ≤ 4 * α ^ 2 := by nlinarith [hc2, sq_nonneg α]
      calc α ^ 2 * (c2m θ) ^ 2 * ((Dz d r θ) ^ 2 * Work.Spaces.w r)
          ≤ (4 * α ^ 2) * ((Dz d r θ) ^ 2 * Work.Spaces.w r) :=
            mul_le_mul_of_nonneg_right h2 (by positivity)
        _ ≤ (4 * α ^ 2) * Hk α 4 d r θ :=
            mul_le_mul_of_nonneg_left hslot2w (by positivity)
        _ = 4 * α ^ 2 * Hk α 4 d r θ := by ring
    linarith [h3, hb0, hb1, hb2]
  have hD1 : (L12 f r) * (d r θ / α + (3 / (2 * α)) * Dth d r θ - c2m θ * Dz d r θ)
      = (L12 f r) * E / α := by
    rw [hE]; first | (field_simp; ring) | field_simp
  rw [hD1]
  have hfac : ((L12 f r) * E / α) ^ 2 * Work.Spaces.w r
      = ((L12 f r) ^ 2 / α ^ 2) * (E ^ 2 * Work.Spaces.w r) := by
    first | (field_simp; ring) | field_simp
  rw [hfac]
  have hLfsq : (L12 f r) ^ 2 / α ^ 2 ≤ 9 * C₀ ^ 2 * α ^ 2 := by
    have h2 : (L12 f r) ^ 2 ≤ (3 * C₀ * α ^ 2) ^ 2 := by
      nlinarith [hLf, abs_nonneg (L12 f r), sq_abs (L12 f r)]
    calc (L12 f r) ^ 2 / α ^ 2 ≤ (3 * C₀ * α ^ 2) ^ 2 / α ^ 2 :=
          div_le_div_of_nonneg_right h2 (sq_nonneg α)
      _ = 9 * C₀ ^ 2 * α ^ 2 := by first | (field_simp; ring) | field_simp
  have hprod : ((L12 f r) ^ 2 / α ^ 2) * (E ^ 2 * Work.Spaces.w r)
      ≤ (9 * C₀ ^ 2 * α ^ 2)
        * (3 * (Hk α 4 d r θ + (9 / 4) * Hk α 4 d r θ + 4 * α ^ 2 * Hk α 4 d r θ)) :=
    mul_le_mul hLfsq hEsqW (by positivity) (by positivity)
  calc ((L12 f r) ^ 2 / α ^ 2) * (E ^ 2 * Work.Spaces.w r)
      ≤ (9 * C₀ ^ 2 * α ^ 2)
        * (3 * (Hk α 4 d r θ + (9 / 4) * Hk α 4 d r θ + 4 * α ^ 2 * Hk α 4 d r θ)) := hprod
    _ = ((351 : ℝ) / 4 * C₀ ^ 2 * α ^ 2 + 108 * C₀ ^ 2 * α ^ 4) * Hk α 4 d r θ := by ring

/-- The second group: `L₁₂(d)(r)·E₂/α`. -/
theorem diffGroup2_le {α Xd : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) (hXd : 0 ≤ Xd)
    {d f' : Fn} (hd : Work.FTS.EllipticEst.SmoothOpen d) (hmd : Work.Spaces.HkMem α 4 d)
    (hXdd : Xn α d = Xd) {r θ : ℝ} (hr : 0 < r) (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    ((L12 d r) * (f' r θ / α + (3 / (2 * α)) * Dth f' r θ - c2m θ * Dz f' r θ)) ^ 2
        * Work.Spaces.w r
      ≤ ((351 : ℝ) / 4 * (Xd ^ 2 / α ^ 2) + 108 * Xd ^ 2) * Hk α 4 f' r θ := by
  have hLd : |L12 d r| ≤ 3 * Xd := by
    have h := Work.FTS.StrongPersist.H6Pair6Aux.l12_supAbs_open hα hα1 hd hmd r hr.le
    rw [hXdd] at h
    exact h
  have hw1 : 1 ≤ Work.Spaces.w r := one_le_w hr
  have hw0 : 0 ≤ Work.Spaces.w r := le_trans zero_le_one hw1
  have hslot0w : (f' r θ) ^ 2 * Work.Spaces.w r ≤ Hk α 4 f' r θ := by
    have h := Work.FTS.Nonlinear.Pieces.g_sq_mul_w_sq_le_HkIntegrand α f' hr hθ
    have hw2 : (f' r θ) ^ 2 * Work.Spaces.w r
        ≤ (f' r θ) ^ 2 * Work.Spaces.w r * Work.Spaces.w r := by
      have := mul_le_mul_of_nonneg_left hw1 (mul_nonneg (sq_nonneg (f' r θ)) hw0)
      linarith [this]
    linarith [h, hw2]
  have hslot1w : (Dth f' r θ) ^ 2 * Work.Spaces.w r ≤ Hk α 4 f' r θ :=
    Work.FTS.Nonlinear.Pieces.dth_sq_mul_w_le_HkIntegrand α f' hα hr hθ
  have hslot2w : (Dz f' r θ) ^ 2 * Work.Spaces.w r ≤ Hk α 4 f' r θ :=
    Work.FTS.Nonlinear.Pieces.dz_sq_mul_w_le_HkIntegrand α f' hr hθ
  have hslot1 : (Dth f' r θ) ^ 2 ≤ Hk α 4 f' r θ := by nlinarith [hslot1w, hw1]
  have hslot2 : (Dz f' r θ) ^ 2 ≤ Hk α 4 f' r θ := by nlinarith [hslot2w, hw1]
  have hc2 : (c2m θ) ^ 2 ≤ 4 := by
    nlinarith [abs_c2m_le θ, abs_nonneg (c2m θ), sq_abs (c2m θ)]
  set E : ℝ := f' r θ + (3 / 2) * Dth f' r θ - α * c2m θ * Dz f' r θ with hE
  have hEsq : E ^ 2 ≤ 3 * ((f' r θ) ^ 2 + (9 / 4) * (Dth f' r θ) ^ 2
      + α ^ 2 * (c2m θ) ^ 2 * (Dz f' r θ) ^ 2) := by
    have h := sq_nonneg (f' r θ - (3 / 2) * Dth f' r θ)
    have h2 := sq_nonneg ((3 / 2) * Dth f' r θ + α * c2m θ * Dz f' r θ)
    have h3 := sq_nonneg (α * c2m θ * Dz f' r θ + f' r θ)
    rw [hE]
    nlinarith [h, h2, h3]
  have hEsqW : E ^ 2 * Work.Spaces.w r
      ≤ 3 * (Hk α 4 f' r θ + (9 / 4) * Hk α 4 f' r θ + 4 * α ^ 2 * Hk α 4 f' r θ) := by
    have h3 : E ^ 2 * Work.Spaces.w r
        ≤ 3 * ((f' r θ) ^ 2 * Work.Spaces.w r
            + (9 / 4) * ((Dth f' r θ) ^ 2 * Work.Spaces.w r)
            + α ^ 2 * (c2m θ) ^ 2 * ((Dz f' r θ) ^ 2 * Work.Spaces.w r)) := by
      have h4 := mul_le_mul_of_nonneg_right hEsq hw0
      nlinarith [h4]
    have hb0 : (f' r θ) ^ 2 * Work.Spaces.w r ≤ Hk α 4 f' r θ := hslot0w
    have hb1 : (9 / 4) * ((Dth f' r θ) ^ 2 * Work.Spaces.w r)
        ≤ (9 / 4) * Hk α 4 f' r θ := mul_le_mul_of_nonneg_left hslot1w (by norm_num)
    have hb2 : α ^ 2 * (c2m θ) ^ 2 * ((Dz f' r θ) ^ 2 * Work.Spaces.w r)
        ≤ 4 * α ^ 2 * Hk α 4 f' r θ := by
      have h2 : α ^ 2 * (c2m θ) ^ 2 ≤ 4 * α ^ 2 := by nlinarith [hc2, sq_nonneg α]
      calc α ^ 2 * (c2m θ) ^ 2 * ((Dz f' r θ) ^ 2 * Work.Spaces.w r)
          ≤ (4 * α ^ 2) * ((Dz f' r θ) ^ 2 * Work.Spaces.w r) :=
            mul_le_mul_of_nonneg_right h2 (by positivity)
        _ ≤ (4 * α ^ 2) * Hk α 4 f' r θ :=
            mul_le_mul_of_nonneg_left hslot2w (by positivity)
        _ = 4 * α ^ 2 * Hk α 4 f' r θ := by ring
    linarith [h3, hb0, hb1, hb2]
  have hD1 : (L12 d r) * (f' r θ / α + (3 / (2 * α)) * Dth f' r θ - c2m θ * Dz f' r θ)
      = (L12 d r) * E / α := by
    rw [hE]; first | (field_simp; ring) | field_simp
  rw [hD1]
  have hfac : ((L12 d r) * E / α) ^ 2 * Work.Spaces.w r
      = ((L12 d r) ^ 2 / α ^ 2) * (E ^ 2 * Work.Spaces.w r) := by
    first | (field_simp; ring) | field_simp
  rw [hfac]
  have hLfsq : (L12 d r) ^ 2 / α ^ 2 ≤ 9 * Xd ^ 2 / α ^ 2 := by
    have h2 : (L12 d r) ^ 2 ≤ (3 * Xd) ^ 2 := by
      nlinarith [hLd, abs_nonneg (L12 d r), sq_abs (L12 d r)]
    calc (L12 d r) ^ 2 / α ^ 2 ≤ (3 * Xd) ^ 2 / α ^ 2 :=
          div_le_div_of_nonneg_right h2 (sq_nonneg α)
      _ = 9 * Xd ^ 2 / α ^ 2 := by ring
  have hprod : ((L12 d r) ^ 2 / α ^ 2) * (E ^ 2 * Work.Spaces.w r)
      ≤ (9 * Xd ^ 2 / α ^ 2)
        * (3 * (Hk α 4 f' r θ + (9 / 4) * Hk α 4 f' r θ + 4 * α ^ 2 * Hk α 4 f' r θ)) :=
    mul_le_mul hLfsq hEsqW (by positivity) (by positivity)
  calc ((L12 d r) ^ 2 / α ^ 2) * (E ^ 2 * Work.Spaces.w r)
      ≤ (9 * Xd ^ 2 / α ^ 2)
        * (3 * (Hk α 4 f' r θ + (9 / 4) * Hk α 4 f' r θ + 4 * α ^ 2 * Hk α 4 f' r θ)) := hprod
    _ = ((351 : ℝ) / 4 * (Xd ^ 2 / α ^ 2) + 108 * Xd ^ 2) * Hk α 4 f' r θ := by
        first | (field_simp; ring) | field_simp

/-- The third group: the `F_*`-terms. -/
theorem diffGroup3_le {α Xd : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) (hXd : 0 ≤ Xd)
    {d : Fn} (hd : Work.FTS.EllipticEst.SmoothOpen d) (hmd : Work.Spaces.HkMem α 4 d)
    (hXdd : Xn α d = Xd) {r θ : ℝ} (hr : 0 < r) (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    ((L12 d r) * ((3 / (2 * α)) * Dth (Fstar α) r θ - c2m θ * Dz (Fstar α) r θ)
        - c2m θ * (L12 (Fstar α) r) * Dz d r θ) ^ 2 * Work.Spaces.w r
      ≤ 352800 * α ^ 2 * Xd ^ 2 * (1 / (1 + r)) ^ 2 + 32 * α ^ 2 * Hk α 4 d r θ := by
  have hLd : |L12 d r| ≤ 3 * Xd := by
    have h := Work.FTS.StrongPersist.H6Pair6Aux.l12_supAbs_open hα hα1 hd hmd r hr.le
    rw [hXdd] at h
    exact h
  obtain ⟨-, hDthF, hDzF⟩ := Work.FTS.Nonlinear.Pieces.Fstar_shape (α := α) hα hα1
  have hDthF' := hDthF r hr.le θ (Set.Ioo_subset_Icc_self hθ)
  have hDzF' := hDzF r hr.le θ (Set.Ioo_subset_Icc_self hθ)
  have hLF : |L12 (Fstar α) r| ≤ 2 * α := by
    rw [Work.Construction.L12_Fstar_eq hα hα1 hr.le]
    have h1r : 0 < 1 + r := by linarith
    rw [abs_div, abs_of_pos h1r, abs_of_pos (by positivity : (0 : ℝ) < 2 * α)]
    rw [div_le_iff₀ h1r]
    nlinarith [hα]
  have hw1 : 1 ≤ Work.Spaces.w r := one_le_w hr
  have hw0 : 0 ≤ Work.Spaces.w r := le_trans zero_le_one hw1
  have hslot2w : (Dz d r θ) ^ 2 * Work.Spaces.w r ≤ Hk α 4 d r θ :=
    Work.FTS.Nonlinear.Pieces.dz_sq_mul_w_le_HkIntegrand α d hr hθ
  have hslot2 : (Dz d r θ) ^ 2 ≤ Hk α 4 d r θ := by nlinarith [hslot2w, hw1]
  have hc2 : (c2m θ) ^ 2 ≤ 4 := by
    nlinarith [abs_c2m_le θ, abs_nonneg (c2m θ), sq_abs (c2m θ)]
  set E : ℝ := (3 / 2) * Dth (Fstar α) r θ - α * c2m θ * Dz (Fstar α) r θ with hE
  have hEsq : E ^ 2 ≤ (140 * α ^ 2 * (r / (1 + r) ^ 2)) ^ 2 := by
    have h1 : |Dth (Fstar α) r θ| ≤ 40 * α ^ 2 * (r / (1 + r) ^ 2) := hDthF'
    have h2 : |Dz (Fstar α) r θ| ≤ 40 * α * (r / (1 + r) ^ 2) := hDzF'
    rw [hE]
    have h3 : |(3 / 2) * Dth (Fstar α) r θ - α * c2m θ * Dz (Fstar α) r θ|
        ≤ 140 * α ^ 2 * (r / (1 + r) ^ 2) := by
      have h4 : |α * c2m θ * Dz (Fstar α) r θ| ≤ α * 2 * (40 * α * (r / (1 + r) ^ 2)) := by
        rw [abs_mul, abs_mul, abs_of_nonneg hα.le]
        refine mul_le_mul (mul_le_mul_of_nonneg_left (abs_c2m_le θ) hα.le) h2 (abs_nonneg _)
          (by positivity)
      have h5 : |(3 / 2) * Dth (Fstar α) r θ|
          ≤ (3 / 2) * (40 * α ^ 2 * (r / (1 + r) ^ 2)) := by
        rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 3 / 2)]
        exact mul_le_mul_of_nonneg_left h1 (by norm_num)
      have h6 : |(3 / 2) * Dth (Fstar α) r θ - α * c2m θ * Dz (Fstar α) r θ|
          ≤ |(3 / 2) * Dth (Fstar α) r θ| + |α * c2m θ * Dz (Fstar α) r θ| := by
        simpa only [sub_eq_add_neg, abs_neg] using
          abs_add_le ((3 / 2) * Dth (Fstar α) r θ) (-(α * c2m θ * Dz (Fstar α) r θ))
      have h7 : α * 2 * (40 * α * (r / (1 + r) ^ 2)) = 80 * α ^ 2 * (r / (1 + r) ^ 2) := by ring
      have h8 : (3 / 2) * (40 * α ^ 2 * (r / (1 + r) ^ 2))
          = 60 * α ^ 2 * (r / (1 + r) ^ 2) := by ring
      linarith [h6, h4, h5, h7.le, h7.ge, h8.le, h8.ge]
    have h := abs_nonneg ((3 / 2) * Dth (Fstar α) r θ - α * c2m θ * Dz (Fstar α) r θ)
    have hsq := sq_abs ((3 / 2) * Dth (Fstar α) r θ - α * c2m θ * Dz (Fstar α) r θ)
    nlinarith [h3, hsq, h]
  have hD3 : (L12 d r) * ((3 / (2 * α)) * Dth (Fstar α) r θ - c2m θ * Dz (Fstar α) r θ)
        - c2m θ * (L12 (Fstar α) r) * Dz d r θ
      = (L12 d r) * E / α - c2m θ * (L12 (Fstar α) r) * Dz d r θ := by
    rw [hE]; first | (field_simp; ring) | field_simp
  rw [hD3]
  have hsq2 : ((L12 d r) * E / α - c2m θ * (L12 (Fstar α) r) * Dz d r θ) ^ 2
      ≤ 2 * (((L12 d r) * E / α) ^ 2 + (c2m θ * (L12 (Fstar α) r) * Dz d r θ) ^ 2) := by
    nlinarith [sq_nonneg ((L12 d r) * E / α + c2m θ * (L12 (Fstar α) r) * Dz d r θ)]
  have hstep := mul_le_mul_of_nonneg_right hsq2 hw0
  have hA : ((L12 d r) * E / α) ^ 2 * Work.Spaces.w r
      ≤ 176400 * α ^ 2 * Xd ^ 2 * (1 / (1 + r)) ^ 2 := by
    have hfac : ((L12 d r) * E / α) ^ 2 * Work.Spaces.w r
        = ((L12 d r) ^ 2 / α ^ 2) * (E ^ 2 * Work.Spaces.w r) := by
            first | (field_simp; ring) | field_simp
    rw [hfac]
    have hL2 : (L12 d r) ^ 2 / α ^ 2 ≤ 9 * Xd ^ 2 / α ^ 2 := by
      have h2 : (L12 d r) ^ 2 ≤ (3 * Xd) ^ 2 := by
        nlinarith [hLd, abs_nonneg (L12 d r), sq_abs (L12 d r)]
      calc (L12 d r) ^ 2 / α ^ 2 ≤ (3 * Xd) ^ 2 / α ^ 2 :=
            div_le_div_of_nonneg_right h2 (sq_nonneg α)
        _ = 9 * Xd ^ 2 / α ^ 2 := by ring
    have hEw : E ^ 2 * Work.Spaces.w r
        ≤ (140 * α ^ 2 * (r / (1 + r) ^ 2)) ^ 2 * Work.Spaces.w r :=
      mul_le_mul_of_nonneg_right hEsq hw0
    have hEw' : (140 * α ^ 2 * (r / (1 + r) ^ 2)) ^ 2 * Work.Spaces.w r
        = (140 * α ^ 2) ^ 2 * (1 / (1 + r)) ^ 2 := by
      rw [show (140 * α ^ 2 * (r / (1 + r) ^ 2)) ^ 2 * Work.Spaces.w r
          = (140 * α ^ 2) ^ 2 * ((r / (1 + r) ^ 2) ^ 2 * Work.Spaces.w r) from by ring,
        sq_div_shape_eq hr]
    calc ((L12 d r) ^ 2 / α ^ 2) * (E ^ 2 * Work.Spaces.w r)
        ≤ (9 * Xd ^ 2 / α ^ 2) * ((140 * α ^ 2) ^ 2 * (1 / (1 + r)) ^ 2) := by
          refine mul_le_mul hL2 ?_ (by positivity) (by positivity)
          linarith [hEw, hEw'.le, hEw'.ge]
      _ = 176400 * α ^ 2 * Xd ^ 2 * (1 / (1 + r)) ^ 2 := by
          first | (field_simp; ring) | field_simp
  have hB : (c2m θ * (L12 (Fstar α) r) * Dz d r θ) ^ 2 * Work.Spaces.w r
      ≤ 16 * α ^ 2 * Hk α 4 d r θ := by
    have hfac : (c2m θ * (L12 (Fstar α) r) * Dz d r θ) ^ 2 * Work.Spaces.w r
        = (c2m θ) ^ 2 * (L12 (Fstar α) r) ^ 2 * ((Dz d r θ) ^ 2 * Work.Spaces.w r) := by ring
    rw [hfac]
    have hLF2 : (L12 (Fstar α) r) ^ 2 ≤ (2 * α) ^ 2 := by
      nlinarith [hLF, abs_nonneg (L12 (Fstar α) r), sq_abs (L12 (Fstar α) r)]
    calc (c2m θ) ^ 2 * (L12 (Fstar α) r) ^ 2 * ((Dz d r θ) ^ 2 * Work.Spaces.w r)
        ≤ (4 * (2 * α) ^ 2) * ((Dz d r θ) ^ 2 * Work.Spaces.w r) :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul hc2 hLF2 (sq_nonneg _) (by norm_num)) (by positivity)
      _ ≤ (4 * (2 * α) ^ 2) * Hk α 4 d r θ :=
          mul_le_mul_of_nonneg_left hslot2w (by positivity)
      _ = 16 * α ^ 2 * Hk α 4 d r θ := by ring
  linarith [hstep, hA, hB]

/-- **The pointwise bound**: the Hardy-weighted square of the difference field is dominated by
`DiffMaj` on the open quadrant. -/
theorem diff_pointwise_le {α C₀ Xd : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) (hC₀ : 0 ≤ C₀)
    {f f' d : Fn} (hXd : Xn α d = Xd)
    (hf : Work.FTS.EllipticEst.SmoothOpen f) (hf' : Work.FTS.EllipticEst.SmoothOpen f')
    (hd : Work.FTS.EllipticEst.SmoothOpen d)
    (hmf : Work.Spaces.HkMem α 4 f) (hmf' : Work.Spaces.HkMem α 4 f')
    (hmd : Work.Spaces.HkMem α 4 d)
    (hddef : ∀ z θ, d z θ = f z θ - f' z θ) (hXf : Xn α f ≤ C₀ * α ^ 2)
    {r θ : ℝ} (hr : 0 < r) (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    (Sn0 α f r θ - Sn0 α f' r θ) ^ 2 * Work.Spaces.w r ≤ DiffMaj α C₀ Xd d f' r θ := by
  have hw0 : 0 ≤ Work.Spaces.w r := le_trans zero_le_one (one_le_w hr)
  have hexp := Sn0_sub_expand hf hf' hd hmf hmf' hmd hddef r θ hr hθ.1 hθ.2
  set D1 : ℝ := (L12 f r) * (d r θ / α + (3 / (2 * α)) * Dth d r θ - c2m θ * Dz d r θ)
    with hD1def
  set D2 : ℝ := (L12 d r) * (f' r θ / α + (3 / (2 * α)) * Dth f' r θ - c2m θ * Dz f' r θ)
    with hD2def
  set D3 : ℝ := (L12 d r) * ((3 / (2 * α)) * Dth (Fstar α) r θ - c2m θ * Dz (Fstar α) r θ)
      - c2m θ * (L12 (Fstar α) r) * Dz d r θ with hD3def
  have hD : Sn0 α f r θ - Sn0 α f' r θ = D1 + D2 + D3 := by
    rw [hD1def, hD2def, hD3def]
    linarith [hexp]
  have hsq : (D1 + D2 + D3) ^ 2 ≤ 3 * (D1 ^ 2 + D2 ^ 2 + D3 ^ 2) := by
    nlinarith [sq_nonneg (D1 - D2), sq_nonneg (D2 - D3), sq_nonneg (D3 - D1)]
  have hstep : (D1 + D2 + D3) ^ 2 * Work.Spaces.w r
      ≤ 3 * (D1 ^ 2 * Work.Spaces.w r + D2 ^ 2 * Work.Spaces.w r
          + D3 ^ 2 * Work.Spaces.w r) := by
    have h := mul_le_mul_of_nonneg_right hsq hw0
    nlinarith [h]
  have hXdnn : 0 ≤ Xd := by
    rw [← hXd]; exact Work.Spaces.HkNorm_nonneg α 4 d
  have g1 := diffGroup1_le (d := d) hα hα1 hC₀ hf hmf hXf hr hθ
  have g2 := diffGroup2_le (Xd := Xd) (f' := f') hα hα1 hXdnn hd hmd hXd hr hθ
  have g3 := diffGroup3_le (Xd := Xd) hα hα1 hXdnn hd hmd hXd hr hθ
  rw [hD, DiffMaj]
  linarith [hstep, g1, g2, g3]

end Work.FTS_MuLipC.RowN0
